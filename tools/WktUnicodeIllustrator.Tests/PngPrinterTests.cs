using SixLabors.ImageSharp;
using SixLabors.ImageSharp.PixelFormats;
using WktUnicodeIllustrator;
using Xunit;

namespace WktUnicodeIllustrator.Tests;

/// <summary>
/// The PNG printer is the second adapter at the Doc seam: same Doc in, a
/// terminal facsimile out. Assertions are at the image level (dimensions,
/// palette presence, determinism), not glyph shapes.
/// </summary>
public class PngPrinterTests
{
    private static Doc DefaultColoredDoc()
    {
        var composed = CaseIllustrator.Compose();
        Assert.NotNull(composed.Scenario);
        return Style.Build(composed.Scenario!, colored: true);
    }

    [Fact]
    public void Print_produces_a_decodable_png()
    {
        byte[] bytes = PngPrinter.Print(DefaultColoredDoc());

        Assert.True(bytes.Length > 8);
        // PNG signature.
        Assert.Equal(0x89, bytes[0]);
        Assert.Equal((byte)'P', bytes[1]);
        Assert.Equal((byte)'N', bytes[2]);
        Assert.Equal((byte)'G', bytes[3]);

        using var image = Image.Load<Rgba32>(bytes);
        Assert.True(image.Width > 100);
        Assert.True(image.Height > 100);
    }

    [Fact]
    public void Print_is_deterministic()
    {
        byte[] first = PngPrinter.Print(DefaultColoredDoc());
        byte[] second = PngPrinter.Print(DefaultColoredDoc());
        Assert.Equal(first, second);
    }

    [Fact]
    public void Facsimile_contains_A_blue_and_B_red_ink()
    {
        byte[] bytes = PngPrinter.Print(DefaultColoredDoc());
        using var image = Image.Load<Rgba32>(bytes);

        int blueish = 0, reddish = 0;
        for (int y = 0; y < image.Height; y++)
        {
            for (int x = 0; x < image.Width; x++)
            {
                var p = image[x, y];
                if (p.B > 160 && p.B > p.R + 60 && p.B > p.G + 60) blueish++;
                if (p.R > 160 && p.R > p.B + 60 && p.R > p.G + 60) reddish++;
            }
        }

        Assert.True(blueish > 20, $"expected A-blue ink, found {blueish} px");
        Assert.True(reddish > 20, $"expected B-red ink, found {reddish} px");
    }

    [Fact]
    public void Long_header_lines_wrap_instead_of_widening_the_image()
    {
        var doc = new Doc();
        doc.AddLine(new Run(new string('x', 500)));

        byte[] bytes = PngPrinter.Print(doc);
        using var image = Image.Load<Rgba32>(bytes);

        // 500 chars wrapped at 80 columns → 7 visual lines, not one 500-col line.
        byte[] oneLine = PngPrinter.Print(SingleLineDoc(80));
        using var reference = Image.Load<Rgba32>(oneLine);
        Assert.Equal(reference.Width, image.Width);
        // Same fixed margins on both, so compare the content bands: 7 lines vs 1.
        Assert.True(image.Height > reference.Height * 3,
            $"expected wrapped height, got {image.Height} vs single-line {reference.Height}");
    }

    private static Doc SingleLineDoc(int cols)
    {
        var doc = new Doc();
        doc.AddLine(new Run(new string('x', cols)));
        return doc;
    }

    public static TheoryData<string, string?, string?, string> ScenarioCases => new()
    {
        { "default-crossing", null, null, "intersection" },
        { "orthogonal-crossing", "LINESTRING (0 0, 4 0)", "LINESTRING (2 -2, 2 2)", "intersection" },
        { "polygon-union", "POLYGON ((0 0, 8 0, 8 3, 0 3, 0 0))", "POLYGON ((4 1, 12 1, 12 4, 4 4, 4 1))", "union" },
        { "point-x-line", "POINT (3 3)", "LINESTRING (0 0, 6 6)", "none" },
        { "empty-result", "LINESTRING (0 0, 1 1)", "LINESTRING (5 5, 6 6)", "intersection" },
        { "symdifference", "LINESTRING (0 0, 4 0)", "LINESTRING (2 0, 6 0)", "symdifference" },
    };

    [Theory]
    [MemberData(nameof(ScenarioCases))]
    public void Scenario_shaped_case_prints_a_decodable_deterministic_facsimile(
        string name, string? wktA, string? wktB, string operation)
    {
        var composed = CaseIllustrator.Compose(wktA: wktA, wktB: wktB, operation: operation);
        Assert.True(composed.Scenario is not null, $"case {name}: compose failed ({composed.Error})");

        var doc = Style.Build(composed.Scenario!, colored: true);
        byte[] first = PngPrinter.Print(doc);
        byte[] second = PngPrinter.Print(doc);
        Assert.Equal(first, second);

        using var image = Image.Load<Rgba32>(first);
        Assert.True(image.Width > 50 && image.Height > 50,
            $"case {name}: implausible facsimile {image.Width}×{image.Height}");
    }

    [CurveFact]
    public void Curve_demo_scenario_prints_a_deterministic_facsimile()
    {
        var composed = CaseIllustrator.Compose(
            wktA: CaseIllustrator.DefaultCurveA,
            wktB: CaseIllustrator.DefaultCurveB);
        Assert.NotNull(composed.Scenario);

        var doc = Style.Build(composed.Scenario!, colored: true);
        Assert.Equal(PngPrinter.Print(doc), PngPrinter.Print(doc));
    }

    [CurveFact]
    public void Overshoot_demo_facsimile_carries_maroon_and_navy_ink()
    {
        var composed = CaseIllustrator.Compose(
            wktA: CaseIllustrator.DefaultOvershootA,
            wktB: CaseIllustrator.DefaultOvershootB);
        Assert.NotNull(composed.Scenario);

        var doc = Style.Build(composed.Scenario!, colored: true);
        using var image = Image.Load<Rgba32>(PngPrinter.Print(doc));

        // Maroon #800000 and navy #000080 are exact truecolor inks; glyph
        // interiors carry them unblended, so look for near-exact pixels.
        int maroon = 0, navy = 0;
        for (int y = 0; y < image.Height; y++)
        {
            for (int x = 0; x < image.Width; x++)
            {
                var p = image[x, y];
                if (p.R is > 100 and < 150 && p.G < 40 && p.B < 40) maroon++;
                if (p.B is > 100 and < 150 && p.R < 40 && p.G < 40) navy++;
            }
        }

        Assert.True(maroon > 10, $"expected maroon overshoot ink, found {maroon} px");
        Assert.True(navy > 10, $"expected navy overshoot ink, found {navy} px");
    }
}

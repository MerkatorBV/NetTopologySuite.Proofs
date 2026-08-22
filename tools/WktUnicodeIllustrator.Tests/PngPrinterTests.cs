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
}

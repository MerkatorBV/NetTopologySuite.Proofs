using NetTopologySuite.Geometries;
using WktUnicodeIllustrator;
using Xunit;

namespace WktUnicodeIllustrator.Tests;

/// <summary>
/// Surface-interior fills: ░ for one geometry's interior, ╳ where both
/// overlap, strokes drawn on top. Asserted at the Scenario seam (fill layers
/// per cell) and on the printed text.
/// </summary>
public class SurfaceFillTests
{
    private const string RectA = "POLYGON ((0 0, 8 0, 8 3, 0 3, 0 0))";
    private const string RectB = "POLYGON ((4 1, 12 1, 12 4, 4 4, 4 1))";

    [Fact]
    public void Overlapping_rectangles_fill_their_interiors_and_overlap()
    {
        var composed = CaseIllustrator.Compose(wktA: RectA, wktB: RectB, operation: "none");
        var s = composed.Scenario!;

        Layer At(double x, double y)
        {
            var (c, r) = s.Map.Project(new Coordinate(x, y));
            return s.Canvas[c, r];
        }

        Layer aOnly = At(2, 1.5);
        Assert.True(aOnly.HasFlag(Layer.FillA));
        Assert.False(aOnly.HasFlag(Layer.FillB));

        Layer bOnly = At(10, 2.5);
        Assert.True(bOnly.HasFlag(Layer.FillB));
        Assert.False(bOnly.HasFlag(Layer.FillA));

        Layer both = At(6, 2);
        Assert.True(both.HasFlag(Layer.FillA));
        Assert.True(both.HasFlag(Layer.FillB));
    }

    [Fact]
    public void Filled_render_shows_shade_and_overlap_glyphs()
    {
        var r = CaseIllustrator.Render(wktA: RectA, wktB: RectB, operation: "none", useColor: false);
        Assert.Equal(0, r.ExitCode);
        Assert.Contains('░', r.Text);
        Assert.Contains('╳', r.Text);
    }

    [Fact]
    public void No_fill_disables_the_shading()
    {
        var r = CaseIllustrator.Render(
            wktA: RectA, wktB: RectB, operation: "none", useColor: false, showFill: false);
        Assert.Equal(0, r.ExitCode);
        Assert.DoesNotContain('░', r.Text);
    }

    [Fact]
    public void Lineal_inputs_produce_no_fills()
    {
        var composed = CaseIllustrator.Compose();
        var canvas = composed.Scenario!.Canvas;
        for (int y = 0; y < canvas.Height; y++)
            for (int x = 0; x < canvas.Width; x++)
                Assert.Equal(Layer.None, canvas[x, y] & (Layer.FillA | Layer.FillB));
    }

    [CurveFact]
    public void Venn_demo_fills_discs_and_lens()
    {
        var r = CaseIllustrator.Render(
            wktA: CaseIllustrator.DefaultVennA,
            wktB: CaseIllustrator.DefaultVennB,
            operation: "none",
            useColor: false);

        Assert.Equal(0, r.ExitCode);
        Assert.Contains('░', r.Text);
        Assert.Contains('╳', r.Text);
    }
}

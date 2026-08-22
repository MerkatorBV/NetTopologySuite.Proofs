using WktUnicodeIllustrator;
using Xunit;

namespace WktUnicodeIllustrator.Tests;

/// <summary>
/// Regression pins for the semicircle-and-point report: isolated points are ●,
/// an arc apex is a ─ run (not a stray ╳), and curves densify to true arcs
/// instead of the clone's chord Linearize() (which drew a diamond).
/// </summary>
public class ArcRenderingTests
{
    [Fact]
    public void Isolated_mask_is_a_point_mark()
    {
        Assert.Equal('●', StructureGlyph.ChooseFromMask(0));
    }

    [Fact]
    public void Same_side_diagonal_pairs_are_stroke_extrema_not_crossings()
    {
        // Diagonal bits: NE=16, SE=32, SW=64, NW=128 (screen Y grows down).
        Assert.Equal('─', StructureGlyph.ChooseFromMask(64 | 32));   // SW|SE — apex
        Assert.Equal('─', StructureGlyph.ChooseFromMask(128 | 16));  // NW|NE — valley
        Assert.Equal('│', StructureGlyph.ChooseFromMask(16 | 32));   // NE|SE — right bulge
        Assert.Equal('│', StructureGlyph.ChooseFromMask(128 | 64));  // NW|SW — left bulge
        // Opposite pairs stay through-going strokes; 3+ is a real crossing.
        Assert.Equal('╱', StructureGlyph.ChooseFromMask(16 | 64));
        Assert.Equal('╲', StructureGlyph.ChooseFromMask(128 | 32));
        Assert.Equal('╳', StructureGlyph.ChooseFromMask(16 | 32 | 64));
    }

    [CurveFact]
    public void CircularString_densifies_to_a_true_arc_not_control_chords()
    {
        var arc = GeometryCurves.Parse("CIRCULARSTRING (-1 0, 0 1, 1 0)");
        var lin = GeometryCurves.Linearize(arc);

        // The clone's chord Linearize() returns the 3 control points; a true
        // arc densification has many vertices, all on the unit circle.
        Assert.True(lin.NumPoints > 10, $"chord fallback? {lin.NumPoints} points");
        foreach (var c in lin.Coordinates)
        {
            double r = Math.Sqrt(c.X * c.X + c.Y * c.Y);
            Assert.InRange(r, 0.999, 1.001);
        }
    }

    [CurveFact]
    public void Semicircle_and_point_render_as_dome_and_point_mark()
    {
        var r = CaseIllustrator.Render(
            wktA: "CIRCULARSTRING (-1 0, 0 1, 1 0)",
            wktB: "POINT (0 2)",
            operation: "none",
            useColor: false);

        Assert.Equal(0, r.ExitCode);
        // The point is a point mark, the apex a contiguous flat run, and
        // nothing crosses anything — no ╳ anywhere.
        Assert.Contains('●', r.Text);
        Assert.Contains("─────", r.Text.Substring(r.Text.IndexOf("— inputs")));
        Assert.DoesNotContain('╳', r.Text);
    }
}

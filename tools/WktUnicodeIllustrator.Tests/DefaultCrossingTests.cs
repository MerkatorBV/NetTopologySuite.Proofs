using WktUnicodeIllustrator;
using Xunit;

namespace WktUnicodeIllustrator.Tests;

/// <summary>
/// Drives the shipped <see cref="CaseIllustrator"/> path — the same builder
/// the CLI uses — for the MVP line–line crossing. Assertions check structural
/// properties of the real output (not a hard-coded full grid).
/// </summary>
public class DefaultCrossingTests
{
    [Fact]
    public void Default_crossing_exits_0_and_frames_both_arms_with_result_point()
    {
        var r = CaseIllustrator.Render(useColor: false);

        Assert.Equal(0, r.ExitCode);
        Assert.False(string.IsNullOrWhiteSpace(r.Text));
        Assert.Contains(CaseIllustrator.DefaultA, r.Text);
        Assert.Contains(CaseIllustrator.DefaultB, r.Text);
        Assert.Contains("POINT (5 5)", r.Text);
        Assert.Contains("— inputs", r.Text);
        Assert.Contains("— after operation", r.Text);
        Assert.Contains('┌', r.Text);
        Assert.Contains('└', r.Text);

        // Both diagonal glyphs appear (X arms).
        Assert.Contains('╱', r.Text);
        Assert.Contains('╲', r.Text);

        // Inputs mark coincidence; after-op promotes the green result cell to ●.
        Assert.Contains('╳', r.Text);
        Assert.Contains('●', r.Text);

        Assert.False(r.ResultIsEmpty);
        Assert.Equal("POINT (5 5)", r.ResultWkt);
    }

    [Fact]
    public void Horizontal_vertical_crossing_is_orthogonal_with_point_result()
    {
        var r = CaseIllustrator.Render(
            wktA: "LINESTRING (0 0, 4 0)",
            wktB: "LINESTRING (2 -2, 2 2)",
            useColor: false);

        Assert.Equal(0, r.ExitCode);
        Assert.Contains("POINT (2 0)", r.Text);
        Assert.Contains('─', r.Text);
        Assert.Contains('│', r.Text);
        Assert.Contains('●', r.Text);
        Assert.Equal("POINT (2 0)", r.ResultWkt);
    }

    [Fact]
    public void Color_mode_emits_blue_red_and_green_SGR_sequences()
    {
        var r = CaseIllustrator.Render(useColor: true);

        Assert.Equal(0, r.ExitCode);
        // Shipped SGR constants from AnsiRenderer (bright blue / red / green).
        Assert.Contains("\x1b[94m", r.Text); // A blue
        Assert.Contains("\x1b[91m", r.Text); // B red
        Assert.Contains("\x1b[92m", r.Text); // result green
        Assert.Contains("\x1b[0m", r.Text);  // reset
    }

    [Fact]
    public void Two_default_renders_are_structurally_stable()
    {
        var a = CaseIllustrator.Render(useColor: false).Text;
        var b = CaseIllustrator.Render(useColor: false).Text;
        Assert.Equal(Normalize(a), Normalize(b));
    }

    [Fact]
    public void CircularString_pair_parses_via_local_NTS_and_draws_curved_strokes()
    {
        var r = CaseIllustrator.Render(
            wktA: CaseIllustrator.DefaultCurveA,
            wktB: CaseIllustrator.DefaultCurveB,
            useColor: false);

        Assert.Equal(0, r.ExitCode);
        Assert.Null(r.Error);
        Assert.Contains("CIRCULARSTRING", r.Text);
        Assert.Contains("CircularString", r.Text);
        Assert.Contains("linearized curves", r.Text);
        Assert.Contains("— inputs", r.Text);
        Assert.Contains("— after operation", r.Text);
        Assert.Contains('┌', r.Text);
        // Densified arcs should paint more than a 3-point chord triangle.
        int stroke = r.Text.Count(ch => ch is '─' or '│' or '╱' or '╲' or '╳' or '●');
        Assert.True(stroke >= 20, $"expected dense arc strokes, got {stroke}");
        Assert.False(r.ResultIsEmpty);
        Assert.False(string.IsNullOrWhiteSpace(r.ResultWkt));
    }

    [Fact]
    public void CircularString_crosses_horizontal_line()
    {
        // Chord of the densified upper arc is crossed by y = 5 (same mid-height as --demo curve).
        var r = CaseIllustrator.Render(
            wktA: "CIRCULARSTRING (0 0, 5 8, 10 0)",
            wktB: "LINESTRING (0 5, 10 5)",
            useColor: false);

        Assert.Equal(0, r.ExitCode);
        Assert.Contains("CIRCULARSTRING", r.Text);
        Assert.Contains("LINESTRING", r.Text);
        Assert.False(r.ResultIsEmpty);
        Assert.Contains('●', r.Text);
    }

    private static string Normalize(string s) =>
        string.Join('\n', s.Replace("\r\n", "\n").Split('\n').Select(l => l.TrimEnd()));
}

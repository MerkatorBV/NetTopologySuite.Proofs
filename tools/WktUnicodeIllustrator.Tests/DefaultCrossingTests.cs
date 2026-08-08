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
        // Structure pass + densified arcs: box-drawing and/or diagonals, not sparse chords.
        int stroke = r.Text.Count(ch =>
            ch is '─' or '│' or '╱' or '╲' or '╳' or '●'
                or '┌' or '┐' or '└' or '┘' or '├' or '┤' or '┬' or '┴' or '┼'
                or '╭' or '╮' or '╰' or '╯');
        Assert.True(stroke >= 20, $"expected dense structure strokes, got {stroke}");
        Assert.False(r.ResultIsEmpty);
        Assert.False(string.IsNullOrWhiteSpace(r.ResultWkt));
    }

    [Fact]
    public void Structure_glyphs_use_box_drawing_on_axis_aligned_cross()
    {
        var r = CaseIllustrator.Render(
            wktA: "LINESTRING (0 0, 4 0)",
            wktB: "LINESTRING (2 -2, 2 2)",
            useColor: false);

        Assert.Equal(0, r.ExitCode);
        // Horizontal + vertical arms after structure assignment.
        Assert.Contains('─', r.Text);
        Assert.Contains('│', r.Text);
        // Crossing / result marks.
        Assert.True(r.Text.Contains('╳') || r.Text.Contains('┼') || r.Text.Contains('●'));
    }

    [Fact]
    public void CircularString_self_retrace_reports_overshoot_layers()
    {
        var r = CaseIllustrator.Render(
            wktA: CaseIllustrator.DefaultOvershootA,
            wktB: CaseIllustrator.DefaultOvershootB,
            useColor: false,
            showOvershoot: true);

        Assert.Equal(0, r.ExitCode);
        Assert.Contains("CIRCULARSTRING", r.Text);
        Assert.NotNull(r.OvershootAWkt);
        Assert.NotNull(r.OvershootBWkt);
        Assert.Contains("A-overshoot (maroon)", r.Text);
        Assert.Contains("B-overshoot (navy)", r.Text);
        // Overshoot geometry should be non-empty self-overlap of the retrace arcs.
        Assert.DoesNotContain("A-overshoot (maroon): (none)", r.Text);
        Assert.DoesNotContain("B-overshoot (navy): (none)", r.Text);
    }

    [Fact]
    public void Simple_line_has_no_overshoot()
    {
        var r = CaseIllustrator.Render(
            wktA: CaseIllustrator.DefaultA,
            wktB: CaseIllustrator.DefaultB,
            useColor: false,
            showOvershoot: true);

        Assert.Equal(0, r.ExitCode);
        Assert.Null(r.OvershootAWkt);
        Assert.Null(r.OvershootBWkt);
        Assert.Contains("A-overshoot (maroon): (none)", r.Text);
    }

    [Fact]
    public void Color_mode_includes_maroon_and_navy_when_overshoot_present()
    {
        var r = CaseIllustrator.Render(
            wktA: CaseIllustrator.DefaultOvershootA,
            wktB: CaseIllustrator.DefaultOvershootB,
            useColor: true,
            showOvershoot: true);

        Assert.Equal(0, r.ExitCode);
        // True-color SGR for maroon / navy (see AnsiRenderer).
        Assert.Contains("\x1b[38;2;128;0;0m", r.Text); // maroon A-overshoot
        Assert.Contains("\x1b[38;2;0;0;128m", r.Text);   // navy B-overshoot
    }

    [Fact]
    public void StructureGlyph_corner_masks_map_to_box_corners()
    {
        // Pure unit tests of the structure → character table (no geometry).
        Assert.Equal('└', StructureGlyph.ChooseFromMask(1 | 2));      // N|E
        Assert.Equal('┘', StructureGlyph.ChooseFromMask(1 | 8));      // N|W
        Assert.Equal('┌', StructureGlyph.ChooseFromMask(4 | 2));      // S|E
        Assert.Equal('┐', StructureGlyph.ChooseFromMask(4 | 8));      // S|W
        Assert.Equal('─', StructureGlyph.ChooseFromMask(2 | 8));      // E|W
        Assert.Equal('│', StructureGlyph.ChooseFromMask(1 | 4));      // N|S
        Assert.Equal('┼', StructureGlyph.ChooseFromMask(1 | 2 | 4 | 8));
        Assert.Equal('╲', StructureGlyph.ChooseFromMask(128 | 32));   // NW|SE → ╲
        Assert.Equal('╱', StructureGlyph.ChooseFromMask(16 | 64));    // NE|SW → ╱
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

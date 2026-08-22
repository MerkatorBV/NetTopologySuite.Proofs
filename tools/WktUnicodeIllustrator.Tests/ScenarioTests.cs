using WktUnicodeIllustrator;
using Xunit;

namespace WktUnicodeIllustrator.Tests;

/// <summary>
/// Assertions at the Compose→Scenario seam: layer occupancy on the grid,
/// not substrings of the printed text.
/// </summary>
public class ScenarioTests
{
    [Fact]
    public void Default_crossing_marks_center_cell_with_A_B_and_result()
    {
        var composed = CaseIllustrator.Compose();

        Assert.NotNull(composed.Scenario);
        var s = composed.Scenario!;
        var canvas = s.Canvas;

        var (cx, cy) = s.Map.Project(new NetTopologySuite.Geometries.Coordinate(5, 5));
        Layer center = canvas[cx, cy];
        Assert.True(center.HasFlag(Layer.A));
        Assert.True(center.HasFlag(Layer.B));
        Assert.True(center.HasFlag(Layer.Result));
    }

    [Fact]
    public void Default_crossing_paints_no_overshoot_layers()
    {
        var composed = CaseIllustrator.Compose();
        var canvas = composed.Scenario!.Canvas;

        int overshootCells = 0;
        for (int y = 0; y < canvas.Height; y++)
            for (int x = 0; x < canvas.Width; x++)
                if (canvas[x, y].HasFlag(Layer.OvershootA) || canvas[x, y].HasFlag(Layer.OvershootB))
                    overshootCells++;

        Assert.Equal(0, overshootCells);
    }

    [Fact]
    public void Point_result_occupies_exactly_one_cell()
    {
        var composed = CaseIllustrator.Compose(
            wktA: "LINESTRING (0 0, 4 0)",
            wktB: "LINESTRING (2 -2, 2 2)");
        var canvas = composed.Scenario!.Canvas;

        int resultCells = 0;
        for (int y = 0; y < canvas.Height; y++)
            for (int x = 0; x < canvas.Width; x++)
                if (canvas[x, y].HasFlag(Layer.Result))
                    resultCells++;

        Assert.Equal(1, resultCells);
    }

    [Fact]
    public void Op_none_skips_result_and_scenario_records_it()
    {
        var composed = CaseIllustrator.Compose(operation: "none");
        var s = composed.Scenario!;

        Assert.Null(s.Result);
        var canvas = s.Canvas;
        for (int y = 0; y < canvas.Height; y++)
            for (int x = 0; x < canvas.Width; x++)
                Assert.False(canvas[x, y].HasFlag(Layer.Result));
    }

    [Fact]
    public void Parse_failure_is_a_compose_failure_with_exit_2()
    {
        var composed = CaseIllustrator.Compose(wktA: "NOT WKT AT ALL");

        Assert.Null(composed.Scenario);
        Assert.Equal(2, composed.ExitCode);
        Assert.NotNull(composed.Error);
    }

    [CurveFact]
    public void Overshoot_demo_scenario_carries_both_overshoot_extracts()
    {
        var composed = CaseIllustrator.Compose(
            wktA: CaseIllustrator.DefaultOvershootA,
            wktB: CaseIllustrator.DefaultOvershootB);
        var s = composed.Scenario!;

        Assert.True(s.OvershootA is { IsEmpty: false });
        Assert.True(s.OvershootB is { IsEmpty: false });
    }
}

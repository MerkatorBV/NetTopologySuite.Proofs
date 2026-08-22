using NetTopologySuite.Geometries;
using WktUnicodeIllustrator;
using Xunit;

namespace WktUnicodeIllustrator.Tests;

/// <summary>
/// Direct tests for the world→grid fit, including the cell-aspect correction
/// (aafb92b): a square world must span ~cellAspect× more columns than rows so
/// it reads square on ~1:2 terminal cells.
/// </summary>
public class WorldToGridTests
{
    [Fact]
    public void Square_world_spans_cellAspect_times_more_columns_than_rows()
    {
        var env = new Envelope(0, 10, 0, 10);
        var map = new WorldToGrid(env, width: 41, height: 21, cellAspect: 2.0);

        var (c0, r0) = map.Project(new Coordinate(0, 0));
        var (c1, r1) = map.Project(new Coordinate(10, 10));

        int colSpan = Math.Abs(c1 - c0);
        int rowSpan = Math.Abs(r1 - r0);
        double ratio = (double)colSpan / rowSpan;
        Assert.InRange(ratio, 1.7, 2.3);
    }

    [Fact]
    public void Square_cells_preserve_world_aspect_in_cell_space()
    {
        var env = new Envelope(0, 10, 0, 10);
        var map = new WorldToGrid(env, width: 41, height: 21, cellAspect: 1.0);

        var (c0, r0) = map.Project(new Coordinate(0, 0));
        var (c1, r1) = map.Project(new Coordinate(10, 10));

        Assert.Equal(Math.Abs(r1 - r0), Math.Abs(c1 - c0));
    }

    [Fact]
    public void Y_axis_is_flipped_to_screen_rows()
    {
        var env = new Envelope(0, 10, 0, 10);
        var map = new WorldToGrid(env, width: 41, height: 21);

        var (_, rowBottom) = map.Project(new Coordinate(5, 0));
        var (_, rowTop) = map.Project(new Coordinate(5, 10));
        Assert.True(rowTop < rowBottom);
    }

    [Fact]
    public void Projection_clamps_to_grid_bounds()
    {
        var env = new Envelope(0, 10, 0, 10);
        var map = new WorldToGrid(env, width: 41, height: 21);

        var (col, row) = map.Project(new Coordinate(1000, -1000));
        Assert.InRange(col, 0, 40);
        Assert.InRange(row, 0, 20);
    }
}

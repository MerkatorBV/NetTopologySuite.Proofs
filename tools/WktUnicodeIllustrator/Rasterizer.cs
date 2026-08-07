using NetTopologySuite.Geometries;

namespace WktUnicodeIllustrator;

/// <summary>
/// Rasterizes NTS linework onto a <see cref="Canvas"/> with Unicode direction glyphs.
/// MVP scope: <see cref="LineString"/> / <see cref="MultiLineString"/> only.
/// </summary>
internal static class Rasterizer
{
    public static void DrawGeometry(Canvas canvas, WorldToGrid map, Geometry g, Layer layer)
    {
        switch (g)
        {
            case LineString ls:
                DrawLineString(canvas, map, ls, layer);
                break;
            case MultiLineString mls:
                for (int i = 0; i < mls.NumGeometries; i++)
                    DrawLineString(canvas, map, (LineString)mls.GetGeometryN(i), layer);
                break;
            case Point p:
                var (c, r) = map.Project(p.Coordinate);
                canvas.Paint(c, r, layer, '●');
                break;
            case GeometryCollection gc:
                for (int i = 0; i < gc.NumGeometries; i++)
                    DrawGeometry(canvas, map, gc.GetGeometryN(i), layer);
                break;
            default:
                // MVP fallback: stroke the exterior ring / edges if present.
                if (g.Boundary is { IsEmpty: false } b)
                    DrawGeometry(canvas, map, b, layer);
                break;
        }
    }

    public static void DrawLineString(Canvas canvas, WorldToGrid map, LineString ls, Layer layer)
    {
        var coords = ls.Coordinates;
        if (coords.Length == 0) return;
        if (coords.Length == 1)
        {
            var (c, r) = map.Project(coords[0]);
            canvas.Paint(c, r, layer, '●');
            return;
        }

        for (int i = 0; i < coords.Length - 1; i++)
        {
            var a = map.Project(coords[i]);
            var b = map.Project(coords[i + 1]);
            DrawSegment(canvas, a.Col, a.Row, b.Col, b.Row, layer);
        }
    }

    /// <summary>Bresenham line with slope-aware Unicode glyphs.</summary>
    public static void DrawSegment(Canvas canvas, int x0, int y0, int x1, int y1, Layer layer)
    {
        char glyph = DirectionGlyph(x0, y0, x1, y1);
        int dx = Math.Abs(x1 - x0);
        int dy = Math.Abs(y1 - y0);
        int sx = x0 < x1 ? 1 : -1;
        int sy = y0 < y1 ? 1 : -1;
        int err = dx - dy;
        int x = x0, y = y0;

        while (true)
        {
            canvas.Paint(x, y, layer, glyph);
            if (x == x1 && y == y1) break;
            int e2 = 2 * err;
            if (e2 > -dy) { err -= dy; x += sx; }
            if (e2 < dx) { err += dx; y += sy; }
        }
    }

    public static char DirectionGlyph(int x0, int y0, int x1, int y1)
    {
        int dx = x1 - x0;
        int dy = y1 - y0; // grid: +dy is downward
        if (dx == 0 && dy == 0) return '●';
        if (dx == 0) return '│';
        if (dy == 0) return '─';

        // Screen Y grows down, so geometric / (NE-SW) is screen ╲ and \ (NW-SE) is ╱.
        double slope = (double)dy / dx; // dy/dx in grid space
        if (Math.Abs(slope) < 0.4) return '─';
        if (Math.Abs(slope) > 2.5) return '│';
        // Same sign: moving right+down or left+up → ╲
        return Math.Sign(dx) == Math.Sign(dy) ? '╲' : '╱';
    }
}

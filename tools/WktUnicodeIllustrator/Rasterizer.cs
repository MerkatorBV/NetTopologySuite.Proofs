using NetTopologySuite.Geometries;

namespace WktUnicodeIllustrator;

/// <summary>
/// Rasterizes NTS linework onto a <see cref="Canvas"/> as layer occupancy.
/// Callers should <see cref="GeometryCurves.Linearize"/> curves first so arcs become dense polylines.
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
            case Polygon poly:
                DrawLineString(canvas, map, poly.ExteriorRing, layer);
                for (int i = 0; i < poly.NumInteriorRings; i++)
                    DrawLineString(canvas, map, poly.GetInteriorRingN(i), layer);
                break;
            case Point p:
                var (c, r) = map.Project(p.Coordinate);
                canvas.Paint(c, r, layer);
                break;
            case GeometryCollection gc:
                for (int i = 0; i < gc.NumGeometries; i++)
                    DrawGeometry(canvas, map, gc.GetGeometryN(i), layer);
                break;
            default:
                // Stroke boundary / edges when present (MultiPolygon, etc.).
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
            canvas.Paint(c, r, layer);
            return;
        }

        for (int i = 0; i < coords.Length - 1; i++)
        {
            var a = map.Project(coords[i]);
            var b = map.Project(coords[i + 1]);
            DrawSegment(canvas, a.Col, a.Row, b.Col, b.Row, layer);
        }
    }

    /// <summary>Bresenham line over layer occupancy.</summary>
    public static void DrawSegment(Canvas canvas, int x0, int y0, int x1, int y1, Layer layer)
    {
        int dx = Math.Abs(x1 - x0);
        int dy = Math.Abs(y1 - y0);
        int sx = x0 < x1 ? 1 : -1;
        int sy = y0 < y1 ? 1 : -1;
        int err = dx - dy;
        int x = x0, y = y0;

        while (true)
        {
            canvas.Paint(x, y, layer);
            if (x == x1 && y == y1) break;
            int e2 = 2 * err;
            if (e2 > -dy) { err -= dy; x += sx; }
            if (e2 < dx) { err += dx; y += sy; }
        }
    }
}

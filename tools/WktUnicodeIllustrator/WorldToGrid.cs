using NetTopologySuite.Geometries;

namespace WktUnicodeIllustrator;

/// <summary>
/// Maps world (X right, Y up) into grid (col right, row down) with a small margin.
/// </summary>
internal sealed class WorldToGrid
{
    /// <summary>Terminal character height ÷ width; ~2 for typical monospace fonts.</summary>
    public const double DefaultCellAspect = 2.0;

    private readonly double _minX, _minY, _maxX, _maxY;
    private readonly int _width, _height;
    private readonly double _pad;

    public WorldToGrid(Envelope env, int width, int height, double padFraction = 0.08,
        double cellAspect = DefaultCellAspect)
    {
        _width = width;
        _height = height;
        double dx = Math.Max(env.Width, 1e-9);
        double dy = Math.Max(env.Height, 1e-9);
        // Keep *visual* aspect: a grid cell is cellAspect× taller than wide on
        // screen, so the frame's visual aspect is (w-1) / ((h-1)·cellAspect).
        // Expand the thinner world axis so shapes are not stretched.
        double worldAspect = dx / dy;
        double gridAspect = (double)(width - 1)
            / (Math.Max(1, height - 1) * Math.Max(0.1, cellAspect));
        if (worldAspect > gridAspect)
            dy = dx / gridAspect;
        else
            dx = dy * gridAspect;

        double cx = (env.MinX + env.MaxX) / 2.0;
        double cy = (env.MinY + env.MaxY) / 2.0;
        _pad = padFraction;
        double hx = dx * (0.5 + _pad);
        double hy = dy * (0.5 + _pad);
        _minX = cx - hx;
        _maxX = cx + hx;
        _minY = cy - hy;
        _maxY = cy + hy;
    }

    public (int Col, int Row) Project(Coordinate c)
    {
        double u = (c.X - _minX) / (_maxX - _minX);
        double v = (c.Y - _minY) / (_maxY - _minY); // 0 = bottom
        int col = (int)Math.Round(u * (_width - 1));
        int row = (int)Math.Round((1.0 - v) * (_height - 1)); // flip Y
        col = Math.Clamp(col, 0, _width - 1);
        row = Math.Clamp(row, 0, _height - 1);
        return (col, row);
    }
}

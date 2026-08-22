namespace WktUnicodeIllustrator;

/// <summary>
/// Occupancy grid: each cell records which layers paint it. Glyph and colour
/// choices belong to the <see cref="Style"/> step, not the canvas.
/// </summary>
internal sealed class Canvas
{
    public int Width { get; }
    public int Height { get; }

    private readonly Layer[,] _cells;

    public Canvas(int width, int height)
    {
        if (width < 4 || height < 4)
            throw new ArgumentOutOfRangeException(nameof(width), "Grid must be at least 4×4.");
        Width = width;
        Height = height;
        _cells = new Layer[height, width];
    }

    public Layer this[int x, int y] => _cells[y, x];

    public void Paint(int x, int y, Layer layer)
    {
        if ((uint)x >= (uint)Width || (uint)y >= (uint)Height) return;
        _cells[y, x] |= layer;
    }
}

[Flags]
internal enum Layer
{
    None = 0,
    A = 1,
    B = 2,
    Result = 4,
    /// <summary>Self-overlap / overshoot on geometry A (maroon).</summary>
    OvershootA = 8,
    /// <summary>Self-overlap / overshoot on geometry B (navy).</summary>
    OvershootB = 16,
    /// <summary>Interior of a surface in A (░ fill; ╳ where it meets FillB).</summary>
    FillA = 32,
    /// <summary>Interior of a surface in B.</summary>
    FillB = 64,
}

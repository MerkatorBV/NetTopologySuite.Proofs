namespace WktUnicodeIllustrator;

/// <summary>
/// Character-grid canvas. Each cell tracks which layers paint it and a preferred
/// glyph (line-direction glyph or intersection mark).
/// </summary>
internal sealed class Canvas
{
    public int Width { get; }
    public int Height { get; }

    private readonly Cell[,] _cells;

    public Canvas(int width, int height)
    {
        if (width < 4 || height < 4)
            throw new ArgumentOutOfRangeException(nameof(width), "Grid must be at least 4×4.");
        Width = width;
        Height = height;
        _cells = new Cell[height, width];
        for (int y = 0; y < height; y++)
            for (int x = 0; x < width; x++)
                _cells[y, x] = new Cell();
    }

    public Cell this[int x, int y] => _cells[y, x];

    public void Paint(int x, int y, Layer layer, char glyph)
    {
        if ((uint)x >= (uint)Width || (uint)y >= (uint)Height) return;
        var c = _cells[y, x];
        c.Layers |= layer;
        switch (layer)
        {
            case Layer.A:
                if (c.GlyphA is '\0' or ' ') c.GlyphA = glyph;
                break;
            case Layer.B:
                if (c.GlyphB is '\0' or ' ') c.GlyphB = glyph;
                break;
            case Layer.Result:
                c.GlyphResult = glyph is '\0' or ' ' ? '●' : glyph;
                break;
        }
        // Composite display glyph: result wins, else first input stroke.
        if (c.GlyphResult is not ('\0' or ' '))
            c.Glyph = c.GlyphResult;
        else if (c.GlyphA is not ('\0' or ' '))
            c.Glyph = c.GlyphA;
        else
            c.Glyph = c.GlyphB;
    }

    public IEnumerable<(int X, int Y, Cell Cell)> Enumerate()
    {
        for (int y = 0; y < Height; y++)
            for (int x = 0; x < Width; x++)
                yield return (x, y, _cells[y, x]);
    }
}

[Flags]
internal enum Layer
{
    None = 0,
    A = 1,
    B = 2,
    Result = 4,
}

internal sealed class Cell
{
    public Layer Layers;
    /// <summary>Last / preferred display glyph (may be result-overwritten).</summary>
    public char Glyph;
    public char GlyphA;
    public char GlyphB;
    public char GlyphResult;
}

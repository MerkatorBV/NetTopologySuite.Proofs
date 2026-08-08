namespace WktUnicodeIllustrator;

/// <summary>
/// Structure-based glyph assignment (lightweight cousin of Xu–Zhang–Wong structure ASCII art).
/// After occupancy is painted, each stroked cell is matched to a Unicode box/diagonal
/// character from its local 8-neighbourhood — not from Bresenham slope alone.
/// </summary>
internal static class StructureGlyph
{
    // Cardinal bits (screen Y grows downward).
    private const int N = 1;
    private const int E = 2;
    private const int S = 4;
    private const int W = 8;
    // Diagonals
    private const int NE = 16;
    private const int SE = 32;
    private const int SW = 64;
    private const int NW = 128;

    /// <summary>
    /// Overwrite per-layer glyphs from connectivity structure.
    /// Result points (no neighbours) stay ● so the op mark stays distinct.
    /// </summary>
    public static void Assign(Canvas canvas)
    {
        for (int y = 0; y < canvas.Height; y++)
        {
            for (int x = 0; x < canvas.Width; x++)
            {
                var cell = canvas[x, y];
                if (cell.Layers.HasFlag(Layer.A))
                    cell.GlyphA = Choose(canvas, x, y, Layer.A);
                if (cell.Layers.HasFlag(Layer.B))
                    cell.GlyphB = Choose(canvas, x, y, Layer.B);
                if (cell.Layers.HasFlag(Layer.Result))
                    cell.GlyphResult = ChooseResult(canvas, x, y);
            }
        }
    }

    private static char ChooseResult(Canvas canvas, int x, int y)
    {
        int mask = NeighbourMask(canvas, x, y, Layer.Result);
        int ortho = mask & 0xF;
        // Isolated / degree-0 → point mark (intersection points, multipoints).
        if (ortho == 0 && (mask & 0xF0) == 0)
            return '●';
        return ChooseFromMask(mask);
    }

    private static char Choose(Canvas canvas, int x, int y, Layer layer)
    {
        int mask = NeighbourMask(canvas, x, y, layer);
        return ChooseFromMask(mask);
    }

    private static int NeighbourMask(Canvas canvas, int x, int y, Layer layer)
    {
        int m = 0;
        if (Has(canvas, x, y - 1, layer)) m |= N;
        if (Has(canvas, x + 1, y, layer)) m |= E;
        if (Has(canvas, x, y + 1, layer)) m |= S;
        if (Has(canvas, x - 1, y, layer)) m |= W;
        if (Has(canvas, x + 1, y - 1, layer)) m |= NE;
        if (Has(canvas, x + 1, y + 1, layer)) m |= SE;
        if (Has(canvas, x - 1, y + 1, layer)) m |= SW;
        if (Has(canvas, x - 1, y - 1, layer)) m |= NW;
        return m;
    }

    private static bool Has(Canvas canvas, int x, int y, Layer layer)
    {
        if ((uint)x >= (uint)canvas.Width || (uint)y >= (uint)canvas.Height) return false;
        return canvas[x, y].Layers.HasFlag(layer);
    }

    /// <summary>
    /// Map local structure → glyph. Orthogonal junctions win; pure diagonals next;
    /// mixed soft corners use rounded box-drawing when helpful for arcs.
    /// </summary>
    internal static char ChooseFromMask(int mask)
    {
        int ortho = mask & 0xF;
        int diag = mask & 0xF0;
        int oCount = Pop4(ortho);
        int dCount = Pop4(diag >> 4);

        // Pure diagonal strokes (curve chords often land here).
        // Screen Y grows downward. Unicode:
        //   ╱ = upper-right ↔ lower-left  → NE–SW neighbours
        //   ╲ = upper-left  ↔ lower-right → NW–SE neighbours
        if (oCount == 0 && dCount > 0)
        {
            bool nesw = (diag & (NE | SW)) != 0;
            bool nwse = (diag & (NW | SE)) != 0;
            if (nesw && !nwse) return '╱';
            if (nwse && !nesw) return '╲';
            if (nesw && nwse) return '╳';
            return '·';
        }

        // Orthogonal box-drawing (structure junctions).
        if (oCount > 0)
        {
            char box = OrthoGlyph(ortho);
            // Soften simple L-corners when a diagonal also continues the arc.
            if (oCount == 2 && dCount > 0)
                return SoftCorner(ortho, diag) ?? box;
            return box;
        }

        return '·';
    }

    private static char OrthoGlyph(int ortho) => ortho switch
    {
        0 => '·',
        N or S or (N | S) => '│',
        E or W or (E | W) => '─',
        N | E => '└',
        N | W => '┘',
        S | E => '┌',
        S | W => '┐',
        N | E | W => '┴',
        S | E | W => '┬',
        N | S | E => '├',
        N | S | W => '┤',
        N | S | E | W => '┼',
        // 3-way already covered; leftover single-ish
        _ => oCountFallback(ortho),
    };

    private static char oCountFallback(int ortho)
    {
        if ((ortho & (N | S)) != 0 && (ortho & (E | W)) == 0) return '│';
        if ((ortho & (E | W)) != 0 && (ortho & (N | S)) == 0) return '─';
        return '┼';
    }

    /// <summary>Prefer rounded corners when a diagonal suggests curvature.</summary>
    private static char? SoftCorner(int ortho, int diag) => ortho switch
    {
        // └ with NE or similar arc continuation → ╰
        N | E when (diag & (NE | SE | NW)) != 0 => '╰',
        N | W when (diag & (NW | SW | NE)) != 0 => '╯',
        S | E when (diag & (SE | NE | SW)) != 0 => '╭',
        S | W when (diag & (SW | SE | NW)) != 0 => '╮',
        _ => null,
    };

    private static int Pop4(int v)
    {
        int n = 0;
        for (int i = 0; i < 4; i++)
            if ((v & (1 << i)) != 0) n++;
        return n;
    }
}

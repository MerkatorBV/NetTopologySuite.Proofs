using System.Text;

namespace WktUnicodeIllustrator;

/// <summary>
/// Renders a <see cref="Canvas"/> as ANSI-coloured Unicode.
/// A = blue, B = red, Result = green. Overlaps pick a blend glyph/colour rule.
/// </summary>
internal static class AnsiRenderer
{
    // Bright colours for dark terminals; reset after each cell so plain text stays clean.
    private const string Reset = "\x1b[0m";
    private const string Blue = "\x1b[94m";   // bright blue — A
    private const string Red = "\x1b[91m";    // bright red  — B
    private const string Green = "\x1b[92m";  // bright green — result / op
    private const string Magenta = "\x1b[95m"; // A∩B before op (shared pixel, no result yet)
    private const string Dim = "\x1b[90m";

    public static string Render(Canvas canvas, bool showResult, bool useColor = true)
    {
        var sb = new StringBuilder(canvas.Width * canvas.Height * 8);
        // Top border
        sb.Append(useColor ? Dim : "");
        sb.Append('┌').Append(new string('─', canvas.Width)).Append('┐');
        if (useColor) sb.Append(Reset);
        sb.AppendLine();

        for (int y = 0; y < canvas.Height; y++)
        {
            sb.Append(useColor ? Dim : "").Append('│');
            if (useColor) sb.Append(Reset);

            for (int x = 0; x < canvas.Width; x++)
            {
                var cell = canvas[x, y];
                char g = ResolveGlyph(cell, showResult);
                if (g == '\0' || g == ' ')
                {
                    sb.Append(' ');
                    continue;
                }

                if (!useColor)
                {
                    sb.Append(g);
                    continue;
                }

                string color = PickColor(cell.Layers, showResult);
                sb.Append(color).Append(g).Append(Reset);
            }

            sb.Append(useColor ? Dim : "").Append('│');
            if (useColor) sb.Append(Reset);
            sb.AppendLine();
        }

        sb.Append(useColor ? Dim : "");
        sb.Append('└').Append(new string('─', canvas.Width)).Append('┘');
        if (useColor) sb.Append(Reset);
        sb.AppendLine();
        return sb.ToString();
    }

    public static string Legend(bool useColor = true)
    {
        if (!useColor)
            return "Legend: A = blue layer  ·  B = red layer  ·  result = green  ·  A∩B pixel = magenta";

        return $"Legend: {Blue}A (blue){Reset}  ·  {Red}B (red){Reset}  ·  {Green}result (green){Reset}  ·  {Magenta}A∩B pixel{Reset}";
    }

    private static char ResolveGlyph(Cell cell, bool showResult)
    {
        if (cell.Layers == Layer.None) return ' ';

        // After the operation: result cells get a clear green mark (●), not a
        // recolored input stroke, so the op is visually distinct.
        if (showResult && cell.Layers.HasFlag(Layer.Result))
        {
            char r = cell.GlyphResult;
            // Point results stay ●; linear result pieces keep structure glyphs.
            if (r is '\0' or ' ' or '·') return '●';
            return r;
        }

        // Inputs-only: cells touched by both A and B show a cross so the
        // coincidence is visible even before the green result overlay.
        bool a = cell.Layers.HasFlag(Layer.A);
        bool b = cell.Layers.HasFlag(Layer.B);
        if (a && b) return '╳';
        if (a && cell.GlyphA is not ('\0' or ' ')) return cell.GlyphA;
        if (b && cell.GlyphB is not ('\0' or ' ')) return cell.GlyphB;
        if (a || b) return '·';
        return ' ';
    }

    private static string PickColor(Layer layers, bool showResult)
    {
        if (showResult && layers.HasFlag(Layer.Result))
            return Green;
        bool a = layers.HasFlag(Layer.A);
        bool b = layers.HasFlag(Layer.B);
        if (a && b) return Magenta;
        if (a) return Blue;
        if (b) return Red;
        return Dim;
    }
}

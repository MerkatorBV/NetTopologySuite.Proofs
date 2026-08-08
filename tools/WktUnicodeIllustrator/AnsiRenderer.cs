using System.Text;

namespace WktUnicodeIllustrator;

/// <summary>
/// Renders a <see cref="Canvas"/> as ANSI-coloured Unicode.
/// A = blue, B = red, Result = green, overshoot A = maroon, overshoot B = navy.
/// </summary>
internal static class AnsiRenderer
{
    private const string Reset = "\x1b[0m";
    private const string Blue = "\x1b[94m";              // bright blue — A
    private const string Red = "\x1b[91m";               // bright red  — B
    private const string Green = "\x1b[92m";             // bright green — result
    private const string Magenta = "\x1b[95m";           // A∩B pixel
    private const string Maroon = "\x1b[38;2;128;0;0m";  // A overshoot (self-overlap)
    private const string Navy = "\x1b[38;2;0;0;128m";    // B overshoot (self-overlap)
    private const string Dim = "\x1b[90m";

    public static string Render(Canvas canvas, bool showResult, bool useColor = true)
    {
        var sb = new StringBuilder(canvas.Width * canvas.Height * 12);
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
        {
            return "Legend: A = blue · B = red · result = green · A∩B = magenta · "
                 + "A-overshoot = maroon · B-overshoot = navy";
        }

        return $"Legend: {Blue}A (blue){Reset}  ·  {Red}B (red){Reset}  ·  {Green}result (green){Reset}  ·  "
             + $"{Magenta}A∩B{Reset}  ·  {Maroon}A-overshoot (maroon){Reset}  ·  {Navy}B-overshoot (navy){Reset}";
    }

    private static char ResolveGlyph(Cell cell, bool showResult)
    {
        if (cell.Layers == Layer.None) return ' ';

        if (showResult && cell.Layers.HasFlag(Layer.Result))
        {
            char r = cell.GlyphResult;
            if (r is '\0' or ' ' or '·') return '●';
            return r;
        }

        // Overshoot paints on top of base A/B so self-overlap is visible.
        bool oa = cell.Layers.HasFlag(Layer.OvershootA);
        bool ob = cell.Layers.HasFlag(Layer.OvershootB);
        if (oa && ob) return '╳';
        if (oa && cell.GlyphOvershootA is not ('\0' or ' ')) return cell.GlyphOvershootA;
        if (ob && cell.GlyphOvershootB is not ('\0' or ' ')) return cell.GlyphOvershootB;
        if (oa || ob) return '═'; // fallback double-line feel for overshoot

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

        bool oa = layers.HasFlag(Layer.OvershootA);
        bool ob = layers.HasFlag(Layer.OvershootB);
        if (oa && ob) return Magenta; // both overshoots coincide
        if (oa) return Maroon;
        if (ob) return Navy;

        bool a = layers.HasFlag(Layer.A);
        bool b = layers.HasFlag(Layer.B);
        if (a && b) return Magenta;
        if (a) return Blue;
        if (b) return Red;
        return Dim;
    }
}

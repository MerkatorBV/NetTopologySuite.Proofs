using System.Text;

namespace WktUnicodeIllustrator;

/// <summary>
/// Prints a <see cref="Doc"/> as ANSI terminal text: colour roles map to SGR
/// codes, <see cref="DocColor.Default"/> runs are emitted bare. Encoding only —
/// wording, glyphs, and layout are the <see cref="Style"/> step's business.
/// </summary>
internal static class AnsiPrinter
{
    private const string Reset = "\x1b[0m";
    private const string Blue = "\x1b[94m";              // bright blue — A
    private const string Red = "\x1b[91m";               // bright red  — B
    private const string Green = "\x1b[92m";             // bright green — result
    private const string Magenta = "\x1b[95m";           // A∩B pixel
    private const string Maroon = "\x1b[38;2;128;0;0m";  // A overshoot (self-overlap)
    private const string Navy = "\x1b[38;2;0;0;128m";    // B overshoot (self-overlap)
    private const string Dim = "\x1b[90m";

    public static string Print(Doc doc)
    {
        var sb = new StringBuilder();
        foreach (var line in doc.Lines)
        {
            foreach (var run in line)
            {
                if (run.Color == DocColor.Default)
                {
                    sb.Append(run.Text);
                    continue;
                }
                sb.Append(Sgr(run.Color)).Append(run.Text).Append(Reset);
            }
            sb.AppendLine();
        }
        return sb.ToString();
    }

    private static string Sgr(DocColor color) => color switch
    {
        DocColor.Dim => Dim,
        DocColor.A => Blue,
        DocColor.B => Red,
        DocColor.Result => Green,
        DocColor.Both => Magenta,
        DocColor.OvershootA => Maroon,
        DocColor.OvershootB => Navy,
        _ => "",
    };
}

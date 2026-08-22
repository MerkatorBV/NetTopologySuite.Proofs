using System.Reflection;
using SixLabors.Fonts;
using SixLabors.ImageSharp;
using SixLabors.ImageSharp.Drawing.Processing;
using SixLabors.ImageSharp.PixelFormats;
using SixLabors.ImageSharp.Processing;

namespace WktUnicodeIllustrator;

/// <summary>
/// Prints a <see cref="Doc"/> as a PNG facsimile: the same glyphs and colours a
/// terminal shows, rastered with the embedded Cascadia Mono font on the Windows
/// Terminal "Campbell" palette. The reproducible replacement for a manual
/// screenshot — encoding only, like every printer.
/// Long lines wrap at max(80, widest panel line), mimicking a terminal window.
/// </summary>
internal static class PngPrinter
{
    private const float FontSize = 16f;
    private const int Margin = 12;
    public const int MinWrapColumns = 80;

    // Windows Terminal Campbell palette (bright variants match the SGR codes
    // AnsiPrinter emits); maroon/navy are the exact truecolor values.
    private static readonly Color Background = Color.FromRgb(0x0C, 0x0C, 0x0C);
    private static readonly Color Foreground = Color.FromRgb(0xCC, 0xCC, 0xCC);

    private static readonly Lazy<Font> Mono = new(LoadFont);

    public static byte[] Print(Doc doc)
    {
        var font = Mono.Value;
        float cellW = TextMeasurer.MeasureAdvance("█", new TextOptions(font)).Width;
        // The font's designed line advance — box-drawing glyphs span exactly this,
        // so vertical strokes connect across rows like they do in a terminal.
        var fm = font.FontMetrics;
        float cellH = MathF.Ceiling(
            (fm.HorizontalMetrics.Ascender - fm.HorizontalMetrics.Descender + fm.HorizontalMetrics.LineGap)
            * font.Size / fm.UnitsPerEm);

        var lines = Wrap(doc.Lines, WrapColumns(doc));

        int maxCols = 1;
        foreach (var line in lines)
        {
            int cols = 0;
            foreach (var run in line) cols += run.Text.Length;
            maxCols = Math.Max(maxCols, cols);
        }

        int width = Margin * 2 + (int)MathF.Ceiling(maxCols * cellW);
        int height = Margin * 2 + Math.Max(1, lines.Count) * (int)cellH;

        using var image = new Image<Rgba32>(width, height);
        image.Mutate(ctx =>
        {
            ctx.Fill(Background);
            for (int i = 0; i < lines.Count; i++)
            {
                float y = Margin + i * (int)cellH;
                int col = 0;
                foreach (var run in lines[i])
                {
                    if (run.Text.Length == 0) continue;
                    var origin = new PointF(Margin + col * cellW, y);
                    var options = new RichTextOptions(font) { Origin = origin };
                    ctx.DrawText(options, run.Text, Ink(run.Color));
                    col += run.Text.Length;
                }
            }
        });

        using var ms = new MemoryStream();
        image.SaveAsPng(ms);
        return ms.ToArray();
    }

    private static Color Ink(DocColor color) => color switch
    {
        DocColor.Dim => Color.FromRgb(0x76, 0x76, 0x76),
        DocColor.A => Color.FromRgb(0x3B, 0x78, 0xFF),
        DocColor.B => Color.FromRgb(0xE7, 0x48, 0x56),
        DocColor.Result => Color.FromRgb(0x16, 0xC6, 0x0C),
        DocColor.Both => Color.FromRgb(0xB4, 0x00, 0x9E),
        DocColor.OvershootA => Color.FromRgb(0x80, 0x00, 0x00),
        DocColor.OvershootB => Color.FromRgb(0x00, 0x00, 0x80),
        _ => Foreground,
    };

    /// <summary>Wrap width: the widest framed panel line, but at least 80 columns.</summary>
    private static int WrapColumns(Doc doc)
    {
        int frame = 0;
        foreach (var line in doc.Lines)
        {
            if (line.Count == 0) continue;
            string first = line[0].Text;
            if (first.Length > 0 && first[0] is '┌' or '│' or '└')
            {
                int cols = 0;
                foreach (var run in line) cols += run.Text.Length;
                frame = Math.Max(frame, cols);
            }
        }
        return Math.Max(MinWrapColumns, frame);
    }

    private static List<List<Run>> Wrap(List<List<Run>> lines, int columns)
    {
        var result = new List<List<Run>>();
        foreach (var line in lines)
        {
            int total = 0;
            foreach (var run in line) total += run.Text.Length;
            if (total <= columns)
            {
                result.Add(line);
                continue;
            }

            var current = new List<Run>();
            int used = 0;
            foreach (var run in line)
            {
                string rest = run.Text;
                while (rest.Length > 0)
                {
                    int room = columns - used;
                    if (room == 0)
                    {
                        result.Add(current);
                        current = new List<Run>();
                        used = 0;
                        room = columns;
                    }
                    int take = Math.Min(room, rest.Length);
                    current.Add(new Run(rest[..take], run.Color));
                    used += take;
                    rest = rest[take..];
                }
            }
            if (current.Count > 0)
                result.Add(current);
        }
        return result;
    }

    private static Font LoadFont()
    {
        using var stream = Assembly.GetExecutingAssembly().GetManifestResourceStream(
            "WktUnicodeIllustrator.assets.CascadiaMono-Regular.ttf")
            ?? throw new InvalidOperationException("Embedded font CascadiaMono-Regular.ttf not found.");
        var collection = new FontCollection();
        var family = collection.Add(stream);
        return family.CreateFont(FontSize);
    }
}

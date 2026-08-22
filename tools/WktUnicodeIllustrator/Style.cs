using System.Text;
using NetTopologySuite.Geometries;

namespace WktUnicodeIllustrator;

/// <summary>
/// Styles a <see cref="Scenario"/> into a <see cref="Doc"/>: header, legend,
/// and framed panels with structure glyphs and layer-precedence colours.
/// Owns everything about how a sketch reads; printers only encode.
/// `colored` is a styling input, not an encoding switch — the legend wording
/// differs between the plain and coloured forms.
/// </summary>
internal static class Style
{
    public static Doc Build(Scenario s, bool colored)
    {
        var doc = new Doc();

        doc.AddLine(new Run("WKT Unicode illustrator — line / curve cases"));
        doc.AddLine(new Run($"  A ({Describe(s.A)}): {s.A.AsText()}"));
        doc.AddLine(new Run($"  B ({Describe(s.B)}): {s.B.AsText()}"));
        doc.AddLine(new Run($"  op: {s.OpName}"));
        if (s.ShowOvershoot)
        {
            doc.AddLine(new Run(s.OvershootA is { IsEmpty: false }
                ? $"  A-overshoot (maroon): {s.OvershootA.AsText()}"
                : "  A-overshoot (maroon): (none)"));
            doc.AddLine(new Run(s.OvershootB is { IsEmpty: false }
                ? $"  B-overshoot (navy): {s.OvershootB.AsText()}"
                : "  B-overshoot (navy): (none)"));
        }
        if (s.Result is null)
            doc.AddLine(new Run("  result: (skipped)"));
        else if (s.Result.IsEmpty)
            doc.AddLine(new Run("  result: EMPTY"));
        else
            doc.AddLine(new Run($"  result ({Describe(s.Result)}): {s.Result.AsText()}"));
        doc.AddBlank();

        doc.AddLine(Legend(colored));
        doc.AddBlank();

        var glyphs = ComputeGlyphs(s.Canvas);

        doc.AddLine(new Run("— inputs (A blue, B red; overshoot maroon/navy; magenta where A∩B) —"));
        AddPanel(doc, s.Canvas, glyphs, showResult: false, colored);
        doc.AddBlank();

        if (s.Result is not null)
        {
            doc.AddLine(new Run("— after operation (result in green) —"));
            AddPanel(doc, s.Canvas, glyphs, showResult: true, colored);
        }

        return doc;
    }

    private static List<Run> Legend(bool colored)
    {
        if (!colored)
        {
            return new List<Run>
            {
                new("Legend: A = blue · B = red · result = green · A∩B = magenta · "
                    + "A-overshoot = maroon · B-overshoot = navy"),
            };
        }

        return new List<Run>
        {
            new("Legend: "),
            new("A (blue)", DocColor.A),
            new("  ·  "),
            new("B (red)", DocColor.B),
            new("  ·  "),
            new("result (green)", DocColor.Result),
            new("  ·  "),
            new("A∩B", DocColor.Both),
            new("  ·  "),
            new("A-overshoot (maroon)", DocColor.OvershootA),
            new("  ·  "),
            new("B-overshoot (navy)", DocColor.OvershootB),
        };
    }

    private static void AddPanel(Doc doc, Canvas canvas, GlyphSet glyphs, bool showResult, bool colored)
    {
        DocColor frame = colored ? DocColor.Dim : DocColor.Default;

        doc.AddLine(new Run("┌" + new string('─', canvas.Width) + "┐", frame));

        for (int y = 0; y < canvas.Height; y++)
        {
            var runs = new List<Run> { new("│", frame) };
            var plain = new StringBuilder();

            for (int x = 0; x < canvas.Width; x++)
            {
                Layer layers = canvas[x, y];
                char g = ResolveGlyph(layers, glyphs, x, y, showResult);
                if (g == '\0' || g == ' ' || !colored)
                {
                    plain.Append(g is '\0' ? ' ' : g);
                    continue;
                }

                if (plain.Length > 0)
                {
                    runs.Add(new Run(plain.ToString()));
                    plain.Clear();
                }
                runs.Add(new Run(g.ToString(), PickColor(layers, showResult)));
            }

            if (plain.Length > 0)
                runs.Add(new Run(plain.ToString()));
            runs.Add(new Run("│", frame));
            doc.AddLine(runs);
        }

        doc.AddLine(new Run("└" + new string('─', canvas.Width) + "┘", frame));
    }

    /// <summary>Per-layer structure glyphs, computed once and shared by both panels.</summary>
    private sealed class GlyphSet
    {
        public required char[,] A { get; init; }
        public required char[,] B { get; init; }
        public required char[,] Result { get; init; }
        public required char[,] OvershootA { get; init; }
        public required char[,] OvershootB { get; init; }
    }

    private static GlyphSet ComputeGlyphs(Canvas canvas)
    {
        var set = new GlyphSet
        {
            A = new char[canvas.Height, canvas.Width],
            B = new char[canvas.Height, canvas.Width],
            Result = new char[canvas.Height, canvas.Width],
            OvershootA = new char[canvas.Height, canvas.Width],
            OvershootB = new char[canvas.Height, canvas.Width],
        };

        for (int y = 0; y < canvas.Height; y++)
        {
            for (int x = 0; x < canvas.Width; x++)
            {
                Layer layers = canvas[x, y];
                if (layers.HasFlag(Layer.A))
                    set.A[y, x] = StructureGlyph.Choose(canvas, x, y, Layer.A);
                if (layers.HasFlag(Layer.B))
                    set.B[y, x] = StructureGlyph.Choose(canvas, x, y, Layer.B);
                if (layers.HasFlag(Layer.OvershootA))
                    set.OvershootA[y, x] = StructureGlyph.Choose(canvas, x, y, Layer.OvershootA);
                if (layers.HasFlag(Layer.OvershootB))
                    set.OvershootB[y, x] = StructureGlyph.Choose(canvas, x, y, Layer.OvershootB);
                if (layers.HasFlag(Layer.Result))
                    set.Result[y, x] = StructureGlyph.ChooseResult(canvas, x, y);
            }
        }

        return set;
    }

    private static char ResolveGlyph(Layer layers, GlyphSet glyphs, int x, int y, bool showResult)
    {
        if (layers == Layer.None) return ' ';

        if (showResult && layers.HasFlag(Layer.Result))
        {
            char r = glyphs.Result[y, x];
            if (r is '\0' or ' ' or '·') return '●';
            return r;
        }

        // Overshoot paints on top of base A/B so self-overlap is visible.
        bool oa = layers.HasFlag(Layer.OvershootA);
        bool ob = layers.HasFlag(Layer.OvershootB);
        if (oa && ob) return '╳';
        if (oa && glyphs.OvershootA[y, x] is not ('\0' or ' ')) return glyphs.OvershootA[y, x];
        if (ob && glyphs.OvershootB[y, x] is not ('\0' or ' ')) return glyphs.OvershootB[y, x];
        if (oa || ob) return '═'; // fallback double-line feel for overshoot

        bool a = layers.HasFlag(Layer.A);
        bool b = layers.HasFlag(Layer.B);
        if (a && b) return '╳';
        if (a && glyphs.A[y, x] is not ('\0' or ' ')) return glyphs.A[y, x];
        if (b && glyphs.B[y, x] is not ('\0' or ' ')) return glyphs.B[y, x];
        if (a || b) return '·';
        return ' ';
    }

    private static DocColor PickColor(Layer layers, bool showResult)
    {
        if (showResult && layers.HasFlag(Layer.Result))
            return DocColor.Result;

        bool oa = layers.HasFlag(Layer.OvershootA);
        bool ob = layers.HasFlag(Layer.OvershootB);
        if (oa && ob) return DocColor.Both; // both overshoots coincide
        if (oa) return DocColor.OvershootA;
        if (ob) return DocColor.OvershootB;

        bool a = layers.HasFlag(Layer.A);
        bool b = layers.HasFlag(Layer.B);
        if (a && b) return DocColor.Both;
        if (a) return DocColor.A;
        if (b) return DocColor.B;
        return DocColor.Dim;
    }

    private static string Describe(Geometry g) =>
        g switch
        {
            Point => "Point",
            LineString ls => ls.IsClosed ? "LinearRing" : "LineString",
            MultiLineString => "MultiLineString",
            Polygon => "Polygon",
            MultiPoint => "MultiPoint",
            GeometryCollection => g.GeometryType,
            _ => g.GeometryType,
        };
}

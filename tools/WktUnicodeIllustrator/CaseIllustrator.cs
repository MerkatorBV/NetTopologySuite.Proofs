using System.Text;
using NetTopologySuite.Geometries;

namespace WktUnicodeIllustrator;

/// <summary>
/// Pure entry for WKT pair Unicode case sketches (lines and SQL/MM curves).
/// Used by the CLI and by automated checks — same code path both ways.
/// </summary>
public static class CaseIllustrator
{
    public const string DefaultA = "LINESTRING (0 0, 10 10)";
    public const string DefaultB = "LINESTRING (0 10, 10 0)";

    /// <summary>Two arcs crossing near the middle of the square (curve demo).</summary>
    public const string DefaultCurveA = "CIRCULARSTRING (0 0, 5 8, 10 0)";
    public const string DefaultCurveB = "CIRCULARSTRING (0 10, 5 2, 10 10)";

    public static IllustratorResult Render(
        string? wktA = null,
        string? wktB = null,
        string operation = "intersection",
        int width = 41,
        int height = 21,
        bool useColor = false)
    {
        wktA ??= DefaultA;
        wktB ??= DefaultB;

        Geometry a, b;
        try
        {
            a = GeometryCurves.Parse(wktA);
            b = GeometryCurves.Parse(wktB);
        }
        catch (Exception ex)
        {
            return IllustratorResult.Fail(2, $"WKT parse failed: {ex.Message}");
        }

        if (a.IsEmpty || b.IsEmpty)
            return IllustratorResult.Fail(2, "A and B must be non-empty geometries.");

        // Curve overlay is playground: densify for ops + draw while keeping native types for labels/WKT.
        Geometry aDraw = GeometryCurves.Linearize(a);
        Geometry bDraw = GeometryCurves.Linearize(b);

        var env = aDraw.EnvelopeInternal.Copy();
        env.ExpandToInclude(bDraw.EnvelopeInternal);

        Geometry? result;
        string opName = operation;
        try
        {
            result = operation.ToLowerInvariant() switch
            {
                "intersection" or "cross" or "x" => aDraw.Intersection(bDraw),
                "union" => aDraw.Union(bDraw),
                "difference" => aDraw.Difference(bDraw),
                "symdifference" or "xor" => aDraw.SymmetricDifference(bDraw),
                "none" => null,
                _ => aDraw.Intersection(bDraw),
            };
            if (operation is "cross" or "x")
                opName = "intersection";
            if (GeometryCurves.IsCurve(a) || GeometryCurves.IsCurve(b))
                opName += " (linearized curves)";
        }
        catch (Exception ex)
        {
            return IllustratorResult.Fail(3, $"Operation failed: {ex.Message}");
        }

        if (result is { IsEmpty: false })
            env.ExpandToInclude(result.EnvelopeInternal);

        if (env.Width == 0) env.ExpandBy(1, 0);
        if (env.Height == 0) env.ExpandBy(0, 1);

        width = Math.Clamp(width, 8, 200);
        height = Math.Clamp(height, 4, 100);

        var map = new WorldToGrid(env, width, height);
        var canvas = new Canvas(width, height);

        Rasterizer.DrawGeometry(canvas, map, aDraw, Layer.A);
        Rasterizer.DrawGeometry(canvas, map, bDraw, Layer.B);
        if (result is { IsEmpty: false })
            Rasterizer.DrawGeometry(canvas, map, result, Layer.Result);

        // Structure-based pass: match local stroke connectivity to box/diagonal
        // glyphs (Xu–Zhang–Wong structure ASCII art idea, fixed glyph palette).
        StructureGlyph.Assign(canvas);

        var sb = new StringBuilder();
        sb.AppendLine("WKT Unicode illustrator — line / curve cases");
        sb.AppendLine($"  A ({Describe(a)}): {a.AsText()}");
        sb.AppendLine($"  B ({Describe(b)}): {b.AsText()}");
        sb.AppendLine($"  op: {opName}");
        if (result is null)
            sb.AppendLine("  result: (skipped)");
        else if (result.IsEmpty)
            sb.AppendLine("  result: EMPTY");
        else
            sb.AppendLine($"  result ({Describe(result)}): {result.AsText()}");
        sb.AppendLine();
        sb.AppendLine(AnsiRenderer.Legend(useColor));
        sb.AppendLine();

        sb.AppendLine("— inputs (A blue, B red; magenta where pixels coincide) —");
        sb.Append(AnsiRenderer.Render(canvas, showResult: false, useColor: useColor));
        sb.AppendLine();

        if (result is not null)
        {
            sb.AppendLine("— after operation (result in green) —");
            sb.Append(AnsiRenderer.Render(canvas, showResult: true, useColor: useColor));
        }

        return new IllustratorResult
        {
            ExitCode = 0,
            Text = sb.ToString(),
            ResultWkt = result is null ? null : result.AsText(),
            ResultIsEmpty = result?.IsEmpty ?? true,
        };
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

public sealed class IllustratorResult
{
    public int ExitCode { get; init; }
    public string Text { get; init; } = "";
    public string? ResultWkt { get; init; }
    public bool ResultIsEmpty { get; init; }
    public string? Error { get; init; }

    public static IllustratorResult Fail(int code, string error) =>
        new() { ExitCode = code, Error = error, Text = error + Environment.NewLine };
}

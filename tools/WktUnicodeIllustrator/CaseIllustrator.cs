using System.Text;
using NetTopologySuite.Geometries;
using NetTopologySuite.IO;

namespace WktUnicodeIllustrator;

/// <summary>
/// Pure entry for the line–line (and general WKT pair) Unicode case sketch.
/// Used by the CLI and by automated checks — same code path both ways.
/// </summary>
public static class CaseIllustrator
{
    public const string DefaultA = "LINESTRING (0 0, 10 10)";
    public const string DefaultB = "LINESTRING (0 10, 10 0)";

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

        var reader = new WKTReader { IsOldNtsCoordinateSyntaxAllowed = false };
        Geometry a, b;
        try
        {
            a = reader.Read(wktA);
            b = reader.Read(wktB);
        }
        catch (Exception ex)
        {
            return IllustratorResult.Fail(2, $"WKT parse failed: {ex.Message}");
        }

        if (a.IsEmpty || b.IsEmpty)
            return IllustratorResult.Fail(2, "A and B must be non-empty geometries.");

        var env = a.EnvelopeInternal.Copy();
        env.ExpandToInclude(b.EnvelopeInternal);

        Geometry? result;
        string opName = operation;
        try
        {
            result = operation.ToLowerInvariant() switch
            {
                "intersection" or "cross" or "x" => a.Intersection(b),
                "union" => a.Union(b),
                "difference" => a.Difference(b),
                "symdifference" or "xor" => a.SymmetricDifference(b),
                "none" => null,
                _ => a.Intersection(b),
            };
            if (operation is "cross" or "x")
                opName = "intersection (line-line cross)";
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

        Rasterizer.DrawGeometry(canvas, map, a, Layer.A);
        Rasterizer.DrawGeometry(canvas, map, b, Layer.B);
        if (result is { IsEmpty: false })
            Rasterizer.DrawGeometry(canvas, map, result, Layer.Result);

        var sb = new StringBuilder();
        sb.AppendLine("WKT Unicode illustrator — MVP (line–line cross)");
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
            GeometryCollection => "GeometryCollection",
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

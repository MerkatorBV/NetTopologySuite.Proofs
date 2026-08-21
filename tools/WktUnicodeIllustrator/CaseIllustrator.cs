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

    /// <summary>
    /// Self-overlapping circular string: second arc is the reverse of the first
    /// (same mid control) — full path retrace = overshoot / self-overlap.
    /// </summary>
    public const string DefaultOvershootA =
        "CIRCULARSTRING (0 0, 5 6, 10 0, 5 6, 0 0)";

    /// <summary>Companion self-overlapping arc for B (upper band, reverse retrace).</summary>
    public const string DefaultOvershootB =
        "CIRCULARSTRING (0 10, 5 4, 10 10, 5 4, 0 10)";

    public static IllustratorResult Render(
        string? wktA = null,
        string? wktB = null,
        string operation = "intersection",
        int width = 41,
        int height = 21,
        bool useColor = false,
        bool showOvershoot = true)
    {
        wktA ??= DefaultA;
        wktB ??= DefaultB;

        // No chord fallback, by design: a lines-only build must never render a
        // curve case as its control chords — that picture lies.
        if (!GeometryCurves.HasCurveSupport
            && (GeometryCurves.ContainsCurveWkt(wktA) || GeometryCurves.ContainsCurveWkt(wktB)))
        {
            return IllustratorResult.Fail(4,
                "Curve WKT requires the curve-aware NetTopologySuite clone; this build uses "
                + "NuGet NetTopologySuite (lines only). Clone NetTopologySuite (branch "
                + "feat/curves-structure-wkt-foundation) next to this repo or pass "
                + "-p:NtsProject=<path-to-NetTopologySuite.csproj>.");
        }

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

        Geometry aDraw = GeometryCurves.Linearize(a);
        Geometry bDraw = GeometryCurves.Linearize(b);

        Geometry? overA = null;
        Geometry? overB = null;
        try
        {
            if (showOvershoot)
            {
                overA = Overshoot.ExtractSelfOverlap(a);
                overB = Overshoot.ExtractSelfOverlap(b);
            }
        }
        catch (Exception ex)
        {
            return IllustratorResult.Fail(3, $"Overshoot extract failed: {ex.Message}");
        }

        var env = aDraw.EnvelopeInternal.Copy();
        env.ExpandToInclude(bDraw.EnvelopeInternal);
        if (overA is { IsEmpty: false }) env.ExpandToInclude(overA.EnvelopeInternal);
        if (overB is { IsEmpty: false }) env.ExpandToInclude(overB.EnvelopeInternal);

        // Self-overlapping densified curves are not overlay-safe; node segments first.
        Geometry aOp = Overshoot.PrepareForOverlay(aDraw);
        Geometry bOp = Overshoot.PrepareForOverlay(bDraw);

        Geometry? result;
        string opName = operation;
        try
        {
            result = operation.ToLowerInvariant() switch
            {
                "intersection" or "cross" or "x" => aOp.Intersection(bOp),
                "union" => aOp.Union(bOp),
                "difference" => aOp.Difference(bOp),
                "symdifference" or "xor" => aOp.SymmetricDifference(bOp),
                "none" => null,
                _ => aOp.Intersection(bOp),
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
        if (overA is { IsEmpty: false })
            Rasterizer.DrawGeometry(canvas, map, overA, Layer.OvershootA);
        if (overB is { IsEmpty: false })
            Rasterizer.DrawGeometry(canvas, map, overB, Layer.OvershootB);
        if (result is { IsEmpty: false })
            Rasterizer.DrawGeometry(canvas, map, result, Layer.Result);

        StructureGlyph.Assign(canvas);

        var sb = new StringBuilder();
        sb.AppendLine("WKT Unicode illustrator — line / curve cases");
        sb.AppendLine($"  A ({Describe(a)}): {a.AsText()}");
        sb.AppendLine($"  B ({Describe(b)}): {b.AsText()}");
        sb.AppendLine($"  op: {opName}");
        if (showOvershoot)
        {
            sb.AppendLine(overA is { IsEmpty: false }
                ? $"  A-overshoot (maroon): {overA.AsText()}"
                : "  A-overshoot (maroon): (none)");
            sb.AppendLine(overB is { IsEmpty: false }
                ? $"  B-overshoot (navy): {overB.AsText()}"
                : "  B-overshoot (navy): (none)");
        }
        if (result is null)
            sb.AppendLine("  result: (skipped)");
        else if (result.IsEmpty)
            sb.AppendLine("  result: EMPTY");
        else
            sb.AppendLine($"  result ({Describe(result)}): {result.AsText()}");
        sb.AppendLine();
        sb.AppendLine(AnsiRenderer.Legend(useColor));
        sb.AppendLine();

        sb.AppendLine("— inputs (A blue, B red; overshoot maroon/navy; magenta where A∩B) —");
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
            OvershootAWkt = overA is { IsEmpty: false } ? overA.AsText() : null,
            OvershootBWkt = overB is { IsEmpty: false } ? overB.AsText() : null,
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
    public string? OvershootAWkt { get; init; }
    public string? OvershootBWkt { get; init; }
    public string? Error { get; init; }

    public static IllustratorResult Fail(int code, string error) =>
        new() { ExitCode = code, Error = error, Text = error + Environment.NewLine };
}

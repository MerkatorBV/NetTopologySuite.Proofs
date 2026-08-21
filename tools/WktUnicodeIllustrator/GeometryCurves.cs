using NetTopologySuite.Geometries;
#if CURVE_NTS
using NetTopologySuite.Geometries.Curves;
#endif
using NetTopologySuite.IO;

namespace WktUnicodeIllustrator;

/// <summary>
/// Curve-aware helpers on top of the local NetTopologySuite clone
/// (<c>CIRCULARSTRING</c> / <c>COMPOUNDCURVE</c> / <c>CURVEPOLYGON</c> in WKTReader).
/// Stock NuGet 2.6 has no SQL/MM curves; ops/draw densify arcs to polylines
/// because curve overlay is still playground.
/// </summary>
internal static class GeometryCurves
{
    private static readonly GeometryFactory Gf = GeometryFactory.Default;

    /// <summary>True when compiled against the curve-aware NTS clone (CURVE_NTS).</summary>
    public static bool HasCurveSupport =>
#if CURVE_NTS
        true;
#else
        false;
#endif

    private static readonly string[] CurveWktKeywords =
    {
        "CIRCULARSTRING", "COMPOUNDCURVE", "CURVEPOLYGON", "MULTICURVE", "MULTISURFACE",
    };

    /// <summary>Cheap pre-parse check for SQL/MM curve WKT keywords.</summary>
    public static bool ContainsCurveWkt(string wkt) =>
        CurveWktKeywords.Any(k => wkt.Contains(k, StringComparison.OrdinalIgnoreCase));

    /// <summary>Parse WKT with the linked NTS (curve-aware when using the local clone).</summary>
    public static Geometry Parse(string wkt)
    {
        var reader = new WKTReader { IsOldNtsCoordinateSyntaxAllowed = false };
        return reader.Read(wkt.Trim());
    }

    /// <summary>
    /// Produce a linear geometry safe for rasterization and NTS overlay ops.
    /// Prefer <see cref="ILinearizable{T}"/> when present; otherwise densify
    /// playground <see cref="CircularString"/> / <see cref="CompoundCurve"/>.
    /// </summary>
    public static Geometry Linearize(Geometry g, int samplesPerArc = 48)
    {
        if (g is null || g.IsEmpty) return g;

#if CURVE_NTS
        // Official linearize path when the type implements it (Curve package / future NTS).
        if (g is ILinearizable<LineString> linLs)
            return linLs.Linearize();
        if (g is ILinearizable<Polygon> linPoly)
            return linPoly.Linearize();
        if (g is ILinearizable<Geometry> linAny)
            return linAny.Linearize();
#endif

        return g switch
        {
#if CURVE_NTS
            CircularString cs => DensifyCircularString(cs, samplesPerArc),
            CompoundCurve cc => DensifyCompoundCurve(cc, samplesPerArc),
            CurvePolygon cp => DensifyCurvePolygon(cp, samplesPerArc),
#endif
            GeometryCollection gc when NeedsLinearize(gc) => LinearizeCollection(gc, samplesPerArc),
            _ => g,
        };
    }

    public static bool IsCurve(Geometry g) =>
#if CURVE_NTS
        g is CircularString or CompoundCurve or CurvePolygon
        || g is ILinearizable<LineString>
        ||
#endif
        (g is GeometryCollection coll && NeedsLinearize(coll));

    private static bool NeedsLinearize(GeometryCollection gc)
    {
        for (int i = 0; i < gc.NumGeometries; i++)
            if (IsCurve(gc.GetGeometryN(i))) return true;
        return false;
    }

    private static Geometry LinearizeCollection(GeometryCollection gc, int samplesPerArc)
    {
        var parts = new Geometry[gc.NumGeometries];
        for (int i = 0; i < gc.NumGeometries; i++)
            parts[i] = Linearize(gc.GetGeometryN(i), samplesPerArc);
        return gc.Factory.BuildGeometry(parts);
    }

#if CURVE_NTS
    private static LineString DensifyCircularString(CircularString cs, int samplesPerArc)
    {
        var controls = cs.CoordinateSequence;
        if (controls.Count == 0)
            return Gf.CreateLineString();

        var pts = new List<Coordinate>();
        // 2n+1 controls → n arcs at (0,1,2), (2,3,4), …
        for (int i = 0; i + 2 < controls.Count; i += 2)
        {
            var a = controls.GetCoordinate(i);
            var b = controls.GetCoordinate(i + 1);
            var c = controls.GetCoordinate(i + 2);
            var arc = SampleArc(a, b, c, samplesPerArc);
            if (pts.Count == 0)
                pts.AddRange(arc);
            else
                pts.AddRange(arc.Skip(1));
        }

        if (pts.Count < 2)
            return Gf.CreateLineString();
        return Gf.CreateLineString(pts.ToArray());
    }

    private static LineString DensifyCompoundCurve(CompoundCurve cc, int samplesPerArc)
    {
        var pts = new List<Coordinate>();
        foreach (var component in cc.Curves)
        {
            Geometry lin = component switch
            {
                CircularString cs => DensifyCircularString(cs, samplesPerArc),
                LineString ls => ls,
                _ => Linearize(component, samplesPerArc),
            };
            var coords = lin.Coordinates;
            if (coords.Length == 0) continue;
            if (pts.Count == 0)
                pts.AddRange(coords.Select(Copy));
            else
                pts.AddRange(coords.Skip(1).Select(Copy));
        }
        if (pts.Count < 2)
            return Gf.CreateLineString();
        return Gf.CreateLineString(pts.ToArray());
    }

    private static Geometry DensifyCurvePolygon(CurvePolygon cp, int samplesPerArc)
    {
        // Stroke-friendly: linearize exterior + holes to a Polygon when possible,
        // else return exterior ring as LineString for raster stroke.
        try
        {
            var exterior = Linearize(cp.ExteriorRing, samplesPerArc);
            if (exterior is not LineString shell || shell.NumPoints < 4)
                return exterior;

            var holes = new List<LinearRing>();
            for (int i = 0; i < cp.NumInteriorRings; i++)
            {
                var h = Linearize(cp.GetInteriorRingN(i), samplesPerArc);
                if (h is LineString ls && ls.NumPoints >= 4)
                    holes.Add(Gf.CreateLinearRing(ls.CoordinateSequence));
            }

            var shellRing = shell is LinearRing lr
                ? lr
                : Gf.CreateLinearRing(EnsureClosed(shell.Coordinates));
            return Gf.CreatePolygon(shellRing, holes.ToArray());
        }
        catch
        {
            return Linearize(cp.ExteriorRing, samplesPerArc);
        }
    }

    private static Coordinate[] EnsureClosed(Coordinate[] coords)
    {
        if (coords.Length == 0) return coords;
        if (coords[0].Equals2D(coords[^1])) return coords;
        var list = new List<Coordinate>(coords) { Copy(coords[0]) };
        return list.ToArray();
    }
#endif

    /// <summary>Sample circle arc a → c through on-arc point b.</summary>
    internal static Coordinate[] SampleArc(Coordinate a, Coordinate b, Coordinate c, int samples)
    {
        samples = Math.Clamp(samples, 4, 256);
        if (!TryCircleFrom3(a, b, c, out var cx, out var cy, out var r))
            return new[] { Copy(a), Copy(b), Copy(c) };

        double angA = Math.Atan2(a.Y - cy, a.X - cx);
        double angB = Math.Atan2(b.Y - cy, b.X - cx);
        double angC = Math.Atan2(c.Y - cy, c.X - cx);

        double ccwAC = NormalizePositive(angC - angA);
        double cwAC = NormalizePositive(angA - angC);
        double ccwAB = NormalizePositive(angB - angA);
        double ccwBC = NormalizePositive(angC - angB);
        double cwAB = NormalizePositive(angA - angB);
        double cwBC = NormalizePositive(angB - angC);
        double errCcw = Math.Abs((ccwAB + ccwBC) - ccwAC);
        double errCw = Math.Abs((cwAB + cwBC) - cwAC);
        double span = errCcw <= errCw ? ccwAC : -cwAC;

        var result = new Coordinate[samples + 1];
        for (int i = 0; i <= samples; i++)
        {
            double t = (double)i / samples;
            double ang = angA + span * t;
            result[i] = new Coordinate(cx + r * Math.Cos(ang), cy + r * Math.Sin(ang));
        }
        result[0] = Copy(a);
        result[^1] = Copy(c);
        return result;
    }

    internal static bool TryCircleFrom3(
        Coordinate a, Coordinate b, Coordinate c,
        out double cx, out double cy, out double r)
    {
        cx = cy = r = 0;
        double ax = a.X, ay = a.Y, bx = b.X, by = b.Y, x0 = c.X, y0 = c.Y;
        double d = 2 * (ax * (by - y0) + bx * (y0 - ay) + x0 * (ay - by));
        if (Math.Abs(d) < 1e-12) return false;

        double a2 = ax * ax + ay * ay;
        double b2 = bx * bx + by * by;
        double c2 = x0 * x0 + y0 * y0;
        cx = (a2 * (by - y0) + b2 * (y0 - ay) + c2 * (ay - by)) / d;
        cy = (a2 * (x0 - bx) + b2 * (ax - x0) + c2 * (bx - ax)) / d;
        double dx = ax - cx, dy = ay - cy;
        r = Math.Sqrt(dx * dx + dy * dy);
        return r > 1e-12;
    }

    private static double NormalizePositive(double ang)
    {
        double t = ang % (2 * Math.PI);
        if (t < 0) t += 2 * Math.PI;
        return t;
    }

    private static Coordinate Copy(Coordinate c) => new(c.X, c.Y);
}

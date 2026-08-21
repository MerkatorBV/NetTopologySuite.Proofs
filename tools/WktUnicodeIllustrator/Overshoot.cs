using NetTopologySuite.Geometries;
#if CURVE_NTS
using NetTopologySuite.Geometries.Curves;
#endif

namespace WktUnicodeIllustrator;

/// <summary>
/// Detects self-overlap / self-crossing ("overshoot") on lineal geometry —
/// the common case for a multi-arc <c>CIRCULARSTRING</c> that retraces or
/// crosses itself after linearization.
/// </summary>
internal static class Overshoot
{
    private static readonly GeometryFactory Gf = GeometryFactory.Default;

    /// <summary>
    /// Returns a (possibly multi) geometry of self-intersections: points where
    /// non-adjacent edges cross, and line pieces where non-adjacent edges collinearly
    /// overlap. Empty / null when the path is simple (no overshoot).
    /// </summary>
    public static Geometry? ExtractSelfOverlap(Geometry g, int samplesPerArc = 48)
    {
        if (g is null || g.IsEmpty) return null;

#if CURVE_NTS
        // CircularString reverse-retrace: (A, M, B, M, A) — second arc walks the first
        // backwards; treat the whole densified path as overshoot so maroon/navy
        // lights the entire self-overlap, not only floating multipoints.
        if (g is CircularString cs)
        {
            var retrace = ExtractCircularStringRetrace(cs, samplesPerArc);
            if (retrace is { IsEmpty: false })
                return retrace;
        }
#endif

        var lin = GeometryCurves.Linearize(g, samplesPerArc);
        return lin switch
        {
            LineString ls => ExtractFromLineString(ls),
            MultiLineString mls => ExtractFromMulti(mls),
            Polygon poly => ExtractFromLineString(poly.ExteriorRing),
            GeometryCollection gc => ExtractFromCollection(gc),
            _ => null,
        };
    }

#if CURVE_NTS
    /// <summary>
    /// Detect arcs that reverse an earlier arc (shared mid control, swapped ends).
    /// Returns densified union of those reverse arcs (the overshooting retrace).
    /// </summary>
    private static Geometry? ExtractCircularStringRetrace(CircularString cs, int samplesPerArc)
    {
        var seq = cs.CoordinateSequence;
        int n = seq.Count;
        if (n < 5) return null;

        var parts = new List<Geometry>();
        // Arc k uses controls (2k, 2k+1, 2k+2).
        int numArcs = (n - 1) / 2;
        for (int i = 0; i < numArcs; i++)
        {
            var a0 = seq.GetCoordinate(2 * i);
            var a1 = seq.GetCoordinate(2 * i + 1);
            var a2 = seq.GetCoordinate(2 * i + 2);
            for (int j = i + 1; j < numArcs; j++)
            {
                var b0 = seq.GetCoordinate(2 * j);
                var b1 = seq.GetCoordinate(2 * j + 1);
                var b2 = seq.GetCoordinate(2 * j + 2);
                // Reverse retrace: same mid, ends swapped.
                bool reverse = a1.Equals2D(b1) && a0.Equals2D(b2) && a2.Equals2D(b0);
                // Same-direction duplicate arc (identical controls).
                bool same = a0.Equals2D(b0) && a1.Equals2D(b1) && a2.Equals2D(b2);
                if (!reverse && !same) continue;

                var dense = GeometryCurves.SampleArc(b0, b1, b2, samplesPerArc);
                if (dense.Length >= 2)
                    parts.Add(Gf.CreateLineString(dense));
            }
        }

        return Combine(parts);
    }
#endif

    public static bool HasOvershoot(Geometry g) =>
        ExtractSelfOverlap(g) is { IsEmpty: false };

    /// <summary>
    /// Node a (possibly non-simple) lineal geometry so OverlayNG can consume it.
    /// Self-overlapping densified circular strings are unioned edge-wise.
    /// </summary>
    public static Geometry PrepareForOverlay(Geometry g)
    {
        if (g is null || g.IsEmpty) return g;
        try
        {
            if (g is LineString ls)
            {
                if (ls.IsSimple) return ls;
                return NodeLineString(ls);
            }
            if (g is MultiLineString or GeometryCollection)
                return g.Union();
            return g;
        }
        catch
        {
            return g;
        }
    }

    private static Geometry NodeLineString(LineString ls)
    {
        var coords = ls.Coordinates;
        var segs = new List<Geometry>();
        for (int i = 0; i < coords.Length - 1; i++)
        {
            if (coords[i].Equals2D(coords[i + 1])) continue;
            segs.Add(Gf.CreateLineString(new[] { Copy(coords[i]), Copy(coords[i + 1]) }));
        }
        if (segs.Count == 0) return ls;
        return Gf.BuildGeometry(segs).Union();
    }

    private static Geometry? ExtractFromMulti(MultiLineString mls)
    {
        var parts = new List<Geometry>();
        for (int i = 0; i < mls.NumGeometries; i++)
        {
            var p = ExtractFromLineString((LineString)mls.GetGeometryN(i));
            if (p is { IsEmpty: false }) parts.Add(p);
        }
        // Also inter-component intersections (optional overshoot between parts).
        for (int i = 0; i < mls.NumGeometries; i++)
        {
            for (int j = i + 1; j < mls.NumGeometries; j++)
            {
                var ix = mls.GetGeometryN(i).Intersection(mls.GetGeometryN(j));
                if (!ix.IsEmpty) parts.Add(ix);
            }
        }
        return Combine(parts);
    }

    private static Geometry? ExtractFromCollection(GeometryCollection gc)
    {
        var parts = new List<Geometry>();
        for (int i = 0; i < gc.NumGeometries; i++)
        {
            var p = ExtractSelfOverlap(gc.GetGeometryN(i));
            if (p is { IsEmpty: false }) parts.Add(p);
        }
        return Combine(parts);
    }

    private static Geometry? ExtractFromLineString(LineString ls)
    {
        var coords = ls.Coordinates;
        if (coords.Length < 4) return null;

        // Drop closing vertex duplicate for pair enumeration (still allow
        // first/last segment pairs to interact as non-adjacent).
        int nSeg = coords.Length - 1;
        bool closed = ls.IsClosed && coords.Length >= 4;

        var parts = new List<Geometry>();
        for (int i = 0; i < nSeg; i++)
        {
            if (coords[i].Equals2D(coords[i + 1])) continue;
            var segI = Gf.CreateLineString(new[] { Copy(coords[i]), Copy(coords[i + 1]) });

            for (int j = i + 2; j < nSeg; j++)
            {
                // Closed ring: first and last segments share the closure vertex only —
                // skip that adjacency (i==0, j==nSeg-1).
                if (closed && i == 0 && j == nSeg - 1) continue;
                if (coords[j].Equals2D(coords[j + 1])) continue;

                var segJ = Gf.CreateLineString(new[] { Copy(coords[j]), Copy(coords[j + 1]) });
                Geometry ix;
                try
                {
                    ix = segI.Intersection(segJ);
                }
                catch
                {
                    continue;
                }

                if (ix.IsEmpty) continue;

                // Drop pure shared-vertex touches that are only consecutive in the
                // densified chain (already excluded by j>=i+2), keep crossings & overlaps.
                if (ix is Point pt)
                {
                    // Ignore if the only contact is an endpoint-to-endpoint joint
                    // between nearly consecutive densify samples (j == i+2 and
                    // point equals the shared middle vertex of the polyline).
                    if (j == i + 2 && IsEndpointJoint(pt.Coordinate, coords, i, j))
                        continue;
                }

                parts.Add(ix);
            }
        }

        return Combine(parts);
    }

    private static bool IsEndpointJoint(Coordinate p, Coordinate[] coords, int i, int j)
    {
        // Segments (i,i+1) and (j,j+1) with j=i+2: joint vertex is coords[i+1] == coords[j]
        // only if densify didn't insert a gap — typically not equal. If intersection
        // equals coords[i+1] or coords[j], treat as chain joint.
        return p.Equals2D(coords[i + 1]) || p.Equals2D(coords[j]);
    }

    private static Geometry? Combine(List<Geometry> parts)
    {
        if (parts.Count == 0) return null;
        try
        {
            var u = Gf.BuildGeometry(parts).Union();
            return u.IsEmpty ? null : u;
        }
        catch
        {
            return Gf.BuildGeometry(parts);
        }
    }

    private static Coordinate Copy(Coordinate c) => new(c.X, c.Y);
}

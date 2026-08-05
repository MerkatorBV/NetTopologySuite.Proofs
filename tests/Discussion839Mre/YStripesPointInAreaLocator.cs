// ============================================================================
// Faithful C# port of JTS PR #1145 YStripes point-in-area locator (micycle1).
// Source tip: micycle1/jts branch ystripes —
//   YStripesPointInPolygonLocator / YStripesPointInAreaLocator
// Used only for corpus gallery differential; not a production NTS API.
// ============================================================================

using NetTopologySuite.Algorithm;
using NetTopologySuite.Geometries;
using NetTopologySuite.Index.Strtree;

namespace Discussion839Mre;

/// <summary>
/// Point-in-area locator mirroring JTS <c>YStripesPointInAreaLocator</c> (#1145).
/// </summary>
public sealed class YStripesPointInAreaLocator : IPointInAreaLocator
{
    private readonly Envelope? _env;
    private readonly IPointInAreaLocator? _single;
    private readonly STRtree<object>? _tree;
    private readonly Envelope _qEnv = new();

    public YStripesPointInAreaLocator(Geometry geom)
    {
        var polys = new List<Polygon>();
        CollectPolygons(geom, polys);

        if (polys.Count == 0)
        {
            _env = geom.EnvelopeInternal.Copy();
            _single = null;
            _tree = null;
            return;
        }

        if (polys.Count == 1)
        {
            _single = new YStripesPointInPolygonLocator(polys[0]);
            _env = null;
            _tree = null;
            return;
        }

        var e = new Envelope();
        var t = new STRtree<object>();
        foreach (var p in polys)
        {
            var pe = p.EnvelopeInternal;
            e.ExpandToInclude(pe);
            t.Insert(pe, new YStripesPointInPolygonLocator(p));
        }
        t.Build();

        _env = e;
        _single = null;
        _tree = t;
    }

    public Location Locate(Coordinate p)
    {
        double x = p.X, y = p.Y;

        if (_single == null && _tree == null)
            return Location.Exterior;

        if (_single != null)
            return _single.Locate(p);

        if (_env is null || !_env.Contains(x, y))
            return Location.Exterior;

        _qEnv.Init(p);
        var cands = _tree!.Query(_qEnv);
        if (cands.Count == 0)
            return Location.Exterior;

        bool onBoundary = false;
        foreach (var item in cands)
        {
            var loc = ((IPointInAreaLocator)item).Locate(p);
            if (loc == Location.Interior)
                return Location.Interior;
            if (loc == Location.Boundary)
                onBoundary = true;
        }
        return onBoundary ? Location.Boundary : Location.Exterior;
    }

    private static void CollectPolygons(Geometry g, List<Polygon> outList)
    {
        if (g is Polygon poly)
        {
            if (!poly.IsEmpty)
                outList.Add(poly);
            return;
        }
        if (g is GeometryCollection gc)
        {
            for (int i = 0; i < gc.NumGeometries; i++)
                CollectPolygons(gc.GetGeometryN(i), outList);
        }
    }
}

/// <summary>
/// Per-polygon Y-stripe index + ray-crossing (JTS package-private class port).
/// </summary>
internal sealed class YStripesPointInPolygonLocator : IPointInAreaLocator
{
    private readonly RingIndex _shell;
    private readonly RingIndex[] _holes;

    public YStripesPointInPolygonLocator(Polygon polygon)
    {
        ArgumentNullException.ThrowIfNull(polygon);
        _shell = RingIndex.Build((LinearRing)polygon.ExteriorRing);
        _holes = new RingIndex[polygon.NumInteriorRings];
        for (int i = 0; i < _holes.Length; i++)
            _holes[i] = RingIndex.Build((LinearRing)polygon.GetInteriorRingN(i));
    }

    public Location Locate(Coordinate p)
    {
        double x = p.X, y = p.Y;
        if (!_shell.CoversPointFast(x, y))
            return Location.Exterior;

        var loc = _shell.LocateYStripes(x, y);
        if (loc != Location.Interior)
            return loc;

        foreach (var hole in _holes)
        {
            if (!hole.CoversPointFast(x, y))
                continue;
            var hLoc = hole.LocateYStripes(x, y);
            if (hLoc == Location.Boundary)
                return Location.Boundary;
            if (hLoc == Location.Interior)
                return Location.Exterior; // inside a hole
        }
        return Location.Interior;
    }

    private sealed class RingIndex
    {
        private readonly double[] _xs, _ys;
        private readonly double[] _segXMin, _segXMax, _segYMin, _segYMax;
        private readonly double _minX, _minY, _maxX, _maxY, _height, _invH;
        private readonly int _nStripes;
        private readonly int[] _stripeOffsets;
        private readonly int[] _stripeCounts;
        private readonly int[] _segIndex;

        private RingIndex(
            double[] xs, double[] ys,
            double[] segXMin, double[] segXMax, double[] segYMin, double[] segYMax,
            double minX, double minY, double maxX, double maxY,
            int nStripes, int[] stripeOffsets, int[] stripeCounts, int[] segIndex)
        {
            _xs = xs;
            _ys = ys;
            _segXMin = segXMin;
            _segXMax = segXMax;
            _segYMin = segYMin;
            _segYMax = segYMax;
            _minX = minX;
            _minY = minY;
            _maxX = maxX;
            _maxY = maxY;
            _height = maxY - minY;
            _invH = _height == 0 ? 0.0 : 1.0 / _height;
            _nStripes = nStripes;
            _stripeOffsets = stripeOffsets;
            _stripeCounts = stripeCounts;
            _segIndex = segIndex;
        }

        public static RingIndex Build(LinearRing ring)
        {
            var seq = ring.CoordinateSequence;
            int n = seq.Count;
            if (n < 2)
                throw new ArgumentException("Ring has < 2 points");

            var xs = new double[n];
            var ys = new double[n];
            double minX = double.PositiveInfinity, minY = double.PositiveInfinity;
            double maxX = double.NegativeInfinity, maxY = double.NegativeInfinity;

            for (int i = 0; i < n; i++)
            {
                double x = seq.GetX(i), y = seq.GetY(i);
                xs[i] = x;
                ys[i] = y;
                if (x < minX) minX = x;
                if (x > maxX) maxX = x;
                if (y < minY) minY = y;
                if (y > maxY) maxY = y;
            }

            int nSegs = n - 1;
            var segXMin = new double[nSegs];
            var segXMax = new double[nSegs];
            var segYMin = new double[nSegs];
            var segYMax = new double[nSegs];

            double perim = 0.0;
            double area2 = 0.0;
            for (int i = 0; i < nSegs; i++)
            {
                double ax = xs[i], ay = ys[i];
                double bx = xs[i + 1], by = ys[i + 1];
                segXMin[i] = ax < bx ? ax : bx;
                segXMax[i] = ax > bx ? ax : bx;
                segYMin[i] = ay < by ? ay : by;
                segYMax[i] = ay > by ? ay : by;
                double dx = bx - ax, dy = by - ay;
                perim += Math.Sqrt(dx * dx + dy * dy);
                area2 += ax * by - bx * ay;
            }
            double area = Math.Abs(0.5 * area2);

            int basen = Math.Max(64, Math.Min(nSegs, 65_536));
            double score = perim > 0 ? (area * Math.PI * 4.0) / (perim * perim) : 1.0;
            double boost = Math.Max(0.35, Math.Min(1.0, score * 1.5));
            int nStripes = maxY == minY ? 1 : Math.Max(1, (int)Math.Round(basen * boost));

            if (nStripes == 1)
            {
                var offsets = new[] { 0 };
                var counts = new[] { nSegs };
                var idx = new int[nSegs];
                for (int i = 0; i < nSegs; i++) idx[i] = i;
                return new RingIndex(xs, ys, segXMin, segXMax, segYMin, segYMax,
                    minX, minY, maxX, maxY, 1, offsets, counts, idx);
            }

            double scale = nStripes / (maxY - minY);
            var countsTmp = new int[nStripes];
            int nMap = 0;
            for (int i = 0; i < nSegs; i++)
            {
                int smin = (int)((segYMin[i] - minY) * scale);
                int smax = (int)((segYMax[i] - minY) * scale);
                if (smax >= nStripes) smax = nStripes - 1;
                if (smin < 0) smin = 0;
                if (smin > smax) smin = smax;
                for (int s = smin; s <= smax; s++)
                {
                    countsTmp[s]++;
                    nMap++;
                }
            }

            var stripeOffsets = new int[nStripes];
            var stripeCounts = new int[nStripes];
            int run = 0;
            for (int s = 0; s < nStripes; s++)
            {
                stripeOffsets[s] = run;
                run += countsTmp[s];
            }
            var segIndex = new int[nMap];

            for (int i = 0; i < nSegs; i++)
            {
                int smin = (int)((segYMin[i] - minY) * scale);
                int smax = (int)((segYMax[i] - minY) * scale);
                if (smax >= nStripes) smax = nStripes - 1;
                if (smin < 0) smin = 0;
                if (smin > smax) smin = smax;
                for (int s = smin; s <= smax; s++)
                {
                    int pos = stripeOffsets[s] + stripeCounts[s]++;
                    segIndex[pos] = i;
                }
            }

            return new RingIndex(xs, ys, segXMin, segXMax, segYMin, segYMax,
                minX, minY, maxX, maxY, nStripes, stripeOffsets, stripeCounts, segIndex);
        }

        public bool CoversPointFast(double x, double y) =>
            !(y < _minY || y > _maxY || x < _minX || x > _maxX);

        public Location LocateYStripes(double px, double py)
        {
            bool inside = false;
            int onIdx = -1;

            int s;
            if (_nStripes == 1 || _height == 0)
                s = 0;
            else
            {
                s = (int)(((py - _minY) * _invH) * _nStripes);
                if (s < 0) s = 0;
                else if (s >= _nStripes) s = _nStripes - 1;
            }

            int bas = _stripeOffsets[s];
            int cnt = _stripeCounts[s];
            int end = bas + cnt;

            for (int p = bas; p < end; p++)
            {
                int i = _segIndex[p];
                double ymin = _segYMin[i], ymax = _segYMax[i];
                if (py < ymin || py > ymax)
                    continue;

                double ax = _xs[i], ay = _ys[i];
                double bx = _xs[i + 1], by = _ys[i + 1];
                double xmin = _segXMin[i], xmax = _segXMax[i];

                // Horizontal edges: boundary only; never counted for crossings
                if (ay == by)
                {
                    if (py == ay && px >= xmin && px <= xmax)
                    {
                        onIdx = i;
                        break;
                    }
                    continue;
                }

                // Entire segment strictly to the right: guaranteed crossing if straddle
                if (px < xmin)
                {
                    if ((ay > py) != (by > py))
                        inside = !inside;
                    continue;
                }

                // Entire segment strictly to the left
                if (px > xmax)
                    continue;

                int rc = Raycast(ax, ay, bx, by, px, py, xmin, xmax, ymin, ymax);
                if (rc == RcOn)
                {
                    onIdx = i;
                    break;
                }
                if (rc == RcIn)
                    inside = !inside;
            }

            if (onIdx != -1)
                return Location.Boundary;
            return inside ? Location.Interior : Location.Exterior;
        }

        private const int RcOut = 0;
        private const int RcIn = 1;
        private const int RcOn = 2;

        private static int Raycast(
            double ax, double ay, double bx, double by,
            double px, double py,
            double minx, double maxx, double miny, double maxy)
        {
            if ((px == ax && py == ay) || (px == bx && py == by))
                return RcOn;
            if (ay == by)
            {
                if (py == ay && px >= minx && px <= maxx)
                    return RcOn;
                return RcOut;
            }
            // Half-open straddle
            if (!((ay > py) != (by > py)))
                return RcOut;

            int orient = CGAlgorithmsDD.OrientationIndex(ax, ay, bx, by, px, py);
            if (orient == 0)
            {
                if (px >= minx && px <= maxx && py >= miny && py <= maxy)
                    return RcOn;
                return RcOut;
            }
            if (by < ay)
                orient = -orient;
            return orient > 0 ? RcIn : RcOut;
        }
    }
}

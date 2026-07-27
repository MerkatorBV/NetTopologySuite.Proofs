// ============================================================================
// oracle/csharp/RocqNative.cs
// ----------------------------------------------------------------------------
// Phase 5 reference binding: the .NET side of `libntsrocq` (oracle/nts_ffi.h).
//
// This file is REFERENCE SOURCE, not a compiled artifact of this repository --
// there is no .NET toolchain in the proofs CI (same status as
// docs/arc-offset-red-test-example.cs).  It is the copy-in starting point for
// `NetTopologySuite.Robust.Native` in the NetTopologySuite.Curve consumer,
// and it is the executable form of the ABI contract: if this file and
// oracle/nts_ffi.h disagree, one of them is wrong.
//
// What it buys over the existing RocqRefRunner: RocqRefRunner shells out to
// `oracle_bin` and speaks a line protocol -- one process spawn plus two pipe
// round-trips per predicate call.  That is fine for differential test corpora
// (which is all it was ever used for) and hopeless inside a noding loop.  These
// entry points are ordinary p/invoke calls into the same extracted code.
//
// Threading: the embedded OCaml 4.14 runtime is not re-entrant, so every call
// is serialised on `Gate`.  Callers that need parallelism should partition work
// and batch, not remove the lock.
//
// AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
// ============================================================================

using System;
using System.Runtime.InteropServices;

namespace NetTopologySuite.Robust.Native
{
    /// <summary>5-valued orientation result (Phase 0, b64_orient_sign_filtered).</summary>
    public enum RocqOrientSign
    {
        /// <summary>Clockwise / right turn.</summary>
        Neg = -1,

        /// <summary>Collinear.</summary>
        Zero = 0,

        /// <summary>Counter-clockwise / left turn.</summary>
        Pos = 1,

        /// <summary>A NaN reached the predicate.</summary>
        Nan = 2,

        /// <summary>The Shewchuk Stage A filter declines to answer. Never a wrong
        /// sign: escalate to an exact path rather than treating it as Zero.</summary>
        Uncertain = 3
    }

    /// <summary>5-valued segment-intersection result (Phase 1).</summary>
    public enum RocqIntersectSign
    {
        None = 0,
        Point = 1,
        Collinear = 2,
        Nan = 3,
        Uncertain = 4
    }

    /// <summary>Overlay boolean operation (Phase 3, OverlayGraph.v order).</summary>
    public enum RocqBooleanOp
    {
        Union = 0,
        Intersection = 1,
        Difference = 2,
        SymDiff = 3
    }

    internal static class RocqNativeMethods
    {
        // Resolves to libntsrocq.so / libntsrocq.dylib / ntsrocq.dll.
        private const string Lib = "ntsrocq";

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_init();

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_abi_version();

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_orient_sign_filtered(
            double p0x, double p0y, double p1x, double p1y, double qx, double qy);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_orient_sign_naive(
            double p0x, double p0y, double p1x, double p1y, double qx, double qy);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern double nts_rocq_orient2d(
            double p0x, double p0y, double p1x, double p1y, double qx, double qy);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_intersect_sign_filtered(
            double p0x, double p0y, double p1x, double p1y,
            double q0x, double q0y, double q1x, double q1y);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_intersect_point(
            double p0x, double p0y, double p1x, double p1y,
            double q0x, double q0y, double q1x, double q1y,
            out double x, out double y);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern void nts_rocq_intersect_point_xy(
            double p0x, double p0y, double p1x, double p1y,
            double q0x, double q0y, double q1x, double q1y,
            out double x, out double y);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_passes_through_hot_pixel(
            double p0x, double p0y, double p1x, double p1y, double cx, double cy);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_passes_through_hot_pixel_halfopen(
            double p0x, double p0y, double p1x, double p1y, double cx, double cy);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern double nts_rocq_snap_coord(double x);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern double nts_rocq_snap_coord_scaled(double x, double scale);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_edge_in_result(int op, int inLeft, int inRight);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern double nts_rocq_in_circle(
            double ax, double ay, double bx, double by,
            double cx, double cy, double px, double py);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_chord_crosses_arc_circle(
            double sx, double sy, double mx, double my, double ex, double ey,
            double px, double py, double qx, double qy);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern void nts_rocq_arc_line_intersect_xy(
            double sx, double sy, double mx, double my, double ex, double ey,
            double px, double py, double qx, double qy,
            out double x, out double y);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_arc_passes_through_hot_pixel(
            double sx, double sy, double mx, double my, double ex, double ey,
            double cx, double cy, double scale);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern void nts_rocq_two_sum(
            double x, double y, out double sum, out double err);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_grow_expansion(
            double q, double[] xs, int n, double[] outH, int outCap, out double qFinal);

        [DllImport(Lib, CallingConvention = CallingConvention.Cdecl)]
        internal static extern int nts_rocq_simplify_perp(
            double eps, double[] xy, int nPts, double[] outXy, int outCap);
    }

    /// <summary>
    /// Managed façade over the Coq-extracted geometry kernel.  Every method here
    /// returns exactly what the proofs-repo oracle returns for the same inputs
    /// (gated by oracle/gen_ffi_parity_tests.py on every build of the proofs).
    /// </summary>
    public static class RocqNative
    {
        /// <summary>ABI this binding was written against (see nts_ffi.h).</summary>
        public const int ExpectedAbiVersion = 1;

        private static readonly object Gate = new object();

        static RocqNative()
        {
            RocqNativeMethods.nts_rocq_init();

            int abi = RocqNativeMethods.nts_rocq_abi_version();
            if (abi != ExpectedAbiVersion)
            {
                throw new InvalidOperationException(
                    $"libntsrocq ABI {abi} does not match the expected {ExpectedAbiVersion}. " +
                    "Rebuild the native library from the matching NetTopologySuite.Proofs commit.");
            }
        }

        // ---- Phase 0: orientation ------------------------------------------

        /// <summary>Shewchuk Stage A filtered orientation of (p0, p1, q).</summary>
        public static RocqOrientSign OrientSignFiltered(
            double p0x, double p0y, double p1x, double p1y, double qx, double qy)
        {
            lock (Gate)
            {
                return (RocqOrientSign)RocqNativeMethods.nts_rocq_orient_sign_filtered(
                    p0x, p0y, p1x, p1y, qx, qy);
            }
        }

        /// <summary>Unfiltered sign of the raw determinant. NOT robust; for
        /// differential testing against the filtered predicate.</summary>
        public static RocqOrientSign OrientSignNaive(
            double p0x, double p0y, double p1x, double p1y, double qx, double qy)
        {
            lock (Gate)
            {
                return (RocqOrientSign)RocqNativeMethods.nts_rocq_orient_sign_naive(
                    p0x, p0y, p1x, p1y, qx, qy);
            }
        }

        /// <summary>The raw binary64 orientation determinant.</summary>
        public static double Orient2D(
            double p0x, double p0y, double p1x, double p1y, double qx, double qy)
        {
            lock (Gate)
            {
                return RocqNativeMethods.nts_rocq_orient2d(p0x, p0y, p1x, p1y, qx, qy);
            }
        }

        // ---- Phase 1: segment intersection ---------------------------------

        public static RocqIntersectSign IntersectSignFiltered(
            double p0x, double p0y, double p1x, double p1y,
            double q0x, double q0y, double q1x, double q1y)
        {
            lock (Gate)
            {
                return (RocqIntersectSign)RocqNativeMethods.nts_rocq_intersect_sign_filtered(
                    p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y);
            }
        }

        /// <summary>Option-wrapped intersection point; false leaves x/y NaN.</summary>
        public static bool TryIntersectPoint(
            double p0x, double p0y, double p1x, double p1y,
            double q0x, double q0y, double q1x, double q1y,
            out double x, out double y)
        {
            lock (Gate)
            {
                return RocqNativeMethods.nts_rocq_intersect_point(
                    p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y, out x, out y) == 1;
            }
        }

        /// <summary>Total coordinate projections, computed unconditionally.</summary>
        public static void IntersectPointXy(
            double p0x, double p0y, double p1x, double p1y,
            double q0x, double q0y, double q1x, double q1y,
            out double x, out double y)
        {
            lock (Gate)
            {
                RocqNativeMethods.nts_rocq_intersect_point_xy(
                    p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y, out x, out y);
            }
        }

        // ---- Phase 2: snap rounding ----------------------------------------

        public static bool PassesThroughHotPixel(
            double p0x, double p0y, double p1x, double p1y, double cx, double cy)
        {
            lock (Gate)
            {
                return RocqNativeMethods.nts_rocq_passes_through_hot_pixel(
                    p0x, p0y, p1x, p1y, cx, cy) == 1;
            }
        }

        public static bool PassesThroughHotPixelHalfOpen(
            double p0x, double p0y, double p1x, double p1y, double cx, double cy)
        {
            lock (Gate)
            {
                return RocqNativeMethods.nts_rocq_passes_through_hot_pixel_halfopen(
                    p0x, p0y, p1x, p1y, cx, cy) == 1;
            }
        }

        /// <summary>Round half to even onto the unit grid.</summary>
        public static double SnapCoord(double x)
        {
            lock (Gate)
            {
                return RocqNativeMethods.nts_rocq_snap_coord(x);
            }
        }

        /// <summary>Snap onto a power-of-two grid (value first, scale second --
        /// the Coq argument order).</summary>
        public static double SnapCoordScaled(double x, double scale)
        {
            lock (Gate)
            {
                return RocqNativeMethods.nts_rocq_snap_coord_scaled(x, scale);
            }
        }

        // ---- Phase 3: overlay labelling ------------------------------------

        public static bool EdgeInResult(RocqBooleanOp op, bool inLeft, bool inRight)
        {
            lock (Gate)
            {
                int r = RocqNativeMethods.nts_rocq_edge_in_result(
                    (int)op, inLeft ? 1 : 0, inRight ? 1 : 0);
                if (r < 0)
                {
                    throw new ArgumentOutOfRangeException(nameof(op));
                }
                return r == 1;
            }
        }

        // ---- Phase 4: circular arcs ----------------------------------------

        /// <summary>In-circle determinant: positive iff (a,b,c) is CCW and p is
        /// strictly inside its circumcircle.</summary>
        public static double InCircle(
            double ax, double ay, double bx, double by,
            double cx, double cy, double px, double py)
        {
            lock (Gate)
            {
                return RocqNativeMethods.nts_rocq_in_circle(ax, ay, bx, by, cx, cy, px, py);
            }
        }

        /// <summary>SUFFICIENT condition only: true =&gt; the chord crosses the
        /// arc's circumcircle. False is inconclusive.</summary>
        public static bool ChordCrossesArcCircle(
            double sx, double sy, double mx, double my, double ex, double ey,
            double px, double py, double qx, double qy)
        {
            lock (Gate)
            {
                return RocqNativeMethods.nts_rocq_chord_crosses_arc_circle(
                    sx, sy, mx, my, ex, ey, px, py, qx, qy) == 1;
            }
        }

        /// <summary>Single-root Cramer projection; emits infinity/NaN on a
        /// two-crossing line. Not an enumerator.</summary>
        public static void ArcLineIntersectXy(
            double sx, double sy, double mx, double my, double ex, double ey,
            double px, double py, double qx, double qy,
            out double x, out double y)
        {
            lock (Gate)
            {
                RocqNativeMethods.nts_rocq_arc_line_intersect_xy(
                    sx, sy, mx, my, ex, ey, px, py, qx, qy, out x, out y);
            }
        }

        /// <summary>SUFFICIENT condition only: true =&gt; the arc passes through
        /// the hot pixel. False is inconclusive.</summary>
        public static bool ArcPassesThroughHotPixel(
            double sx, double sy, double mx, double my, double ex, double ey,
            double cx, double cy, double scale)
        {
            lock (Gate)
            {
                return RocqNativeMethods.nts_rocq_arc_passes_through_hot_pixel(
                    sx, sy, mx, my, ex, ey, cx, cy, scale) == 1;
            }
        }

        // ---- Stage D building blocks ---------------------------------------

        /// <summary>Error-free transformation: sum + err == x + y exactly.</summary>
        public static void TwoSum(double x, double y, out double sum, out double err)
        {
            lock (Gate)
            {
                RocqNativeMethods.nts_rocq_two_sum(x, y, out sum, out err);
            }
        }

        /// <summary>Grows an expansion by one component; returns the settled
        /// components and the running carry.</summary>
        public static double[] GrowExpansion(double q, double[] xs, out double qFinal)
        {
            if (xs == null)
            {
                throw new ArgumentNullException(nameof(xs));
            }

            var outH = new double[xs.Length];
            int k;
            lock (Gate)
            {
                k = RocqNativeMethods.nts_rocq_grow_expansion(
                    q, xs, xs.Length, outH, outH.Length, out qFinal);
            }
            if (k < 0)
            {
                throw new InvalidOperationException("nts_rocq_grow_expansion failed");
            }

            var result = new double[k];
            Array.Copy(outH, result, k);
            return result;
        }

        // ---- Simplifier ------------------------------------------------------

        /// <summary>Greedy perpendicular-distance simplifier. Input and output are
        /// flat (x, y) pairs.</summary>
        public static double[] SimplifyPerp(double eps, double[] xy)
        {
            if (xy == null)
            {
                throw new ArgumentNullException(nameof(xy));
            }
            if ((xy.Length & 1) != 0)
            {
                throw new ArgumentException("expected flat (x, y) pairs", nameof(xy));
            }

            int nPts = xy.Length / 2;
            var outXy = new double[xy.Length];
            int k;
            lock (Gate)
            {
                k = RocqNativeMethods.nts_rocq_simplify_perp(eps, xy, nPts, outXy, nPts);
            }
            if (k < 0)
            {
                throw new InvalidOperationException("nts_rocq_simplify_perp failed");
            }

            var result = new double[2 * k];
            Array.Copy(outXy, result, 2 * k);
            return result;
        }
    }
}

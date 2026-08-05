// ============================================================================
// Discussion #839 MRE harness — ConformingDelaunay + concave filter + Rocq oracle
// ----------------------------------------------------------------------------
// Replays NetTopologySuite/NetTopologySuite#discussion-839 and checks local
// Delaunay legality of every internal edge via the proofs-repo oracle kernel
// (oracle_bin INCIRCLE_SIGN == extracted b64_inCircle, same code as
// nts_rocq_in_circle / Phase 5 FFI).
//
// Oracle path (default): WSL oracle_bin at
//   ~/nettopologysuite.proofs/oracle/oracle_bin
// Override with env ORACLE_BIN (Windows path) or WSL_ORACLE_BIN (WSL path).
//
// AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
// ============================================================================

using System.Diagnostics;
using System.Globalization;
using System.Text;
using NetTopologySuite.Algorithm;
using NetTopologySuite.Algorithm.Locate;
using NetTopologySuite.Geometries;
using NetTopologySuite.Triangulate;

static class Program
{
    private const double Scale = 1e5;

    // Raw sites from NTS discussion #839 (closed ring; first == last).
    private static readonly (double X, double Y)[] RawSites =
    {
        (24.395231, 3.3126805),
        (22.195227, 3.3126805),
        (22.195227, -3.6873195),
        (21.695227, -3.6873195),
        (21.695227, -10.657321),
        (20.205229, -12.237323),
        (-10.304773, -13.827319),
        (-10.304773, -18.327318),
        (-27.50477, -21.057314),
        (-27.50477, -9.257312),
        (-26.634775, -7.897311),
        (-23.00477, -6.207324),
        (-23.00477, 4.292676),
        (-6.0047703, 4.292676),
        (-6.0047703, 6.292676),
        (-17.00477, 6.292676),
        (-17.00477, 13.292676),
        (12.99523, 16.972685),
        (12.99523, 20.832685),
        (21.265226, 22.292677),
        (22.265226, 22.292677),
        (24.395231, 14.31268),
        (24.395231, 3.3126805),
    };

    public static int Main(string[] args)
    {
        CultureInfo.DefaultThreadCurrentCulture = CultureInfo.InvariantCulture;
        CultureInfo.DefaultThreadCurrentUICulture = CultureInfo.InvariantCulture;

        bool useScaled = !args.Contains("--no-scale", StringComparer.OrdinalIgnoreCase);
        double tolerance = args.Contains("--tol0", StringComparer.OrdinalIgnoreCase) ? 0.0 : 0.1;

        Console.WriteLine("=== NTS discussion #839 MRE + Rocq INCIRCLE oracle ===");
        Console.WriteLine($"NTS: {typeof(Geometry).Assembly.GetName().Version}");
        Console.WriteLine($"Scale applied: {useScaled} (SCALE={Scale})");
        Console.WriteLine($"Builder.Tolerance: {tolerance}");
        Console.WriteLine();

        // Sanity: oracle flip witness from DelaunayLocallyDelaunay.loc_D
        // A=(0,0) B=(2,0) C=(1,1) D=(1,-1/2) ⇒ inCircle = +3/2
        if (!TryOracleInCircle(0, 0, 2, 0, 1, 1, 1, -0.5, out var pinSign, out var pinVal, out var pinErr))
        {
            Console.Error.WriteLine($"FATAL: Rocq oracle unavailable: {pinErr}");
            Console.Error.WriteLine("Set WSL_ORACLE_BIN or ORACLE_BIN, or ensure WSL has");
            Console.Error.WriteLine("  ~/nettopologysuite.proofs/oracle/oracle_bin");
            return 2;
        }
        Console.WriteLine($"Oracle pin (flip witness A B C D): {pinSign} {pinVal:R}");
        if (pinSign != "POS" || Math.Abs(pinVal - 1.5) > 1e-12)
        {
            Console.Error.WriteLine("FATAL: oracle pin failed (expected POS 1.5)");
            return 2;
        }
        Console.WriteLine("Oracle pin OK (matches DelaunayLocallyDelaunay.loc_in_circle_test_D).");
        Console.WriteLine();

        var pm = new PrecisionModel(PrecisionModel.MaximumPreciseValue);
        var gf = new GeometryFactory(pm, 0);

        var coordinates = RawSites
            .Select(p => useScaled
                ? new Coordinate(Math.Round(p.X * Scale, 0), Math.Round(p.Y * Scale, 0))
                : new Coordinate(p.X, p.Y))
            .Distinct()
            .ToList();

        var coPoly = coordinates.ToList();
        if (!coPoly[0].Equals2D(coPoly[^1]))
            coPoly.Add(new Coordinate(coPoly[0]));

        var polygon = gf.CreatePolygon(coPoly.ToArray());
        Console.WriteLine($"Polygon.IsValid: {polygon.IsValid}");
        Console.WriteLine($"Polygon.NumPoints: {polygon.NumPoints}");
        Console.WriteLine($"Polygon.Area: {polygon.Area:R}");
        Console.WriteLine($"Shell CCW: {Orientation.IsCCW(polygon.ExteriorRing.CoordinateSequence)}");
        Console.WriteLine($"Envelope: {polygon.EnvelopeInternal}");
        Console.WriteLine();

        var builder = new ConformingDelaunayTriangulationBuilder
        {
            Tolerance = tolerance,
            Constraints = polygon
        };
        builder.SetSites(polygon);

        GeometryCollection triangulation = builder.GetTriangles(gf);
        var triangles = triangulation.OfType<Polygon>().ToList();
        Console.WriteLine($"Total triangles: {triangles.Count}");

        var locator = new IndexedPointInAreaLocator(polygon);
        var byLocation = triangles
            .Select(t =>
            {
                var c = t.Centroid.Coordinate;
                var loc = locator.Locate(c);
                return (T: t, C: c, Loc: loc);
            })
            .ToList();

        int nInt = byLocation.Count(x => x.Loc == Location.Interior);
        int nBnd = byLocation.Count(x => x.Loc == Location.Boundary);
        int nExt = byLocation.Count(x => x.Loc == Location.Exterior);
        Console.WriteLine($"Centroid filter: Interior={nInt} Boundary={nBnd} Exterior={nExt}");
        Console.WriteLine($"Reporter filter (Interior only): {nInt}");
        Console.WriteLine($"Alternate filter (!= Exterior): {nInt + nBnd}");
        Console.WriteLine();

        // Also Contains-based filter (OGC Contains excludes boundary of both).
        int nContains = triangles.Count(t => polygon.Contains(t.Centroid));
        int nCovers = triangles.Count(t => polygon.Covers(t.Centroid));
        Console.WriteLine($"polygon.Contains(centroid): {nContains}");
        Console.WriteLine($"polygon.Covers(centroid):   {nCovers}");

        // Straddle check: interior-centroid triangles that are not fully covered.
        int notCovered = 0, notWithin = 0;
        foreach (var x in byLocation.Where(x => x.Loc == Location.Interior))
        {
            if (!polygon.Covers(x.T)) notCovered++;
            if (!x.T.Within(polygon)) notWithin++;
        }
        Console.WriteLine($"Interior-centroid triangles not Covers(t): {notCovered}");
        Console.WriteLine($"Interior-centroid triangles not Within(poly): {notWithin}");
        Console.WriteLine();

        Console.WriteLine("--- triangles classified exterior by locator ---");
        foreach (var x in byLocation.Where(x => x.Loc == Location.Exterior))
        {
            var ring = x.T.ExteriorRing.Coordinates;
            Console.WriteLine(
                $"  EXT centroid=({Fmt(x.C.X)},{Fmt(x.C.Y)}) " +
                $"verts={FmtTri(ring)} area={x.T.Area:R}");
        }
        Console.WriteLine();

        Console.WriteLine("--- triangles classified interior by locator ---");
        foreach (var x in byLocation.Where(x => x.Loc == Location.Interior))
        {
            Console.WriteLine(
                $"  INT centroid=({Fmt(x.C.X)},{Fmt(x.C.Y)}) " +
                $"verts={FmtTri(x.T.ExteriorRing.Coordinates)} area={x.T.Area:R}");
        }
        Console.WriteLine();

        // Build undirected edge → list of opposite vertices (adjacency).
        var edgeMap = new Dictionary<string, List<(Coordinate A, Coordinate B, Coordinate Opp, Polygon T)>>();
        foreach (var t in triangles)
        {
            var c = t.ExteriorRing.Coordinates;
            // c[0],c[1],c[2],c[3]=c[0]
            AddEdge(edgeMap, c[0], c[1], c[2], t);
            AddEdge(edgeMap, c[1], c[2], c[0], t);
            AddEdge(edgeMap, c[2], c[0], c[1], t);
        }

        // Constraint edges (scaled polygon shell, undirected).
        var constraintKeys = new HashSet<string>();
        var shell = polygon.ExteriorRing.Coordinates;
        for (int i = 0; i < shell.Length - 1; i++)
            constraintKeys.Add(EdgeKey(shell[i], shell[i + 1]));

        int internalEdges = 0;
        int illegal = 0;
        int illegalUnconstrained = 0;
        int oracleCalls = 0;
        int oracleFails = 0;

        Console.WriteLine("--- internal edges: Rocq INCIRCLE_SIGN (local Delaunay) ---");
        Console.WriteLine("illegal iff 0 < inCircle(A,B,C,D) with (A,B,C) CCW (strict empty-circle violation)");
        Console.WriteLine();

        foreach (var (key, list) in edgeMap)
        {
            if (list.Count != 2)
                continue; // hull edge or degenerate

            internalEdges++;
            var e0 = list[0];
            var e1 = list[1];
            var A = e0.A;
            var B = e0.B;
            var C = e0.Opp;
            var D = e1.Opp;

            // Ensure CCW orientation of ABC for the Shewchuk reading.
            double orient = Orient2D(A, B, C);
            double ax = A.X, ay = A.Y, bx = B.X, by = B.Y, cx = C.X, cy = C.Y, dx = D.X, dy = D.Y;
            if (orient < 0)
            {
                // swap A,B so ABC becomes CCW
                (ax, bx) = (bx, ax);
                (ay, by) = (by, ay);
            }

            bool isConstraint = constraintKeys.Contains(key);
            if (!TryOracleInCircle(ax, ay, bx, by, cx, cy, dx, dy, out var sign, out var val, out var err))
            {
                oracleFails++;
                Console.WriteLine($"  EDGE {key}: oracle error: {err}");
                continue;
            }
            oracleCalls++;

            // Local Delaunay: inCircle <= 0. Strict violation: POS (val > 0).
            bool isIllegal = sign == "POS";
            if (isIllegal)
            {
                illegal++;
                if (!isConstraint) illegalUnconstrained++;
            }

            string tag = isIllegal ? "ILLEGAL" : "legal  ";
            string ctag = isConstraint ? "CONSTRAINT" : "free      ";
            if (isIllegal || args.Contains("--verbose", StringComparer.OrdinalIgnoreCase))
            {
                Console.WriteLine(
                    $"  {tag} {ctag} {sign} val={val:R} " +
                    $"AB=({Fmt(A.X)},{Fmt(A.Y)})-({Fmt(B.X)},{Fmt(B.Y)}) " +
                    $"C=({Fmt(C.X)},{Fmt(C.Y)}) D=({Fmt(D.X)},{Fmt(D.Y)})");
            }
        }

        Console.WriteLine();
        Console.WriteLine("=== SUMMARY ===");
        Console.WriteLine($"triangles total / interior / exterior / boundary: " +
                          $"{triangles.Count} / {nInt} / {nExt} / {nBnd}");
        Console.WriteLine($"internal edges checked: {internalEdges}");
        Console.WriteLine($"oracle INCIRCLE calls: {oracleCalls} (fails={oracleFails})");
        Console.WriteLine($"strict empty-circle violations: {illegal} " +
                          $"(of which unconstrained: {illegalUnconstrained})");
        Console.WriteLine();
        Console.WriteLine(
            illegal == 0
                ? "Verdict (A): no strict local-Delaunay violations on internal edges (oracle)."
                : illegalUnconstrained > 0
                    ? "Verdict (A): unconstrained internal edge(s) fail empty-circle — quality defect class."
                    : "Verdict (A): violations only on CONSTRAINT edges — expected under constrained/conforming DT.");
        Console.WriteLine(
            nExt > 0
                ? $"Verdict (B): locator drops {nExt} exterior centroid(s); keeps {nInt} interior."
                : "Verdict (B): locator found no exterior centroids (every triangle centroid inside/on polygon).");

        return 0;
    }

    private static void AddEdge(
        Dictionary<string, List<(Coordinate A, Coordinate B, Coordinate Opp, Polygon T)>> map,
        Coordinate u, Coordinate v, Coordinate opp, Polygon t)
    {
        var key = EdgeKey(u, v);
        // Store oriented as sorted endpoints for A,B consistency.
        Coordinate a = u, b = v;
        if (CompareCoord(u, v) > 0) { a = v; b = u; }
        if (!map.TryGetValue(key, out var list))
        {
            list = new List<(Coordinate, Coordinate, Coordinate, Polygon)>();
            map[key] = list;
        }
        list.Add((a, b, opp, t));
    }

    private static string EdgeKey(Coordinate u, Coordinate v)
    {
        var a = u;
        var b = v;
        if (CompareCoord(u, v) > 0) { a = v; b = u; }
        return $"{Fmt(a.X)},{Fmt(a.Y)}|{Fmt(b.X)},{Fmt(b.Y)}";
    }

    private static int CompareCoord(Coordinate u, Coordinate v)
    {
        int cx = u.X.CompareTo(v.X);
        return cx != 0 ? cx : u.Y.CompareTo(v.Y);
    }

    private static double Orient2D(Coordinate a, Coordinate b, Coordinate c)
        => (b.X - a.X) * (c.Y - a.Y) - (b.Y - a.Y) * (c.X - a.X);

    private static string Fmt(double x) => x.ToString("G17", CultureInfo.InvariantCulture);

    private static string FmtTri(Coordinate[] ring)
    {
        // 4 coords with closure
        return string.Join(" ",
            Enumerable.Range(0, 3).Select(i => $"({Fmt(ring[i].X)},{Fmt(ring[i].Y)})"));
    }

    /// <summary>
    /// Call oracle_bin INCIRCLE_SIGN (extracted b64_inCircle — same kernel as
    /// nts_rocq_in_circle FFI). Prefers ORACLE_BIN, then WSL_ORACLE_BIN / default WSL path.
    /// </summary>
    private static bool TryOracleInCircle(
        double ax, double ay, double bx, double by,
        double cx, double cy, double px, double py,
        out string sign, out double value, out string error)
    {
        sign = "";
        value = double.NaN;
        error = "";

        string input = string.Create(CultureInfo.InvariantCulture,
            $"INCIRCLE_SIGN\n{ax} {ay}\n{bx} {by}\n{cx} {cy}\n{px} {py}\n");

        string? winOracle = Environment.GetEnvironmentVariable("ORACLE_BIN");
        if (!string.IsNullOrWhiteSpace(winOracle) && File.Exists(winOracle))
        {
            return RunProcessCapture(winOracle, "", input, out sign, out value, out error);
        }

        // Same extracted kernel as Phase 5 FFI (nts_rocq_in_circle); invoked via
        // oracle_bin protocol over WSL when libntsrocq is not loaded in-process.
        // Absolute path: do not rely on $HOME expansion inside quoted -c strings.
        string wslOracle = Environment.GetEnvironmentVariable("WSL_ORACLE_BIN")
            ?? "/home/user/nettopologysuite.proofs/oracle/oracle_bin";
        // Invoke the binary directly (no bash -c) so stdin is the oracle protocol.
        return RunProcessCapture("wsl.exe", $"-e {wslOracle}", input,
            out sign, out value, out error);
    }

    private static bool RunProcessCapture(
        string fileName, string arguments, string stdin,
        out string sign, out double value, out string error)
    {
        sign = "";
        value = double.NaN;
        error = "";
        try
        {
            var psi = new ProcessStartInfo
            {
                FileName = fileName,
                Arguments = arguments,
                RedirectStandardInput = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
                CreateNoWindow = true,
                StandardOutputEncoding = Encoding.UTF8,
                StandardErrorEncoding = Encoding.UTF8,
            };
            using var p = Process.Start(psi)
                ?? throw new InvalidOperationException("failed to start process");
            if (!string.IsNullOrEmpty(stdin))
            {
                p.StandardInput.Write(stdin);
                p.StandardInput.Close();
            }
            string stdout = p.StandardOutput.ReadToEnd();
            string stderr = p.StandardError.ReadToEnd();
            p.WaitForExit(60_000);
            if (p.ExitCode != 0)
            {
                error = $"exit {p.ExitCode}: {stderr} {stdout}".Trim();
                return false;
            }
            // Response: "POS 0x1.8p+0" or "NEG ..." etc.
            var line = stdout.Trim().Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
            if (line.Length < 2)
            {
                error = $"bad oracle output: '{stdout.Trim()}'";
                return false;
            }
            sign = line[0];
            // hex float 0x1.8p+0 — double.Parse doesn't do hex floats; use
            // Convert via C-style. .NET: use double.Parse with HexFloat not available.
            value = ParseHexFloat(line[1]);
            return true;
        }
        catch (Exception ex)
        {
            error = ex.Message;
            return false;
        }
    }

    private static double ParseHexFloat(string s)
    {
        // Accept decimal or C99 hex float (0x1.8p+0).
        if (s.StartsWith("0x", StringComparison.OrdinalIgnoreCase)
            || s.StartsWith("-0x", StringComparison.OrdinalIgnoreCase))
        {
            // Use BitConverter via OCaml-compatible: Convert through C# "R" is hard;
            // parse manually: [+-]?0xH.Hp[+-]d
            bool neg = s[0] == '-';
            string t = neg ? s[1..] : s;
            if (!t.StartsWith("0x", StringComparison.OrdinalIgnoreCase))
                throw new FormatException(s);
            t = t[2..];
            int pIdx = t.IndexOf('p');
            if (pIdx < 0) pIdx = t.IndexOf('P');
            if (pIdx < 0) throw new FormatException(s);
            string mant = t[..pIdx];
            int exp = int.Parse(t[(pIdx + 1)..], CultureInfo.InvariantCulture);
            int dot = mant.IndexOf('.');
            string whole = dot >= 0 ? mant[..dot] : mant;
            string frac = dot >= 0 ? mant[(dot + 1)..] : "";
            // value = (whole.frac as hex) * 2^exp
            double v = 0;
            foreach (char ch in whole)
                v = v * 16 + HexDigit(ch);
            double place = 16;
            foreach (char ch in frac)
            {
                v += HexDigit(ch) / place;
                place *= 16;
            }
            v = Math.ScaleB(v, exp); // v * 2^exp
            return neg ? -v : v;
        }
        return double.Parse(s, CultureInfo.InvariantCulture);
    }

    private static int HexDigit(char ch) => ch switch
    {
        >= '0' and <= '9' => ch - '0',
        >= 'a' and <= 'f' => 10 + ch - 'a',
        >= 'A' and <= 'F' => 10 + ch - 'A',
        _ => throw new FormatException($"bad hex digit {ch}")
    };

    private static string BashSingleQuote(string s)
        => "'" + s.Replace("'", "'\\''") + "'";
}

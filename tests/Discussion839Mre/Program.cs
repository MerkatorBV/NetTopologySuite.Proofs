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
using Discussion839Mre;
using NetTopologySuite.Algorithm;
using NetTopologySuite.Algorithm.Locate;
using NetTopologySuite.Geometries;
using NetTopologySuite.IO;
using NetTopologySuite.Noding;
using NetTopologySuite.Noding.Snapround;
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

        // JTS#90 ScaledNoder scale=0/1 policy scout (no oracle required).
        if (args.Contains("--jts90", StringComparer.OrdinalIgnoreCase)
            || args.Contains("--scaled-noder", StringComparer.OrdinalIgnoreCase))
        {
            return RunJts90ScaledNoderMre();
        }

        // JTS#1145 YStripes PIP gallery vs corpus oracle (no Rocq binary required).
        if (args.Contains("--jts1145", StringComparer.OrdinalIgnoreCase)
            || args.Contains("--ystripes", StringComparer.OrdinalIgnoreCase)
            || args.Contains("--pip-gallery", StringComparer.OrdinalIgnoreCase))
        {
            return RunJts1145PipGallery();
        }

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

    /// <summary>
    /// JTS PR #1145 YStripesPointInAreaLocator vs NTS Indexed/Simple locators
    /// on the corpus PIP gallery (docs/nts-oracle-gallery.md). Geometric GT is
    /// the Qed-backed correct answer; pure ray-parity is recorded separately
    /// where it disagrees at vertex-graze / horizontal-edge rows.
    /// </summary>
    private static int RunJts1145PipGallery()
    {
        Console.WriteLine("=== JTS#1145 YStripes PIP gallery (corpus oracle) ===");
        Console.WriteLine($"NTS: {typeof(Geometry).Assembly.GetName().Version}");
        Console.WriteLine("Locators: IndexedPointInAreaLocator | SimplePointInAreaLocator | YStripes (PR#1145 port)");
        Console.WriteLine("GT: geometric correct answer from docs/nts-oracle-gallery.md (Qed theorems)");
        Console.WriteLine();

        var rdr = new WKTReader();
        var cases = GalleryCases();
        int pass = 0, fail = 0, warn = 0;
        var rows = new List<string>();

        Console.WriteLine(
            $"{"id",-8} {"pt",-22} {"GT",-9} {"parity",-9} {"Indexed",-9} {"Simple",-9} {"YStripes",-9} note");
        Console.WriteLine(new string('-', 110));

        foreach (var c in cases)
        {
            var geom = rdr.Read(c.Wkt);
            var pt = new Coordinate(c.X, c.Y);
            var indexed = new IndexedPointInAreaLocator(geom).Locate(pt);
            var simple = SimplePointInAreaLocator.Locate(pt, geom);
            var ystripes = new YStripesPointInAreaLocator(geom).Locate(pt);

            bool idxOk = MatchesGallery(indexed, c.GeomExpected);
            bool simOk = MatchesGallery(simple, c.GeomExpected);
            bool ysOk = MatchesGallery(ystripes, c.GeomExpected);
            bool parityMismatch = c.NaiveParityDiffers;

            string status;
            if (ysOk && idxOk && simOk)
            {
                pass++;
                status = "PASS";
            }
            else if (ysOk)
            {
                // YStripes correct vs GT; baseline may differ only on BOUNDARY convention
                warn++;
                status = "WARN";
            }
            else
            {
                fail++;
                status = "FAIL";
            }

            string note = status;
            if (parityMismatch) note += " | naive-parity≠geom";
            if (!idxOk) note += " | Indexed≠GT";
            if (!simOk) note += " | Simple≠GT";
            if (!ysOk) note += " | YStripes≠GT";
            if (ystripes != indexed) note += " | Y≠Indexed";
            if (ystripes != simple) note += " | Y≠Simple";

            string ptStr = $"({Fmt(c.X)},{Fmt(c.Y)})";
            Console.WriteLine(
                $"{c.Id,-8} {ptStr,-22} {LocTag(c.GeomExpected),-9} {c.NaiveParityTag,-9} " +
                $"{LocTag(indexed),-9} {LocTag(simple),-9} {LocTag(ystripes),-9} {note}");

            rows.Add(string.Join('\t',
                c.Id, c.X.ToString("G17", CultureInfo.InvariantCulture),
                c.Y.ToString("G17", CultureInfo.InvariantCulture),
                LocTag(c.GeomExpected), c.NaiveParityTag,
                LocTag(indexed), LocTag(simple), LocTag(ystripes), status, c.Theorem));
        }

        Console.WriteLine();
        Console.WriteLine("=== SUMMARY ===");
        Console.WriteLine($"cases: {cases.Count}  PASS(all=GT): {pass}  WARN(YStripes=GT): {warn}  FAIL(YStripes≠GT): {fail}");

        // Critical robustness rows that the gallery was built for
        var critical = new[] { "VGRAZE0", "HORZ_E", "SPECT_POCK", "HAT_POCK" };
        int critFail = 0;
        foreach (var c in cases.Where(c => critical.Contains(c.Id)))
        {
            var geom = rdr.Read(c.Wkt);
            var ys = new YStripesPointInAreaLocator(geom).Locate(new Coordinate(c.X, c.Y));
            if (!MatchesGallery(ys, c.GeomExpected))
            {
                critFail++;
                Console.WriteLine($"  CRITICAL FAIL {c.Id}: YStripes={LocTag(ys)} GT={LocTag(c.GeomExpected)}");
            }
        }

        Console.WriteLine();
        Console.WriteLine("=== VERDICT ===");
        if (fail == 0 && critFail == 0)
        {
            Console.WriteLine("  GREEN: YStripes port matches geometric GT on all gallery vectors");
            Console.WriteLine("         (vertex-graze, horizontal-edge, Spectre pocket, Hat pocket, rect/pixel boundary).");
            Console.WriteLine("  Product: safe soundness gate for JTS#1145; recommend adding these WKT pins to AbstractPointInRingTest.");
        }
        else
        {
            Console.WriteLine($"  RED: {fail} YStripes≠GT ({critFail} critical). Do not rubber-stamp #1145.");
        }
        Console.WriteLine("See docs/jts-1145-pip-lane-2026-08.md");
        Console.WriteLine();
        Console.WriteLine("--- machine table (tab) ---");
        Console.WriteLine("id\tx\ty\tGT\tparity\tIndexed\tSimple\tYStripes\tstatus\ttheorem");
        foreach (var r in rows) Console.WriteLine(r);

        return fail == 0 ? 0 : 1;
    }

    private sealed record GalleryCase(
        string Id,
        string Wkt,
        double X,
        double Y,
        Location GeomExpected,
        string NaiveParityTag,
        bool NaiveParityDiffers,
        string Theorem);

    private static List<GalleryCase> GalleryCases()
    {
        // WKT + geometric answers from docs/nts-oracle-gallery.md.
        // Location.Boundary rows are OGC boundary (Contains=false); pure parity half-open
        // is recorded in NaiveParityTag where relevant.
        const string diamond =
            "POLYGON ((0 1, 1 0, 0 -1, -1 0, 0 1))";
        const string notch =
            "POLYGON ((0 0, 4 0, 4 2, 2 2, 2 1, 0 1, 0 0))";
        const string rect =
            "POLYGON ((0 0, 4 0, 4 3, 0 3, 0 0))";
        const string pixel =
            "POLYGON ((-0.5 -0.5, 0.5 -0.5, 0.5 0.5, -0.5 0.5, -0.5 -0.5))";
        const string spectre =
            "POLYGON ((0 0, 2 0, 3.5 1, 4 0, 6 0, 7.5 1, 7 2, 5 2, 4.5 3, 3 2, 1 2, 0.5 1, -0.5 1, 0 0))";
        // Hat monotile APPROX (exact uses √3); still exercises concave pocket.
        const string hat =
            "POLYGON ((0 0, 2 0, 3.5 0.8660254, 4 0, 6 0, 7.5 0.8660254, 7 1.7320508, 5 1.7320508, 4.5 2.5980762, 3 1.7320508, 1 1.7320508, 0.5 0.8660254, -0.5 0.8660254, 0 0))";

        double s3 = Math.Sqrt(3.0);

        return new List<GalleryCase>
        {
            // Tier 1.1 vertex graze
            new("VGRAZE_G", diamond, 0, 0.5, Location.Interior, "odd", false,
                "diamond_point_in_ring_A"),
            new("VGRAZE0", diamond, 0, 0, Location.Interior, "even*", true,
                "diamond_refutes_parity_seam"),

            // Tier 1.2 horizontal edge
            new("HORZ_E", notch, -1, 1, Location.Exterior, "odd*", true,
                "notch_refutes_parity_without_guard"),

            // Tier 1.3 rectangle half-open / OGC boundary
            new("RECT_IN", rect, 2, 1.5, Location.Interior, "in", false,
                "point_in_ring_rect_iff"),
            new("RECT_L", rect, 0, 1.5, Location.Boundary, "parity-in", true,
                "point_in_ring_rect_iff left"),
            new("RECT_R", rect, 4, 1.5, Location.Boundary, "parity-out", false,
                "point_in_ring_rect_iff right"),
            new("RECT_B", rect, 2, 0, Location.Boundary, "parity-out", false,
                "point_in_ring_rect_iff bottom"),
            new("RECT_T", rect, 2, 3, Location.Boundary, "parity-out", false,
                "point_in_ring_rect_iff top"),

            // Tier 1.4 hot pixel
            new("PIX_C", pixel, 0, 0, Location.Interior, "in", false,
                "unit_pixel_centre_in_ring"),
            new("PIX_BOT", pixel, 0, -0.5, Location.Boundary, "parity-out*", true,
                "pixel_grazing_bottom_edge"),

            // Tier 2 Spectre
            new("SPECT_IN", spectre, 5, 0.5, Location.Interior, "odd", false,
                "spectre_parity_classification"),
            new("SPECT_POCK", spectre, 3.5, 0.5, Location.Exterior, "even", false,
                "spectre_parity_classification pocket"),

            // Tier 2 Hat (approx WKT; GT from geometric pocket/interior)
            new("HAT_IN", hat, 4.25, 5 * s3 / 4, Location.Interior, "odd", false,
                "hat_parity_classification interior APPROX"),
            new("HAT_POCK", hat, 3.5, s3 / 4, Location.Exterior, "even", false,
                "hat_parity_classification pocket APPROX"),
        };
    }

    /// <summary>
    /// Gallery GT for robust OGC-style locators: Interior / Exterior / Boundary.
    /// Pure parity may disagree on * rows; MatchesGallery accepts Boundary as a
    /// correct robust answer whenever GT is Boundary.
    /// </summary>
    private static bool MatchesGallery(Location got, Location expected) => got == expected;

    private static string LocTag(Location loc) => loc switch
    {
        Location.Interior => "INT",
        Location.Exterior => "EXT",
        Location.Boundary => "BND",
        _ => loc.ToString(),
    };

    /// <summary>
    /// JTS PR #90 / mukoki OpenJUMP beanshell: ScaledNoder(scale=1) vs scale≠1
    /// rounds input vertices inconsistently (NTS port of the same control flow).
    /// </summary>
    private static int RunJts90ScaledNoderMre()
    {
        Console.WriteLine("=== JTS#90 ScaledNoder MRE (NTS port of master control flow) ===");
        Console.WriteLine($"NTS: {typeof(Geometry).Assembly.GetName().Version}");
        Console.WriteLine("Input: mukoki lines from locationtech/jts#90 comments");
        Console.WriteLine("  L1 = LINESTRING(0 0, 20.11111 30.11111)");
        Console.WriteLine("  L2 = LINESTRING(20.11111 0, 10.11111 30.11111)");
        // MCIndexSnapRounder is obsolete and crashes under NTS 2.6 HPRtree;
        // SnapRoundingNoder is the production successor (BufferOp fixed-precision path).
        Console.WriteLine("Inner noder: SnapRoundingNoder(PrecisionModel(1.0))");
        Console.WriteLine("(mukoki used MCIndexSnapRounder; same ScaledNoder scale skip applies)");
        Console.WriteLine();

        var l1 = new Coordinate[] { new(0, 0), new(20.11111, 30.11111) };
        var l2 = new Coordinate[] { new(20.11111, 0), new(10.11111, 30.11111) };

        // Policy mirrors of ScaledNoder ctor:
        //   master / NTS 2.6: isScaled = (scale != 1.0)   // skip at scale=1
        //   PR #90:           isScaled = (scale != 0.0)   // skip only at scale=0
        Console.WriteLine("Policy table (would scale inputs?):");
        Console.WriteLine("  scale | master/NTS | PR#90");
        foreach (double s in new[] { 0.0, 1.0, 100.0 })
        {
            bool master = s != 1.0;
            bool pr90 = s != 0.0;
            Console.WriteLine($"  {s,5:0.#} | {master,10} | {pr90}");
        }
        Console.WriteLine();

        // Footgun: master treats scale=0 as "scaled" → Math.Round(x*0)=0 collapse.
        Console.WriteLine("--- scale=0 footgun (master path would Scale) ---");
        var collapsed = ScaleCoords(l1, 0.0);
        Console.WriteLine($"  scale(L1, 0) → {FmtCoords(collapsed)}  (all finite → origin)");
        Console.WriteLine();

        double[] scales = { 1.0, 100.0 };
        var results = new Dictionary<double, IList<ISegmentString>>();

        foreach (double scale in scales)
        {
            var noder = new ScaledNoder(
                new SnapRoundingNoder(new PrecisionModel(1.0)),
                scale);
            var input = new List<ISegmentString>
            {
                new NodedSegmentString((Coordinate[])l1.Clone(), null!),
                new NodedSegmentString((Coordinate[])l2.Clone(), null!),
            };
            noder.ComputeNodes(input);
            var noded = noder.GetNodedSubstrings();
            results[scale] = noded;

            Console.WriteLine($"--- ScaledNoder(scale={scale}) IsIntegerPrecision={noder.IsIntegerPrecision} ---");
            PrintNoded(noded);
            Console.WriteLine($"  vertex grid membership (all coords on 1/scale lattice?): " +
                              $"{AllOnGrid(noded, scale)}");
            Console.WriteLine();
        }

        // Compare endpoint retention: scale=1 keeps full-precision inputs; scale=100 does not.
        var ends1 = CollectEndpoints(results[1.0]);
        var ends100 = CollectEndpoints(results[100.0]);

        // After rescale, scale=100 coords live on 0.01 grid; scale=1 mixed.
        bool scale1InputsRounded = !ends1.Any(c =>
            ApproxEq(c.X, 20.11111) || ApproxEq(c.Y, 30.11111) || ApproxEq(c.X, 10.11111));
        bool scale100InputsRounded = !ends100.Any(c =>
            ApproxEq(c.X, 20.11111) || ApproxEq(c.Y, 30.11111) || ApproxEq(c.X, 10.11111));

        bool grid1 = AllOnGrid(results[1.0], 1.0);
        bool grid100 = AllOnGrid(results[100.0], 100.0);

        Console.WriteLine("=== INVARIANT CHECKS (NTS 2.6 + SnapRoundingNoder) ===");
        Console.WriteLine($"  scale=1 keeps raw non-integer input verts after noding: {!scale1InputsRounded}");
        Console.WriteLine($"  scale=100 rounds input vertices to 0.01 grid: {scale100InputsRounded}");
        Console.WriteLine($"  scale=1 all vertices integer-grid: {grid1}");
        Console.WriteLine($"  scale=100 all vertices 0.01-grid: {grid100}");

        // Simulated PR#90 path for scale=1: force a priori Scale even when scale==1.
        Console.WriteLine();
        Console.WriteLine("--- simulated PR#90 a priori scale=1 (round then SRN) ---");
        var forced = new List<ISegmentString>
        {
            new NodedSegmentString(ScaleCoords(l1, 1.0), null!),
            new NodedSegmentString(ScaleCoords(l2, 1.0), null!),
        };
        var inner = new SnapRoundingNoder(new PrecisionModel(1.0));
        inner.ComputeNodes(forced);
        var forcedOut = inner.GetNodedSubstrings();
        Console.WriteLine("  noded:");
        PrintNoded(forcedOut);
        Console.WriteLine($"  all vertices integer-grid: {AllOnGrid(forcedOut, 1.0)}");
        bool sameAsSkip = NodedEquals(results[1.0], forcedOut);
        Console.WriteLine($"  bit-equal to ScaledNoder(scale=1) skip path: {sameAsSkip}");

        // Historical MCIndexSnapRounder model (intersection-only int snap).
        Console.WriteLine();
        Console.WriteLine("--- historical model (MCIndexSnapRounder-style, intersection-only) ---");
        var rawI = SegIntersection(l1[0], l1[1], l2[0], l2[1]);
        var intI = new Coordinate(Math.Round(rawI.X), Math.Round(rawI.Y));
        Console.WriteLine($"  raw intersection ≈ ({Fmt(rawI.X)}, {Fmt(rawI.Y)})");
        Console.WriteLine($"  int-snapped node: ({Fmt(intI.X)}, {Fmt(intI.Y)})");
        Console.WriteLine($"  master scale=1 skip: ends keep frac {Fmt(l1[1].X)},{Fmt(l1[1].Y)} + node int");
        Console.WriteLine($"  master scale=100: ends on 0.01 + node on 0.01 (mukoki REPRO class)");

        bool srnMasksMukoki = grid1 && scale1InputsRounded; // modern SRN snaps verts too
        bool scale0Footgun = collapsed.Length == 1
            && ApproxEq(collapsed[0].X, 0) && ApproxEq(collapsed[0].Y, 0);

        Console.WriteLine();
        Console.WriteLine("=== VERDICT ===");
        Console.WriteLine(srnMasksMukoki
            ? "  A) Mukoki mixed-precision (scale=1) is MASKED by SnapRoundingNoder (verts snapped)."
            : "  A) Mukoki mixed-precision still visible under this noder.");
        Console.WriteLine(scale0Footgun
            ? "  B) scale=0 footgun LIVE: Math.Round(x*0) collapses finite coords to origin."
            : "  B) scale=0 collapse not observed.");
        Console.WriteLine(sameAsSkip
            ? "  C) On this input, a priori scale=1 equals skip+SRN (no topology delta here)."
            : "  C) A priori scale=1 DIFFERS from skip+SRN on this input.");
        Console.WriteLine("  D) Corpus: wrapper policy / scale=0 safety; not SnapRoundingScale_b64 algebra.");
        Console.WriteLine("See docs/jts-90-scalednoder-lane-2026-08.md");

        // Exit 0 when the two live findings we care about are demonstrated.
        return (srnMasksMukoki && scale0Footgun) ? 0 : 1;
    }

    private static Coordinate SegIntersection(Coordinate a, Coordinate b, Coordinate c, Coordinate d)
    {
        double x1 = a.X, y1 = a.Y, x2 = b.X, y2 = b.Y;
        double x3 = c.X, y3 = c.Y, x4 = d.X, y4 = d.Y;
        double den = (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4);
        double t = ((x1 - x3) * (y3 - y4) - (y1 - y3) * (x3 - x4)) / den;
        return new Coordinate(x1 + t * (x2 - x1), y1 + t * (y2 - y1));
    }

    private static bool NodedEquals(IList<ISegmentString> a, IList<ISegmentString> b)
    {
        if (a.Count != b.Count) return false;
        for (int i = 0; i < a.Count; i++)
        {
            var ca = a[i].Coordinates;
            var cb = b[i].Coordinates;
            if (ca.Length != cb.Length) return false;
            for (int j = 0; j < ca.Length; j++)
            {
                if (!ApproxEq(ca[j].X, cb[j].X) || !ApproxEq(ca[j].Y, cb[j].Y))
                    return false;
            }
        }
        return true;
    }

    private static Coordinate[] ScaleCoords(Coordinate[] pts, double scaleFactor)
    {
        var roundPts = new Coordinate[pts.Length];
        for (int i = 0; i < pts.Length; i++)
        {
            roundPts[i] = new Coordinate(
                Math.Round(pts[i].X * scaleFactor),
                Math.Round(pts[i].Y * scaleFactor));
        }
        return CoordinateArrays.RemoveRepeatedPoints(roundPts);
    }

    private static void PrintNoded(IList<ISegmentString> noded)
    {
        int i = 0;
        foreach (var ss in noded)
        {
            Console.WriteLine($"  [{i++}] {FmtCoords(ss.Coordinates)}");
        }
    }

    private static string FmtCoords(Coordinate[] pts) =>
        "LINESTRING (" + string.Join(", ", pts.Select(p => $"{Fmt(p.X)} {Fmt(p.Y)}")) + ")";

    private static List<Coordinate> CollectEndpoints(IList<ISegmentString> noded)
    {
        var list = new List<Coordinate>();
        foreach (var ss in noded)
            foreach (var c in ss.Coordinates)
                list.Add(c);
        return list;
    }

    private static bool AllOnGrid(IList<ISegmentString> noded, double scale)
    {
        foreach (var ss in noded)
        {
            foreach (var c in ss.Coordinates)
            {
                double sx = c.X * scale;
                double sy = c.Y * scale;
                if (Math.Abs(sx - Math.Round(sx)) > 1e-9) return false;
                if (Math.Abs(sy - Math.Round(sy)) > 1e-9) return false;
            }
        }
        return true;
    }

    private static bool ApproxEq(double a, double b) => Math.Abs(a - b) <= 1e-9;

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

// CurveOracleBugHunt — differential NTS#857 curves vs Rocq oracle_bin
// Assisted-by: xAI Grok

using System.Diagnostics;
using System.Globalization;
using NetTopologySuite.Geometries;
using NetTopologySuite.Geometries.Curves;
using NetTopologySuite.IO;
using NetTopologySuite.Operation.Distance;

static class Program
{
    static int Main()
    {
        var gf = new GeometryFactory();
        var wkt = new WKTReader();
        int fails = 0, warns = 0, ok = 0;

        void Hit(string severity, string tag, string detail)
        {
            if (severity is "FAIL" or "BUG") fails++;
            else if (severity == "WARN") warns++;
            else ok++;
            Console.WriteLine($"{severity}\t{tag}\t{detail}");
        }

        static double Hyp(double x, double y) => Math.Sqrt(x * x + y * y);

        Console.WriteLine("=== ARC_LENGTH vs NTS CircularString.Length ===");
        foreach (var a in Cases.Arcs)
        {
            string stdin = $"ARC_LENGTH\n{a.Ax} {a.Ay}\n{a.Bx} {a.By}\n{a.Cx} {a.Cy}\n";
            string oOut;
            try { oOut = Oracle.Run(stdin); }
            catch (Exception ex) { Hit("FAIL", $"LEN/{a.Name}", $"oracle: {ex.Message}"); continue; }

            var cs = new CircularString(
                gf.CoordinateSequenceFactory.Create(new[]
                {
                    new Coordinate(a.Ax, a.Ay), new Coordinate(a.Bx, a.By), new Coordinate(a.Cx, a.Cy)
                }), gf);
            double ntsLen = cs.Length;
            double polyChord = Hyp(a.Bx - a.Ax, a.By - a.Ay) + Hyp(a.Cx - a.Bx, a.Cy - a.By);

            if (oOut is "DEGENERATE" or "NAN")
            {
                Hit("WARN", $"LEN/{a.Name}", $"oracle={oOut} nts_chord_len={ntsLen:G17}");
                continue;
            }

            double oracleLen = Oracle.ParseHexFloat(oOut);
            double rel = Math.Abs(ntsLen - oracleLen) / Math.Max(oracleLen, 1e-30);
            bool matchesPoly = Math.Abs(ntsLen - polyChord) < 1e-12;
            bool matchesOracle = rel < 1e-9;

            if (matchesOracle)
                Hit("OK", $"LEN/{a.Name}", $"nts={ntsLen:G17} oracle={oracleLen:G17}");
            else if (matchesPoly && oracleLen >= ntsLen - 1e-9)
                Hit("BUG", $"LEN/{a.Name}",
                    $"NTS Length is control-polyline={ntsLen:G17}; oracle arc={oracleLen:G17}; " +
                    $"short_by={(oracleLen - ntsLen):G17} ({100 * (oracleLen - ntsLen) / oracleLen:F2}%)");
            else
                Hit("FAIL", $"LEN/{a.Name}", $"nts={ntsLen:G17} oracle={oracleLen:G17} poly={polyChord:G17}");
        }

        Console.WriteLine("=== ENVELOPE (control bbox vs arc bulge) ===");
        {
            static double Deg(double d) => d * Math.PI / 180;
            double a2x = Math.Cos(Deg(-30)), a2y = Math.Sin(Deg(-30));
            double b2x = Math.Cos(Deg(10)), b2y = Math.Sin(Deg(10));
            double c2x = Math.Cos(Deg(50)), c2y = Math.Sin(Deg(50));
            var cs2 = new CircularString(gf.CoordinateSequenceFactory.Create(new[]
            {
                new Coordinate(a2x, a2y), new Coordinate(b2x, b2y), new Coordinate(c2x, c2y)
            }), gf);
            var env2 = cs2.EnvelopeInternal;
            const double trueMaxX = 1.0; // angle 0° on unit circle lies on arc
            if (env2.MaxX + 1e-12 < trueMaxX)
                Hit("BUG", "ENV/axis_extreme",
                    $"control-point envelope MaxX={env2.MaxX:G17} < true arc MaxX={trueMaxX:G17} " +
                    $"(unit circle arc −30°…50°; GEOS uses analytical envelope)");
            else
                Hit("OK", "ENV/axis_extreme", $"MaxX={env2.MaxX:G17}");
        }

        Console.WriteLine("=== ARC_DISTANCE vs NTS Distance(Point, CircularString) ===");
        foreach (var q in Cases.DistQueries)
        {
            var a = Cases.Arcs[q.ArcIdx];
            string stdin = $"ARC_DISTANCE\n{a.Ax} {a.Ay}\n{a.Bx} {a.By}\n{a.Cx} {a.Cy}\n{q.Px} {q.Py}\n";
            string oOut;
            try { oOut = Oracle.Run(stdin); }
            catch (Exception ex) { Hit("FAIL", $"DIST/{q.Name}", $"oracle: {ex.Message}"); continue; }

            var cs = new CircularString(gf.CoordinateSequenceFactory.Create(new[]
            {
                new Coordinate(a.Ax, a.Ay), new Coordinate(a.Bx, a.By), new Coordinate(a.Cx, a.Cy)
            }), gf);
            var pt = gf.CreatePoint(new Coordinate(q.Px, q.Py));
            double ntsDist = DistanceOp.Distance(pt, cs);

            if (oOut is "DEGENERATE" or "NAN")
            {
                Hit("WARN", $"DIST/{q.Name}", $"oracle={oOut} nts={ntsDist:G17}");
                continue;
            }
            double oracleDist = Oracle.ParseHexFloat(oOut);
            double abs = Math.Abs(ntsDist - oracleDist);
            double rel = abs / Math.Max(oracleDist, 1e-30);
            if (abs < 1e-9 || (oracleDist > 1e-9 && rel < 1e-9))
                Hit("OK", $"DIST/{q.Name}", $"nts={ntsDist:G17} oracle={oracleDist:G17}");
            else
                Hit("BUG", $"DIST/{q.Name}",
                    $"nts={ntsDist:G17} oracle={oracleDist:G17} abs={abs:G17} (chord DistanceOp)");
        }

        Console.WriteLine("=== WKT/WKB structural ===");
        foreach (var s in new[]
        {
            "CIRCULARSTRING (0 0, 1 1, 2 0)",
            "COMPOUNDCURVE ((0 0, 1 0), CIRCULARSTRING (1 0, 2 1, 3 0))",
            "CURVEPOLYGON (CIRCULARSTRING (0 0, 2 2, 4 0, 2 -2, 0 0))",
            "MULTICURVE (CIRCULARSTRING (0 0, 1 1, 2 0), (3 0, 4 0))",
            "MULTISURFACE (CURVEPOLYGON (CIRCULARSTRING (0 0, 2 2, 4 0, 2 -2, 0 0)))",
        })
        {
            try
            {
                var g = wkt.Read(s);
                var bytes = new WKBWriter().Write(g);
                var g2 = new WKBReader().Read(bytes);
                if (!g2.EqualsExact(g))
                    Hit("BUG", "WKB/" + g.GeometryType, "EqualsExact failed after WKB round-trip");
                else
                    Hit("OK", "WKB/" + g.GeometryType, "round-trip");
            }
            catch (Exception ex)
            {
                Hit("FAIL", "WKB/" + s.Split(' ')[0], ex.Message);
            }
        }

        Console.WriteLine("=== RELATE_MATRIX token allowlist (no oracle) ===");
        {
            try
            {
                var (kind, val) = Oracle.ParseRelateWire("UNSUPPORTED");
                if (kind == "token" && val == "UNSUPPORTED")
                    Hit("OK", "REL/token_unsupported", "decline is a token, not a parse error");
                else
                    Hit("FAIL", "REL/token_unsupported", $"got {kind} {val}");
            }
            catch (Exception ex) { Hit("FAIL", "REL/token_unsupported", ex.Message); }

            try
            {
                var (kind, val) = Oracle.ParseRelateWire("FFFFFFFFF");
                if (kind == "matrix" && val == "FFFFFFFFF")
                    Hit("OK", "REL/matrix_disjoint_pin",
                        "#530 / #571 sentinel is a matrix, not UNSUPPORTED");
                else
                    Hit("FAIL", "REL/matrix_disjoint_pin", $"got {kind} {val}");
            }
            catch (Exception ex) { Hit("FAIL", "REL/matrix_disjoint_pin", ex.Message); }

            try
            {
                Oracle.ParseRelateWire("NOT_A_TOKEN");
                Hit("FAIL", "REL/unknown_rejected", "unknown token was accepted");
            }
            catch (Exception)
            {
                Hit("OK", "REL/unknown_rejected", "unknown token is still a parse error");
            }

            try
            {
                var (kind, val) = Oracle.ParseRelateWire("FF?FF1212");
                if (kind == "matrix" && val == "FF?FF1212")
                    Hit("OK", "REL/matrix_cell_unknown",
                        "? is a matrix cell, not a third parse kind (523-b)");
                else
                    Hit("FAIL", "REL/matrix_cell_unknown", $"got {kind} {val}");
            }
            catch (Exception ex) { Hit("FAIL", "REL/matrix_cell_unknown", ex.Message); }

            try
            {
                Oracle.ParseRelateWire("?");
                Hit("FAIL", "REL/bare_unknown_rejected", "bare ? was accepted as Decline");
            }
            catch (Exception)
            {
                Hit("OK", "REL/bare_unknown_rejected",
                    "bare ? is not Decline and not RELATE_TOKENS");
            }
        }

        Console.WriteLine("=== RELATE_MATRIX golden vectors (oracle catalog; #575 / 522-f) ===");
        foreach (var v in Cases.RelateVectors)
        {
            string oOut;
            try { oOut = Oracle.Run($"RELATE_MATRIX\n{v.Key}\n"); }
            catch (Exception ex)
            {
                Hit("WARN", $"REL/{v.Tag}", $"oracle missing or failed: {ex.Message}");
                continue;
            }
            try
            {
                var (kind, val) = Oracle.ParseRelateWire(oOut);
                if (kind == v.Kind && val == v.Expected)
                    Hit("OK", $"REL/{v.Tag}", $"{v.Key} -> {kind} {val} ({v.Provenance})");
                else
                    Hit("FAIL", $"REL/{v.Tag}",
                        $"{v.Key} -> {kind} {val} (exp {v.Kind} {v.Expected}); {v.Provenance}");
            }
            catch (Exception ex) { Hit("FAIL", $"REL/{v.Tag}", ex.Message); }
        }

        Console.WriteLine("=== chord_le_arc_length (oracle theorem) ===");
        foreach (var a in Cases.Arcs)
        {
            string oOut = Oracle.Run($"ARC_LENGTH\n{a.Ax} {a.Ay}\n{a.Bx} {a.By}\n{a.Cx} {a.Cy}\n");
            if (oOut is "DEGENERATE" or "NAN") continue;
            double oracleLen = Oracle.ParseHexFloat(oOut);
            double endChord = Hyp(a.Cx - a.Ax, a.Cy - a.Ay);
            if (endChord > oracleLen + 1e-9)
                Hit("FAIL", $"INVAR/{a.Name}", $"endChord {endChord} > arc {oracleLen}");
            else
                Hit("OK", $"INVAR/chord_le_arc/{a.Name}", $"chord={endChord:G9} arc={oracleLen:G9}");
        }

        Console.WriteLine();
        Console.WriteLine($"SUMMARY\tok={ok}\twarn={warns}\tbug_or_fail={fails}");
        return fails > 0 ? 1 : 0;
    }
}

static class Oracle
{
    public static string Run(string modeInput)
    {
        // Same contract as tests/GeosOracleBugHunt/hunt.py: ORACLE overrides,
        // default is the downloaded CI artifact (WSL path).
        string wslBin = Environment.GetEnvironmentVariable("ORACLE")
            ?? "/mnt/c/com/github/grootstebozewolf/NetTopologySuite.Proofs/.ci-artifacts/oracle-bin-linux/oracle_bin";
        var psi = new ProcessStartInfo
        {
            FileName = "wsl",
            Arguments = "-e " + wslBin,
            RedirectStandardInput = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        using var p = Process.Start(psi)!;
        p.StandardInput.Write(modeInput);
        p.StandardInput.Close();
        string stdout = p.StandardOutput.ReadToEnd().Trim();
        string stderr = p.StandardError.ReadToEnd();
        if (!p.WaitForExit(20000))
            throw new Exception("oracle timeout");
        if (p.ExitCode != 0 && string.IsNullOrEmpty(stdout))
            throw new Exception($"oracle exit {p.ExitCode}: {stderr}");
        return stdout;
    }

    /// <summary>
    /// Classify one RELATE_MATRIX oracle line.
    /// <c>UNSUPPORTED</c> is a decline (result position only), not a parse error.
    /// </summary>
    public static (string Kind, string Value) ParseRelateWire(string s)
    {
        string t = s.Trim();
        if (t == "UNSUPPORTED")
            return ("token", t);
        if (t.Length == 9 && t.All(c => c is 'F' or '0' or '1' or '2' or '?'))
            return ("matrix", t);
        throw new Exception(
            $"relate wire: not a 9-char matrix and not an allowlisted token: '{t}'");
    }

    public static double ParseHexFloat(string s)
    {
        if (s is "DEGENERATE" or "NAN") return double.NaN;
        s = s.Trim();
        bool neg = s.StartsWith('-');
        if (neg) s = s[1..];
        if (!s.StartsWith("0x", StringComparison.OrdinalIgnoreCase))
            return double.Parse(s, CultureInfo.InvariantCulture);
        s = s[2..];
        int p = s.IndexOf('p', StringComparison.OrdinalIgnoreCase);
        if (p < 0)
        {
            double v0 = Convert.ToInt64(s, 16);
            return neg ? -v0 : v0;
        }
        string mant = s[..p];
        int exp = int.Parse(s[(p + 1)..], CultureInfo.InvariantCulture);
        double m;
        int dot = mant.IndexOf('.');
        if (dot < 0)
            m = Convert.ToInt64(mant, 16);
        else
        {
            string whole = mant[..dot];
            string frac = mant[(dot + 1)..];
            m = whole.Length == 0 ? 0 : Convert.ToInt64(whole, 16);
            double f = 0;
            for (int i = 0; i < frac.Length; i++)
            {
                int d = Convert.ToInt32(frac.Substring(i, 1), 16);
                f = f * 16 + d;
            }
            m += f / Math.Pow(16, frac.Length);
        }
        double v = m * Math.Pow(2, exp);
        return neg ? -v : v;
    }
}

static class Cases
{
    public static readonly (string Name, double Ax, double Ay, double Bx, double By, double Cx, double Cy)[] Arcs =
    {
        ("unit_quarter", 1, 0, 0.7071067811865476, 0.7071067811865476, 0, 1),
        ("unit_semicircle", 1, 0, 0, 1, -1, 0),
        ("unit_lower_semi", 1, 0, 0, -1, -1, 0),
        ("R5_semi", 5, 0, 0, 5, -5, 0),
        ("flat_almost_chord", 0, 0, 5, 0.01, 10, 0),
        ("off_centre", 3, 4, 5, 4, 4, 5),
        ("tiny_arc", 0, 0, 1e-3, 1e-6, 2e-3, 0),
    };

    public static readonly (string Name, int ArcIdx, double Px, double Py)[] DistQueries =
    {
        ("semi_center", 1, 0, 0),
        ("semi_outside", 1, 0, 2),
        ("semi_endpoint", 1, 1, 0),
        ("semi_off_sweep", 1, 0, -2),
        ("quarter_origin", 0, 0, 0),
        ("quarter_inside", 0, 0.5, 0.5),
    };

    // Classifier pins from oracle/de9im_triangle_vectors.txt. Not OGC remints.
    // #530 is DISJOINT, not the decline. Decline is the T-junction (#577).
    public static readonly (string Tag, string Key, string Kind, string Expected, string Provenance)[] RelateVectors =
    {
        ("DISJOINT", "triangle_pair_fill TPR_Disjoint", "matrix", "FFFFFFFFF",
            "#571 / 522-c sentinel (the #530 pair, now classified)"),
        ("OVERLAP", "triangle_pair_fill TPR_Overlap", "matrix", "2FFF1FFF2",
            "#567 / 522-b overlap pair"),
        ("CONTAINS", "triangle_pair_fill TPR_Contains", "matrix", "2FFFFFFF2",
            "RelateMatrixTriangle.contains_pair_contains"),
        ("TOUCH_EDGE", "triangle_pair_fill TPR_TouchEdge", "matrix", "FFFF1FFF2",
            "frozen shared-edge pin"),
        ("TOUCH_VERTEX", "triangle_pair_fill TPR_TouchVertex", "matrix", "FFFF1FFF2",
            "#572 / 522-i pair"),
        ("DECLINE", "triangle_pair_fill TPR_Unsupported", "token", "UNSUPPORTED",
            "T-junction leftover (#577 / 522-j). Not the #530 pair."),
    };
}

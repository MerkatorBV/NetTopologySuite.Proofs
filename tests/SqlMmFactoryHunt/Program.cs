// SqlMmFactoryHunt — factory emit vs C# WktIntakeWalker μ (Red / Green / Refactor).
// House style: .NET console like tests/CurveOracleBugHunt; factory stays Java;
// intake is tools/WktIntakeWalker (dotnet run / built exe), not archived Java.
//
// Red  : locked catalog ids, famous water/land LINESTRING endpoints (hardcoded;
//        does not land #746), GEODESICSTRING → same MkChord bag, EMPTY/singleton
//        Decline, collinear CIRCULARSTRING → ID_Collinear.
// Green: random budget after pins.
//
// Verdicts: OK / INTERESTING / DIVERGE / BUG + SUMMARY line.
// No new ADR-0006 keyword. Rocq emit stays QEX (ticket_sqlmm_factory_emit_qed_or_qex).
//
// Assisted-by: Cursor Grok 4.6. claimId: none (tools).

using System.Globalization;

static class Program
{
    static int Main(string[] args)
    {
        int budget = 300, seed = 42;
        bool pinsOnly = false;
        for (int i = 0; i < args.Length; i++)
        {
            switch (args[i])
            {
                case "--budget" or "-Budget" when i + 1 < args.Length:
                    budget = int.Parse(args[++i], CultureInfo.InvariantCulture);
                    break;
                case "--seed" or "-Seed" when i + 1 < args.Length:
                    seed = int.Parse(args[++i], CultureInfo.InvariantCulture);
                    break;
                case "--pins-only":
                    pinsOnly = true;
                    break;
                case "-h" or "--help":
                    Console.WriteLine("SqlMmFactoryHunt — factory emit vs intake μ");
                    Console.WriteLine("  --budget N     random trials after pins (default 300)");
                    Console.WriteLine("  --seed N       RNG seed (default 42)");
                    Console.WriteLine("  --pins-only    Red pins only");
                    Console.WriteLine("Env: SQLMM_FACTORY_CP SQLMM_INTAKE SQLMM_FACTORY_TEMPLATES");
                    Console.WriteLine("     SQLMM_INTAKE = WktIntakeWalker.dll | exe | .csproj");
                    Console.WriteLine("Or:  pwsh tests/SqlMmFactoryHunt/hunt.ps1 -Budget 300 -Seed 42");
                    Console.WriteLine("     dotnet cake --target=SqlMmFactoryHunt");
                    Console.WriteLine("     dotnet cake --target=WktIntakeWalker");
                    return 0;
                default:
                    Console.Error.WriteLine($"unknown arg: {args[i]}");
                    return 2;
            }
        }

        Console.WriteLine("# SqlMmExampleFactory adversarial hunter (.NET / RGR)");
        Console.WriteLine($"# seed={seed} budget={budget}");
        Console.WriteLine("# Red: pins · Green: random budget · factory stays Java");
        Console.WriteLine("# intake: C# tools/WktIntakeWalker CLI (not archived Java)");
        Console.WriteLine("# no new ADR-0006 keyword; Rocq emit QEX");
        Console.WriteLine();

        HuntHost.EnsureReady();
        var counts = new Counts();

        Console.WriteLine("## RED (pins)");
        Pins.Run(counts);

        if (!pinsOnly)
        {
            Console.WriteLine();
            Console.WriteLine("## GREEN (random)");
            var rng = new Random(seed);
            for (int i = 0; i < budget; i++)
            {
                var m = Synth.Next(rng, i);
                string tag = $"trial:{i:D4}:{m.Keyword.ToLowerInvariant()}";
                if (m.Note.Length > 0)
                    tag += $":{m.Note}";
                Classify.RunModel(m, counts, tag);
            }
        }

        Console.WriteLine();
        Console.WriteLine(
            $"SUMMARY ok={counts.Ok} interesting={counts.Interesting} " +
            $"diverge={counts.Diverge} bug={counts.Bug} seed={seed} budget={budget}");
        return counts.Bug == 0 ? 0 : 1;
    }
}

static class Pins
{
    internal static void Run(Counts counts)
    {
        foreach (var id in HuntHost.CatalogIds())
            Classify.RunCatalogPin(id, counts);

        Classify.RunModel(Wire.FinishLs("famous-water", Wire.FamousWater), counts, "pin:famous-water:ls");
        Classify.RunModel(Wire.FinishLs("famous-land", Wire.FamousLand), counts, "pin:famous-land:ls");

        string wktW = $"GEODESICSTRING ({Wire.FmtPt(Wire.FamousWater[0])}, {Wire.FmtPt(Wire.FamousWater[1])})";
        string wktL = $"GEODESICSTRING ({Wire.FmtPt(Wire.FamousLand[0])}, {Wire.FmtPt(Wire.FamousLand[1])})";
        Classify.RunIntakeOnly("pin:famous-water:geodesicstring", wktW,
            Wire.FinishLs("famous-water-g", Wire.FamousWater, geodesic: true), counts);
        Classify.RunIntakeOnly("pin:famous-land:geodesicstring", wktL,
            Wire.FinishLs("famous-land-g", Wire.FamousLand, geodesic: true), counts);

        Classify.RunModel(Wire.FinishLs("empty-ls", []), counts, "pin:empty:linestring");
        Classify.RunModel(Wire.FinishPoint("empty-pt", null), counts, "pin:empty:point");
        Classify.RunModel(Wire.FinishCs("empty-cs", [], empty: true), counts, "pin:empty:circularstring");
        Classify.RunModel(Wire.FinishLs("singleton-ls", [new(0, 0)]), counts, "pin:singleton:linestring");
        Classify.RunIntakeOnly("pin:singleton:geodesicstring", "GEODESICSTRING (0 0)",
            new Model
            {
                Mid = "g-sing",
                Keyword = "LINESTRING",
                ExpectKind = "DECLINE",
                ExpectDecline = "ID_BadPointCount",
                Hold = true,
            }, counts);
        Classify.RunIntakeOnly("pin:empty:geodesicstring", "GEODESICSTRING EMPTY",
            new Model
            {
                Mid = "g-empty",
                Keyword = "LINESTRING",
                ExpectKind = "DECLINE",
                ExpectDecline = "ID_Empty",
                Hold = true,
            }, counts);

        Classify.RunModel(
            Wire.FinishCs("collinear-cs", [new(0, 0), new(1, 0), new(2, 0)]),
            counts, "pin:collinear-cs");
    }
}

static class Synth
{
    internal static Model Next(Random rng, int i)
    {
        string[] kinds =
        [
            "POINT", "LINESTRING", "LINESTRING", "CIRCULARSTRING", "CIRCULARSTRING",
            "CIRCLE", "COMPOUNDCURVE", "CLOTHOID", "GEODESIC_AS_LS",
        ];
        string k = kinds[rng.Next(kinds.Length)];
        string mid = $"synth-{i:D4}";
        if (k == "POINT")
            return Wire.FinishPoint(mid, RandXy(rng));
        if (k == "LINESTRING")
        {
            int n = new[] { 2, 2, 3, 4 }[rng.Next(4)];
            var pts = new List<Xy> { RandXy(rng) };
            while (pts.Count < n)
            {
                var p = RandXy(rng);
                if (!Wire.SameXy(p, pts[^1]))
                    pts.Add(p);
            }
            return Wire.FinishLs(mid, pts);
        }
        if (k == "GEODESIC_AS_LS")
            return Wire.FinishLs(mid, DistinctPair(rng), geodesic: true);
        if (k == "CIRCULARSTRING")
        {
            if (rng.NextDouble() < 0.15)
                return Wire.FinishCs(mid, [new(0, 0), new(1, 0), new(2, 0)]);
            if (rng.NextDouble() < 0.1)
                return Wire.FinishCs(mid, Wire.LockedCsQuarter);
            if (rng.NextDouble() < 0.08)
                return Wire.FinishCs(mid, Wire.LockedCsFull);
            int nArcs = rng.NextDouble() < 2.0 / 3.0 ? 1 : 2;
            if (nArcs == 1)
                return Wire.FinishCs(mid, NoncollinearTriple(rng));
            var t1 = NoncollinearTriple(rng);
            var t2 = NoncollinearTriple(rng);
            t2[0] = t1[2];
            if (Wire.TryTriple(t2[0], t2[1], t2[2]) is null)
                return Wire.FinishCs(mid, [t1[0], t1[1], t1[2], t2[1], t2[2]]);
            return Wire.FinishCs(mid, t1);
        }
        if (k == "CIRCLE")
        {
            if (rng.NextDouble() < 0.12)
                return Wire.FinishCircle(mid, Wire.LockedCircle);
            return Wire.FinishCircle(mid, NoncollinearTriple(rng));
        }
        if (k == "CLOTHOID")
            return Wire.FinishClothoidJts(mid);
        var ls = DistinctPair(rng);
        var cs = NoncollinearTriple(rng);
        cs[0] = ls[^1];
        if (Wire.TryTriple(cs[0], cs[1], cs[2]) != null)
        {
            cs = [ls[^1], new(ls[^1].X + 2, ls[^1].Y + 1), new(ls[^1].X, ls[^1].Y + 3)];
            if (Wire.TryTriple(cs[0], cs[1], cs[2]) != null)
                cs = [ls[^1], new(ls[^1].X + 2, ls[^1].Y), new(ls[^1].X + 3, ls[^1].Y + 1)];
        }
        return Wire.FinishCompound(mid, ls, cs);
    }

    static Xy RandXy(Random rng)
    {
        int kind = rng.Next(4); // int, int, frac, wide  (Python: two "int")
        if (kind <= 1)
            return new(rng.Next(-20, 21), rng.Next(-20, 21));
        if (kind == 2)
        {
            double[] xs = [0.5, 1.5, 2.25, -0.25, 3.125];
            double[] ys = [0.0, 1.0, -1.5, 4.5];
            return new(xs[rng.Next(xs.Length)], ys[rng.Next(ys.Length)]);
        }
        return new(rng.Next(-200, 201), rng.Next(-80, 81));
    }

    static List<Xy> DistinctPair(Random rng)
    {
        for (int i = 0; i < 20; i++)
        {
            var a = RandXy(rng);
            var b = RandXy(rng);
            if (!Wire.SameXy(a, b))
                return [a, b];
        }
        return [new(0, 0), new(2, 0)];
    }

    static List<Xy> NoncollinearTriple(Random rng)
    {
        for (int i = 0; i < 40; i++)
        {
            var a = RandXy(rng);
            var b = RandXy(rng);
            var c = RandXy(rng);
            if (Wire.TryTriple(a, b, c) is null)
                return [a, b, c];
        }
        return [new(0, 0), new(2, 0), new(3, 1)];
    }
}

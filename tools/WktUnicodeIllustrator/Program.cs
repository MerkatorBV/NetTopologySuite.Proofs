using System.Text;

namespace WktUnicodeIllustrator;

/// <summary>
/// CLI: illustrate two WKT geometries (A blue, B red) as ANSI-coloured Unicode art,
/// overshoot/self-overlap in maroon/navy, operation result in green.
/// </summary>
internal static class Program
{
    private static int Main(string[] args)
    {
        Console.OutputEncoding = Encoding.UTF8;

        Options opts;
        try
        {
            opts = Options.Parse(args);
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine(ex.Message);
            return 2;
        }

        if (opts.Help)
        {
            PrintHelp();
            return 0;
        }

        bool useColor = opts.ForceColor
            || (opts.Color && !Console.IsOutputRedirected);

        string? wktA = opts.WktA;
        string? wktB = opts.WktB;
        if (opts.DemoOvershoot)
        {
            wktA ??= CaseIllustrator.DefaultOvershootA;
            wktB ??= CaseIllustrator.DefaultOvershootB;
        }
        else if (opts.DemoCurve)
        {
            wktA ??= CaseIllustrator.DefaultCurveA;
            wktB ??= CaseIllustrator.DefaultCurveB;
        }

        var result = CaseIllustrator.Render(
            wktA: wktA,
            wktB: wktB,
            operation: opts.Operation,
            width: opts.Width,
            height: opts.Height,
            useColor: useColor,
            showOvershoot: opts.ShowOvershoot);

        if (result.ExitCode != 0)
        {
            Console.Error.Write(result.Text);
            return result.ExitCode;
        }

        Console.Write(result.Text);
        return 0;
    }

    private static void PrintHelp()
    {
        Console.WriteLine("""
            WktUnicodeIllustrator — ANSI-coloured Unicode sketches of WKT cases

            Usage:
              dotnet run --project tools/WktUnicodeIllustrator -- [options] [WKT_A] [WKT_B]

            Arguments:
              WKT_A, WKT_B   Geometries in OGC WKT (default: crossing diagonals)

            Options:
              --op <name>        intersection | union | difference | symdifference | none
              --demo curve       CIRCULARSTRING × CIRCULARSTRING crossing
              --demo overshoot   self-overlapping CIRCULARSTRINGs (retrace arcs)
              --no-overshoot     skip maroon/navy self-overlap layers
              --width N          grid width  (default: 41)
              --height N         grid height (default: 21)
              --no-color         plain Unicode, no ANSI escapes
              --force-color      emit ANSI even when stdout is redirected
              -h, --help         this help

            Colours:
              A = blue, B = red, result = green, A∩B = magenta
              A-overshoot (self-overlap) = maroon
              B-overshoot (self-overlap) = navy

            Overshoot: non-adjacent edge intersections after linearization — e.g. a
            CIRCULARSTRING whose second arc reverses the first (same mid control).

            Requires the local curve-aware NetTopologySuite clone for CIRCULARSTRING.

            Exit codes:
              0  ok
              2  bad arguments, WKT parse failure, or empty geometry
              3  overshoot extraction or overlay operation failed
              4  curve WKT given, but this build has no curve support (NuGet
                 fallback; no chord approximation is rendered, by design)

            Examples:
              dotnet run --project tools/WktUnicodeIllustrator -- --demo overshoot
              dotnet run --project tools/WktUnicodeIllustrator -- --demo curve
              dotnet run --project tools/WktUnicodeIllustrator -- --force-color --demo overshoot
            """);
    }

    private sealed class Options
    {
        public string? WktA { get; init; }
        public string? WktB { get; init; }
        public string Operation { get; init; } = "intersection";
        public int Width { get; init; } = 41;
        public int Height { get; init; } = 21;
        public bool Color { get; init; } = true;
        public bool ForceColor { get; init; }
        public bool DemoCurve { get; init; }
        public bool DemoOvershoot { get; init; }
        public bool ShowOvershoot { get; init; } = true;
        public bool Help { get; init; }

        public static Options Parse(string[] args)
        {
            string? a = null, b = null, op = "intersection";
            int w = 41, h = 21;
            bool color = true, forceColor = false, help = false;
            bool demoCurve = false, demoOvershoot = false, showOvershoot = true;

            for (int i = 0; i < args.Length; i++)
            {
                string s = args[i];
                switch (s)
                {
                    case "-h" or "--help":
                        help = true;
                        break;
                    case "--no-color":
                        color = false;
                        forceColor = false;
                        break;
                    case "--force-color" or "--color":
                        forceColor = true;
                        color = true;
                        break;
                    case "--no-overshoot":
                        showOvershoot = false;
                        break;
                    case "--demo" when i + 1 < args.Length:
                        {
                            string which = args[++i];
                            if (which.Equals("curve", StringComparison.OrdinalIgnoreCase)
                                || which.Equals("curves", StringComparison.OrdinalIgnoreCase)
                                || which.Equals("arc", StringComparison.OrdinalIgnoreCase))
                                demoCurve = true;
                            else if (which.Equals("overshoot", StringComparison.OrdinalIgnoreCase)
                                     || which.Equals("self", StringComparison.OrdinalIgnoreCase)
                                     || which.Equals("overlap", StringComparison.OrdinalIgnoreCase))
                                demoOvershoot = true;
                            else
                                throw new ArgumentException($"Unknown demo '{which}' (try: curve | overshoot).");
                            break;
                        }
                    case "--curve" or "--curves":
                        demoCurve = true;
                        break;
                    case "--overshoot":
                        demoOvershoot = true;
                        break;
                    case "--op" when i + 1 < args.Length:
                        op = args[++i];
                        break;
                    case "--width" when i + 1 < args.Length:
                        w = int.Parse(args[++i]);
                        break;
                    case "--height" when i + 1 < args.Length:
                        h = int.Parse(args[++i]);
                        break;
                    default:
                        if (s.StartsWith('-'))
                            throw new ArgumentException($"Unknown option: {s}");
                        if (a is null) a = s;
                        else if (b is null) b = s;
                        else throw new ArgumentException("Too many positional arguments (expected WKT_A WKT_B).");
                        break;
                }
            }

            return new Options
            {
                WktA = a,
                WktB = b,
                Operation = op,
                Width = w,
                Height = h,
                Color = color,
                ForceColor = forceColor,
                DemoCurve = demoCurve,
                DemoOvershoot = demoOvershoot,
                ShowOvershoot = showOvershoot,
                Help = help,
            };
        }
    }
}

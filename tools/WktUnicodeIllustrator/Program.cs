using System.Text;

namespace WktUnicodeIllustrator;

/// <summary>
/// MVP CLI: illustrate two WKT geometries (A blue, B red) as ANSI-coloured Unicode art,
/// then overlay an operation result in green. First case: simple line–line crossing
/// with the intersection point as the green result.
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

        // Default: color on interactive TTYs; off when redirected (unless --force-color).
        bool useColor = opts.ForceColor
            || (opts.Color && !Console.IsOutputRedirected);

        var result = CaseIllustrator.Render(
            wktA: opts.WktA,
            wktB: opts.WktB,
            operation: opts.Operation,
            width: opts.Width,
            height: opts.Height,
            useColor: useColor);

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
              --op <name>      intersection | union | difference | symdifference | none
                               aliases: cross, x → intersection (default: intersection)
              --width N        grid width  (default: 41)
              --height N       grid height (default: 21)
              --no-color       plain Unicode, no ANSI escapes
              --force-color    emit ANSI even when stdout is redirected
              -h, --help       this help

            Colours:
              A = blue, B = red, operation result = green
              pixels that are both A and B (before result paint) = magenta

            Default MVP (simple line–line crossing):
              A = LINESTRING (0 0, 10 10)
              B = LINESTRING (0 10, 10 0)
              op = intersection  →  POINT (5 5) in green

            Examples:
              dotnet run --project tools/WktUnicodeIllustrator
              dotnet run --project tools/WktUnicodeIllustrator -- --no-color
              dotnet run --project tools/WktUnicodeIllustrator -- --force-color
              dotnet run --project tools/WktUnicodeIllustrator -- ^
                "LINESTRING (0 0, 4 0)" "LINESTRING (2 -2, 2 2)"
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
        public bool Help { get; init; }

        public static Options Parse(string[] args)
        {
            string? a = null, b = null, op = "intersection";
            int w = 41, h = 21;
            bool color = true, forceColor = false, help = false;

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
                Help = help,
            };
        }
    }
}

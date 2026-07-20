// SPDX-License-Identifier: BSD-3-Clause
// AI-drafted, human-reviewed.  Assisted-by: Claude (Fable 5)

using System.Globalization;

namespace NetTopologySuite.Tests.Proofs.XUnit.Support;

/// <summary>
/// Locates and parses the proof-derived vector files in this repository's
/// <c>oracle/</c> directory. Every vector consumed here is pinned to a
/// Qed-closed Rocq theorem (see the provenance header of each file).
/// </summary>
public static class OracleVectors
{
    private static readonly Lazy<string> _oracleDirectory = new(FindOracleDirectory);

    /// <summary>The absolute path of the repository's <c>oracle/</c> directory.</summary>
    public static string OracleDirectory => _oracleDirectory.Value;

    /// <summary>Reads all lines of an oracle vector file.</summary>
    public static string[] ReadLines(string fileName)
        => File.ReadAllLines(Path.Combine(OracleDirectory, fileName));

    private static string FindOracleDirectory()
    {
        // Walk up from the test assembly until the repository root (identified
        // by the _CoqProject marker next to oracle/) is found.
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory != null)
        {
            if (File.Exists(Path.Combine(directory.FullName, "_CoqProject"))
                && Directory.Exists(Path.Combine(directory.FullName, "oracle")))
            {
                return Path.Combine(directory.FullName, "oracle");
            }
            directory = directory.Parent;
        }

        throw new DirectoryNotFoundException(
            "Could not locate the repository's oracle/ directory above " + AppContext.BaseDirectory);
    }

    /// <summary>
    /// Parses a numeric token of an oracle vector: either an ordinary decimal
    /// literal or a C99 hexadecimal float literal such as <c>0x1p+512</c> or
    /// <c>-0x1.28d037548c24ap+0</c> (the exact-binary64 notation the oracle
    /// emits so that no decimal rounding sits between the proof and the test).
    /// </summary>
    public static double ParseNumber(string token)
    {
        bool negative = token.StartsWith('-');
        string t = negative ? token.Substring(1) : token;

        double value;
        if (t.StartsWith("0x", StringComparison.OrdinalIgnoreCase))
        {
            value = ParseHexFloat(t);
        }
        else
        {
            value = double.Parse(t, CultureInfo.InvariantCulture);
        }

        return negative ? -value : value;
    }

    private static double ParseHexFloat(string t)
    {
        // 0x H [. HHHH] p [+|-] DDD  -- mantissas emitted by the oracle carry at
        // most 53 significant bits, so the ulong accumulation below is exact.
        int pIndex = t.IndexOfAny(new[] { 'p', 'P' });
        if (pIndex < 0)
            throw new FormatException("Hexadecimal float without exponent: " + t);

        string mantissa = t.Substring(2, pIndex - 2);
        int exponent = int.Parse(t.Substring(pIndex + 1), CultureInfo.InvariantCulture);

        int dotIndex = mantissa.IndexOf('.');
        string digits = dotIndex < 0 ? mantissa : mantissa.Remove(dotIndex, 1);
        int fractionDigits = dotIndex < 0 ? 0 : mantissa.Length - dotIndex - 1;

        ulong bits = 0;
        foreach (char c in digits)
        {
            bits = bits * 16 + (ulong)Convert.ToInt32(c.ToString(), 16);
        }

        return Math.ScaleB(bits, exponent - 4 * fractionDigits);
    }
}

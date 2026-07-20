// SPDX-License-Identifier: BSD-3-Clause
// AI-drafted, human-reviewed.  Assisted-by: Claude (Fable 5)

using NetTopologySuite.Algorithm;
using NetTopologySuite.Geometries;
using NetTopologySuite.Tests.Proofs.XUnit.Support;

namespace NetTopologySuite.Tests.Proofs.XUnit;

/// <summary>
/// Validates <see cref="Orientation.Index"/> against the Rocq-certified
/// orientation vectors in <c>oracle/orientation_proof_vectors.txt</c>.
/// </summary>
/// <remarks>
/// Provenance: <c>theories-flocq/Orient_b64_exact_full.v</c>
/// (<c>b64_orient2d_exact_sound</c>, Qed). The file carries two kinds of
/// vectors:
/// <list type="bullet">
/// <item>vectors every correct orientation predicate must satisfy
/// (<see cref="NtsAgreesWithProvenSign"/>), and</item>
/// <item>vectors annotated <c>-- WRONG</c>, where the proofs show that pure
/// double-double expansion arithmetic over/underflows to a wrong ZERO. NTS's
/// <see cref="Orientation.Index"/> is a composed pipeline (fast filter, then
/// <c>CGAlgorithmsDD</c>), and empirically the two bands behave differently:
/// in the <b>overflow</b> band (~2^512) the filter's determinant saturates to
/// ±infinity, whose sign is still correct, so NTS agrees with the proven sign
/// and those vectors run in the agreement group; in the <b>underflow</b> band
/// (~2^-540) the products flush to zero and NTS returns the documented wrong
/// ZERO, pinned by <see cref="NtsDivergesWhereDoubleDoubleUnderflows"/>. If NTS
/// ever starts returning the proven sign there, the pin fails loudly so the
/// vector can be promoted to the agreement group.</item>
/// </list>
/// </remarks>
public class OrientationProofVectorTests
{
    private const string FileName = "orientation_proof_vectors.txt";

    public static TheoryData<string, double, double, double, double, double, double, int> AgreementVectors
        => LoadVectors(divergent: false);

    public static TheoryData<string, double, double, double, double, double, double, int> DivergenceVectors
        => LoadVectors(divergent: true);

    [Theory]
    [MemberData(nameof(AgreementVectors))]
    public void NtsAgreesWithProvenSign(string description, double x0, double y0, double x1, double y1, double x2, double y2, int expectedSign)
    {
        int actual = (int)Orientation.Index(new Coordinate(x0, y0), new Coordinate(x1, y1), new Coordinate(x2, y2));

        Assert.True(expectedSign == actual,
            $"[{description}] proven sign {expectedSign}, NTS Orientation.Index returned {actual}.");
    }

    [Theory]
    [MemberData(nameof(DivergenceVectors))]
    public void NtsDivergesWhereDoubleDoubleUnderflows(string description, double x0, double y0, double x1, double y1, double x2, double y2, int provenSign)
    {
        int actual = (int)Orientation.Index(new Coordinate(x0, y0), new Coordinate(x1, y1), new Coordinate(x2, y2));

        Assert.True(provenSign != actual,
            $"[{description}] NTS now returns the proven sign {provenSign} — the documented underflow "
            + "divergence no longer reproduces. Move this vector to the agreement group.");
        Assert.True(actual == 0,
            $"[{description}] expected the documented wrong ZERO from underflowing products, got {actual}.");
    }

    private static TheoryData<string, double, double, double, double, double, double, int> LoadVectors(bool divergent)
    {
        var data = new TheoryData<string, double, double, double, double, double, double, int>();
        foreach (string rawLine in OracleVectors.ReadLines(FileName))
        {
            string line = rawLine.Trim();
            if (line.Length == 0 || line.StartsWith('#'))
                continue;

            int hash = line.IndexOf('#');
            string comment = hash < 0 ? "" : line.Substring(hash + 1).Trim();
            string payload = (hash < 0 ? line : line.Substring(0, hash)).Trim();

            // "-- WRONG" documents where pure double-double arithmetic fails; NTS
            // only actually diverges in the underflow band (see class remarks).
            bool isDivergent = comment.EndsWith("-- WRONG", StringComparison.Ordinal)
                && comment.Contains("underflow", StringComparison.OrdinalIgnoreCase);
            if (isDivergent != divergent)
                continue;

            string[] parts = payload.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            Assert.Equal(7, parts.Length);

            int expected = parts[6] switch
            {
                "POS" => 1,
                "NEG" => -1,
                "ZERO" => 0,
                _ => throw new FormatException("Unexpected verdict: " + parts[6]),
            };

            data.Add(
                comment.Length == 0 ? payload : comment,
                OracleVectors.ParseNumber(parts[0]), OracleVectors.ParseNumber(parts[1]),
                OracleVectors.ParseNumber(parts[2]), OracleVectors.ParseNumber(parts[3]),
                OracleVectors.ParseNumber(parts[4]), OracleVectors.ParseNumber(parts[5]),
                expected);
        }

        return data;
    }
}

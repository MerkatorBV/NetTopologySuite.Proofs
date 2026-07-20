// SPDX-License-Identifier: BSD-3-Clause
// AI-drafted, human-reviewed.  Assisted-by: Claude (Fable 5)

using NetTopologySuite.IO;
using NetTopologySuite.Tests.Proofs.XUnit.Support;

namespace NetTopologySuite.Tests.Proofs.XUnit;

/// <summary>
/// Validates <c>Geometry.Relate</c> against the line–line DE-9IM vectors in
/// <c>oracle/de9im_line_line_vectors.txt</c>.
/// </summary>
/// <remarks>
/// The vectors seed from Romanschek et al. (IJGI 2021,
/// doi:10.3390/ijgi10110715) and are pinned in Coq by
/// <c>theories/RelateLineLine.v</c> (<c>ll_matrix_paper_test*</c>, Qed) —
/// each MATRIX line is the full geometry-derived DE-9IM matrix, so
/// <c>a.Relate(b)</c> must reproduce it cell for cell.
/// </remarks>
public class De9ImLineLineVectorTests
{
    private const string FileName = "de9im_line_line_vectors.txt";

    public static TheoryData<string, string, string, string> Vectors
    {
        get
        {
            var data = new TheoryData<string, string, string, string>();

            string? test = null, wktA = null, wktB = null;
            foreach (string rawLine in OracleVectors.ReadLines(FileName))
            {
                string line = rawLine.Trim();
                if (line.StartsWith("TEST ", StringComparison.Ordinal))
                    test = line.Substring(5).Trim();
                else if (line.StartsWith("WKT_A ", StringComparison.Ordinal))
                    wktA = line.Substring(6).Trim();
                else if (line.StartsWith("WKT_B ", StringComparison.Ordinal))
                    wktB = line.Substring(6).Trim();
                else if (line.StartsWith("MATRIX ", StringComparison.Ordinal))
                {
                    Assert.NotNull(test);
                    Assert.NotNull(wktA);
                    Assert.NotNull(wktB);
                    data.Add(test, wktA, wktB, line.Substring(7).Trim());
                    test = wktA = wktB = null;
                }
            }

            Assert.NotEmpty(data);
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(Vectors))]
    public void RelateReproducesProvenMatrix(string test, string wktA, string wktB, string expectedMatrix)
    {
        var reader = new WKTReader();
        var a = reader.Read(wktA);
        var b = reader.Read(wktB);

        string actual = a.Relate(b).ToString();

        Assert.True(expectedMatrix == actual,
            $"[paper test {test}] proven DE-9IM matrix {expectedMatrix}, NTS Relate returned {actual}.");
    }
}

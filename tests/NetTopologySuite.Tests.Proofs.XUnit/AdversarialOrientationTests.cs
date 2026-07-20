// SPDX-License-Identifier: BSD-3-Clause
// AI-drafted, human-reviewed.  Assisted-by: Claude (Fable 5)

using System.Text.RegularExpressions;
using NetTopologySuite.Algorithm;
using NetTopologySuite.Geometries;
using NetTopologySuite.Tests.Proofs.XUnit.Support;

namespace NetTopologySuite.Tests.Proofs.XUnit;

/// <summary>
/// Validates <see cref="Orientation.Index"/> against the near-collinear
/// product-collision family of <c>oracle/adversarial_tests.txt</c> (section A):
/// P = (0,0), (2^k+1, 2^k+2), (2^k, 2^k+1), whose true orientation is POS
/// (exact determinant 1) for every k, while the naive double determinant
/// rounds to ZERO from k = 27 on.
/// </summary>
/// <remarks>
/// The exact verdicts come from the RocqRefRunner exact oracle (ground truth;
/// see the file header). NTS's <see cref="Orientation.Index"/> uses
/// double-double expansion arithmetic, which stays exact in this coordinate
/// range — these vectors demonstrate it agreeing with the proofs precisely
/// where a naive implementation is provably wrong.
/// </remarks>
public class AdversarialOrientationTests
{
    private const string FileName = "adversarial_tests.txt";

    public static TheoryData<int> NearCollinearExponents
    {
        get
        {
            var data = new TheoryData<int>();
            var pattern = new Regex(@"^k=(\d+) coord=2\^\d+ .* EXACT=POS", RegexOptions.None);
            foreach (string rawLine in OracleVectors.ReadLines(FileName))
            {
                var match = pattern.Match(rawLine.Trim());

                // Section C (in-circle overflow) has no "coord=" token, so this
                // pattern only ever selects section A.
                if (match.Success)
                {
                    data.Add(int.Parse(match.Groups[1].Value));
                }
            }

            Assert.NotEmpty(data);
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(NearCollinearExponents))]
    public void NtsMatchesExactOracleWhereNaiveDoublesFail(int k)
    {
        double c = Math.ScaleB(1, k);
        var p0 = new Coordinate(0, 0);
        var p1 = new Coordinate(c + 1, c + 2);
        var p2 = new Coordinate(c, c + 1);

        // The naive double determinant is provably ZERO here (that is what makes
        // the vector adversarial); the exact determinant is +1.
        double naive = (p1.X - p0.X) * (p2.Y - p0.Y) - (p1.Y - p0.Y) * (p2.X - p0.X);
        Assert.Equal(0, naive);

        Assert.Equal(OrientationIndex.CounterClockwise, Orientation.Index(p0, p1, p2));
    }
}

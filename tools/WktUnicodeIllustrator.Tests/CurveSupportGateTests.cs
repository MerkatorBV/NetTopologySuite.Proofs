using WktUnicodeIllustrator;
using Xunit;

namespace WktUnicodeIllustrator.Tests;

/// <summary>
/// The lines-only (NuGet fallback) build must refuse curve WKT with exit 4
/// rather than silently rendering control chords. In curve-aware builds the
/// same inputs render normally — both legs are asserted from one test suite.
/// </summary>
public class CurveSupportGateTests
{
    [Theory]
    [InlineData("CIRCULARSTRING (0 0, 5 8, 10 0)")]
    [InlineData("circularstring (0 0, 5 8, 10 0)")]
    [InlineData("COMPOUNDCURVE (CIRCULARSTRING (0 0, 1 1, 2 0), (2 0, 4 0))")]
    [InlineData("CURVEPOLYGON (CIRCULARSTRING (0 0, 2 2, 4 0, 2 -2, 0 0))")]
    [InlineData("MULTICURVE ((0 0, 1 1))")]
    [InlineData("MULTISURFACE (((0 0, 1 0, 1 1, 0 0)))")]
    public void Curve_wkt_keywords_are_detected(string wkt)
    {
        Assert.True(GeometryCurves.ContainsCurveWkt(wkt));
    }

    [Theory]
    [InlineData("LINESTRING (0 0, 10 10)")]
    [InlineData("POLYGON ((0 0, 1 0, 1 1, 0 0))")]
    [InlineData("MULTILINESTRING ((0 0, 1 1))")]
    public void Linear_wkt_is_not_flagged_as_curve(string wkt)
    {
        Assert.False(GeometryCurves.ContainsCurveWkt(wkt));
    }

    [Fact]
    public void Curve_wkt_renders_in_curve_builds_and_exits_4_in_lines_only_builds()
    {
        var r = CaseIllustrator.Render(
            wktA: CaseIllustrator.DefaultCurveA,
            wktB: CaseIllustrator.DefaultCurveB,
            useColor: false);

        if (GeometryCurves.HasCurveSupport)
        {
            Assert.Equal(0, r.ExitCode);
        }
        else
        {
            Assert.Equal(4, r.ExitCode);
            Assert.NotNull(r.Error);
            Assert.Contains("curve-aware NetTopologySuite clone", r.Error);
        }
    }

    [Fact]
    public void Linear_wkt_is_unaffected_by_the_curve_gate()
    {
        var r = CaseIllustrator.Render(useColor: false);
        Assert.Equal(0, r.ExitCode);
    }
}

using Xunit;

namespace WktUnicodeIllustrator.Tests;

/// <summary>
/// A fact that only runs against the curve-aware NetTopologySuite clone;
/// skipped (not silently passed) in lines-only NuGet fallback builds.
/// </summary>
public sealed class CurveFactAttribute : FactAttribute
{
    public CurveFactAttribute()
    {
        if (!GeometryCurves.HasCurveSupport)
            Skip = "Requires the curve-aware NetTopologySuite clone (lines-only NuGet build; curve WKT exits 4).";
    }
}

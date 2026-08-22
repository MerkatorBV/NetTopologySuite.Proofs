using NetTopologySuite.Geometries;

namespace WktUnicodeIllustrator;

/// <summary>
/// The composed, drawable form of a Case: parsed inputs, the operation result,
/// overshoot extracts, and the fit of world coordinates onto an occupancy grid.
/// Produced by <see cref="CaseIllustrator.Compose"/>; consumed by <see cref="Style"/>.
/// </summary>
internal sealed class Scenario
{
    public required Geometry A { get; init; }
    public required Geometry B { get; init; }

    /// <summary>Operation result; null when the operation was skipped (--op none).</summary>
    public Geometry? Result { get; init; }

    public Geometry? OvershootA { get; init; }
    public Geometry? OvershootB { get; init; }
    public required bool ShowOvershoot { get; init; }

    /// <summary>Display name of the operation (may carry a "(linearized curves)" suffix).</summary>
    public required string OpName { get; init; }

    public required Canvas Canvas { get; init; }
    public required WorldToGrid Map { get; init; }
}

/// <summary>
/// Outcome of composition: a Scenario, or a failure carrying the CLI exit-code
/// contract (2 parse/empty · 3 overshoot/operation · 4 curve support).
/// </summary>
internal sealed class ComposeResult
{
    public Scenario? Scenario { get; private init; }
    public int ExitCode { get; private init; }
    public string? Error { get; private init; }

    public static ComposeResult Ok(Scenario scenario) => new() { Scenario = scenario };

    public static ComposeResult Fail(int exitCode, string error) =>
        new() { ExitCode = exitCode, Error = error };
}

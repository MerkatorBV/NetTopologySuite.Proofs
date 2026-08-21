namespace WktUnicodeIllustrator;

/// <summary>
/// Semantic colour role of a run. Printers map roles to device colours
/// (SGR codes, RGB); <see cref="Default"/> is unstyled text.
/// </summary>
internal enum DocColor
{
    Default,
    Dim,
    A,
    B,
    Result,
    /// <summary>A∩B coincidence (and coinciding overshoots).</summary>
    Both,
    OvershootA,
    OvershootB,
}

/// <summary>A contiguous piece of text carrying one colour role.</summary>
internal readonly record struct Run(string Text, DocColor Color = DocColor.Default);

/// <summary>
/// The device-independent styled text of a Scenario: lines of coloured runs
/// (header, legend, framed panels). What every Printer consumes.
/// </summary>
internal sealed class Doc
{
    public List<List<Run>> Lines { get; } = new();

    public void AddLine(params Run[] runs) => Lines.Add(new List<Run>(runs));

    public void AddLine(List<Run> runs) => Lines.Add(runs);

    public void AddBlank() => Lines.Add(new List<Run>());
}

// Thin Cake entry — house style (.NET / PowerShell / Cake / RGR).
// Target WktIntakeWalker invokes tools/WktIntakeWalker/smoke.ps1.
// claimId: none (tools). No new ADR-0006 keyword.
// Assisted-by: Cursor Grok 4.6.
//
// #748 (SqlMmFactoryHunt) is still open on a sibling branch. After that
// hunter lands, add/compose Task("SqlMmFactoryHunt") here and retarget
// JavaHost intake to this C# walker.

var target = Argument("target", "Default");

Task("WktIntakeWalker")
    .Does(() =>
{
    var script = MakeAbsolute(File("./tools/WktIntakeWalker/smoke.ps1"));
    if (!FileExists(script))
        throw new CakeException($"missing {script}");

    var shell = FindPwsh();
    var args = new ProcessArgumentBuilder()
        .Append("-NoProfile")
        .Append("-File").AppendQuoted(script.FullPath);

    var exit = StartProcess(shell, new ProcessSettings { Arguments = args });
    if (exit != 0)
        throw new CakeException($"WktIntakeWalker exited {exit}");
});

Task("Default")
    .Does(() =>
{
    Information("Targets: WktIntakeWalker");
    Information("  pwsh ./tools/WktIntakeWalker/smoke.ps1");
    Information("  dotnet cake --target=WktIntakeWalker");
    Information("  dotnet run --project tools/WktIntakeWalker -- \"LINESTRING (0 0, 2 0)\"");
    Information("Follow-up after #748 lands: retarget SqlMmFactoryHunt intake to this C# walker.");
});

RunTarget(target);

string FindPwsh()
{
    if (IsRunningOnWindows())
    {
        if (!string.IsNullOrEmpty(Which("pwsh")))
            return "pwsh";
        return "powershell";
    }
    foreach (var c in new[]
    {
        "pwsh",
        System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".local/pwsh/pwsh"),
        "/usr/bin/pwsh",
    })
    {
        if (c == "pwsh" && !string.IsNullOrEmpty(Which("pwsh")))
            return "pwsh";
        if (c != "pwsh" && FileExists(c))
            return c;
    }
    throw new CakeException("pwsh not found. Install PowerShell 7, or run tools/WktIntakeWalker/smoke.ps1 directly.");
}

string Which(string name)
{
    var path = Environment.GetEnvironmentVariable("PATH") ?? "";
    foreach (var dir in path.Split(System.IO.Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries))
    {
        var candidate = System.IO.Path.Combine(dir, name);
        if (FileExists(candidate))
            return candidate;
        if (IsRunningOnWindows() && FileExists(candidate + ".exe"))
            return candidate + ".exe";
    }
    return "";
}

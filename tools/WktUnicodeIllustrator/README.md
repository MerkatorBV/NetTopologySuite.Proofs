# WktUnicodeIllustrator

ANSI-coloured **Unicode sketches** of spatial cases from WKT.

| Layer | Colour | Meaning |
|-------|--------|---------|
| **A** | blue | first input geometry |
| **B** | red | second input geometry |
| **result** | green | operation output (default: intersection) |
| A∩B pixel | magenta | grid cell touched by both inputs (before result paint) |

MVP target: **simple line–line crossing** — two `LINESTRING`s, intersection drawn as a green point.

## Run

```powershell
# Default demo: diagonals of the 10×10 square crossing at (5 5)
dotnet run --project tools/WktUnicodeIllustrator

# Custom WKT + operation
dotnet run --project tools/WktUnicodeIllustrator -- `
  "LINESTRING (0 0, 10 10)" "LINESTRING (0 10, 10 0)" --op intersection

# Horizontal × vertical
dotnet run --project tools/WktUnicodeIllustrator -- `
  "LINESTRING (0 0, 4 0)" "LINESTRING (2 -2, 2 2)"

# No ANSI (CI logs / monochrome)
dotnet run --project tools/WktUnicodeIllustrator -- --no-color

# Force ANSI even when stdout is redirected (pipes / capture files)
dotnet run --project tools/WktUnicodeIllustrator -- --force-color

# Automated checks (same CaseIllustrator path as the CLI)
dotnet test tools/WktUnicodeIllustrator.Tests -c Release
```

Requires a UTF-8 terminal (Windows Terminal, modern PowerShell, or `chcp 65001`).

**Legend:** A = blue · B = red · operation result = green · A∩B pixel = magenta.

## How it works (MVP)

1. Parse A and B with NTS `WKTReader`.
2. Compute `A.Intersection(B)` (or another `--op`).
3. Fit a character grid to the joint envelope (aspect-preserving).
4. Rasterize linework with Bresenham + direction glyphs (`─ │ ╱ ╲`).
5. Print twice: inputs only, then with green result overlay.

Polygons and other types stroke their boundary as a fallback; richer fills are out of MVP scope.

## Layout

```
tools/WktUnicodeIllustrator/
  Program.cs                 CLI (parses args, prints CaseIllustrator output)
  CaseIllustrator.cs         pure WKT → framed Unicode report (CLI + tests)
  Canvas.cs                  layered character grid
  WorldToGrid.cs             envelope → col/row
  Rasterizer.cs              geometry → glyphs
  AnsiRenderer.cs            ANSI colour + frame
  WktUnicodeIllustrator.csproj
  README.md
tools/WktUnicodeIllustrator.Tests/
  DefaultCrossingTests.cs    structural asserts on the shipped path
```

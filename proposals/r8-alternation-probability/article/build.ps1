$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
  1..3 | ForEach-Object {
    & pdflatex -interaction=nonstopmode -halt-on-error forge-alternation-probability.tex
    if ($LASTEXITCODE -ne 0) { throw "pdfLaTeX failed with exit code $LASTEXITCODE" }
  }
} finally { Pop-Location }

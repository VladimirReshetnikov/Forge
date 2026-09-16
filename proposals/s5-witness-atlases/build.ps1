$ErrorActionPreference = 'Stop'
Push-Location (Join-Path $PSScriptRoot 'article')
try {
    & latexmk -pdf -interaction=nonstopmode -halt-on-error atlas.tex
    if ($LASTEXITCODE -ne 0) { throw "LaTeX build failed with exit code $LASTEXITCODE" }
}
finally { Pop-Location }

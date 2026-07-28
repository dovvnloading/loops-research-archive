$ErrorActionPreference = "Stop"

$paperDir = [System.IO.Path]::GetFullPath(
    (Split-Path -Parent $MyInvocation.MyCommand.Path)
)
$bundledTectonic = [System.IO.Path]::GetFullPath(
    (Join-Path $paperDir "..\..\research\mlc_unified\latex\tools\tectonic.exe")
)
$tectonicOverride = [Environment]::GetEnvironmentVariable("PAPER3_TECTONIC")
if ($tectonicOverride) {
    $tectonic = [System.IO.Path]::GetFullPath($tectonicOverride)
}
elseif (Test-Path -LiteralPath $bundledTectonic -PathType Leaf) {
    $tectonic = $bundledTectonic
}
else {
    $tectonicCommand = Get-Command tectonic -ErrorAction SilentlyContinue
    if ($null -eq $tectonicCommand) {
        throw ("Tectonic was not found. Install it, add it to PATH, or set " +
            "PAPER3_TECTONIC to the executable path.")
    }
    $tectonic = $tectonicCommand.Source
}
$buildDir = [System.IO.Path]::GetFullPath((Join-Path $paperDir "build_v2"))
$verifyDir = [System.IO.Path]::GetFullPath((Join-Path $paperDir "build_v2_verify"))
$releasePdf = Join-Path $paperDir "paper3_draft2.pdf"
$outputDir = [System.IO.Path]::GetFullPath((Join-Path $paperDir "output\pdf"))
$outputPdf = Join-Path $outputDir "protected_planar_carriers.pdf"

if (-not (Test-Path -LiteralPath $tectonic -PathType Leaf)) {
    throw "Tectonic executable not found at resolved path: $tectonic"
}

$pythonCommand = Get-Command python -ErrorAction Stop
$pythonExe = $pythonCommand.Source
& $pythonExe -c "import sys; assert sys.version_info >= (3, 10), sys.version"
if ($LASTEXITCODE -ne 0) {
    throw "Python 3.10 or newer is required"
}
& $pythonExe -c "import pypdf"
if ($LASTEXITCODE -ne 0) {
    throw "The release QA requires the pypdf package"
}

$env:SOURCE_DATE_EPOCH = "1785110400"
Write-Host "Python: $pythonExe"
& $pythonExe --version
Write-Host "Tectonic: $tectonic"
& $tectonic --version

New-Item -ItemType Directory -Path $buildDir -Force | Out-Null
New-Item -ItemType Directory -Path $verifyDir -Force | Out-Null
New-Item -ItemType Directory -Path $outputDir -Force | Out-Null

$generatedNames = @("main_v2.pdf", "main_v2.log", "main_v2.console.txt")
foreach ($directory in @($buildDir, $verifyDir)) {
    if (-not $directory.StartsWith($paperDir, [System.StringComparison]::OrdinalIgnoreCase)) {
        throw "Refusing to clean a build path outside the paper directory: $directory"
    }
    foreach ($name in $generatedNames) {
        $target = Join-Path $directory $name
        if (Test-Path -LiteralPath $target) {
            Remove-Item -LiteralPath $target -Force
        }
    }
}

Push-Location $paperDir
try {
    & $pythonExe assemble.py --skeleton skeleton_v2.tex --output main_v2.tex
    if ($LASTEXITCODE -ne 0) {
        throw "Assembly validation failed with exit code $LASTEXITCODE"
    }

    $nativeErrorPreference = $ErrorActionPreference
    $ErrorActionPreference = "Continue"
    try {
        $primaryConsole = Join-Path $buildDir "main_v2.console.txt"
        & $tectonic -X compile main_v2.tex --outdir $buildDir --keep-logs 2>&1 |
            Tee-Object -FilePath $primaryConsole
        $primaryExitCode = $LASTEXITCODE

        $verificationConsole = Join-Path $verifyDir "main_v2.console.txt"
        & $tectonic -X compile main_v2.tex --outdir $verifyDir --keep-logs 2>&1 |
            Tee-Object -FilePath $verificationConsole
        $verificationExitCode = $LASTEXITCODE
    }
    finally {
        $ErrorActionPreference = $nativeErrorPreference
    }
    if ($primaryExitCode -ne 0) {
        throw "Tectonic failed with exit code $primaryExitCode"
    }
    if ($verificationExitCode -ne 0) {
        throw "Reproducibility build failed with exit code $verificationExitCode"
    }

    foreach ($consoleLog in @($primaryConsole, $verificationConsole)) {
        if (Select-String -LiteralPath $consoleLog -Pattern '^warning: main_v2\.tex:' -Quiet) {
            throw "TeX emitted a source warning; inspect $consoleLog"
        }
    }

    $primaryPdf = Join-Path $buildDir "main_v2.pdf"
    $verificationPdf = Join-Path $verifyDir "main_v2.pdf"
    $primaryHash = (Get-FileHash -LiteralPath $primaryPdf -Algorithm SHA256).Hash
    $verificationHash = (Get-FileHash -LiteralPath $verificationPdf -Algorithm SHA256).Hash
    if ($primaryHash -ne $verificationHash) {
        throw "Clean builds are not byte-reproducible: $primaryHash != $verificationHash"
    }
    Write-Host "Reproducible PDF SHA256: $primaryHash"

    Copy-Item -LiteralPath $primaryPdf -Destination $releasePdf -Force
    Copy-Item -LiteralPath $primaryPdf -Destination $outputPdf -Force

    & $pythonExe qa_release.py
    if ($LASTEXITCODE -ne 0) {
        throw "Release QA failed with exit code $LASTEXITCODE"
    }
}
finally {
    Pop-Location
    foreach ($name in $generatedNames) {
        $target = Join-Path $verifyDir $name
        if (Test-Path -LiteralPath $target) {
            Remove-Item -LiteralPath $target -Force
        }
    }
    if ((Test-Path -LiteralPath $verifyDir -PathType Container) -and
        -not (Get-ChildItem -LiteralPath $verifyDir -Force)) {
        Remove-Item -LiteralPath $verifyDir -Force
    }
}

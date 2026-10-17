# Install a clotran release on Windows (x86_64), from PowerShell:
#
#   irm https://raw.githubusercontent.com/jborden/clotran/main/install.ps1 | iex
#
# It downloads the release zip, checks it against the release's SHA256SUMS,
# unpacks it into $env:LOCALAPPDATA\Programs\clotran (replacing what is
# there) and puts its bin on the user PATH. CLOTRAN_VERSION picks a release
# (default: the one this script was written for).
$ErrorActionPreference = 'Stop'
$version = if ($env:CLOTRAN_VERSION) { $env:CLOTRAN_VERSION } else { '1.0.0-rc.4' }
$base = if ($env:CLOTRAN_BASE_URL) { $env:CLOTRAN_BASE_URL } else { "https://github.com/jborden/clotran/releases/download/v$version" }
if ($env:PROCESSOR_ARCHITECTURE -ne 'AMD64') { throw "install.ps1: no release for $env:PROCESSOR_ARCHITECTURE (there is windows-x86_64)" }
[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12

$name = "clotran-$version-windows-x86_64"
$tmp = Join-Path ([IO.Path]::GetTempPath()) ([IO.Path]::GetRandomFileName())
New-Item -ItemType Directory $tmp | Out-Null
try {
  Write-Host "clotran $version for windows-x86_64"
  $web = New-Object Net.WebClient
  $web.DownloadFile("$base/$name.zip", "$tmp\$name.zip")
  $web.DownloadFile("$base/SHA256SUMS", "$tmp\SHA256SUMS")
  $want = (Get-Content "$tmp\SHA256SUMS" | Where-Object { $_ -match " \*?$([regex]::Escape("$name.zip"))$" } | ForEach-Object { ($_ -split ' ')[0] })
  if (-not $want) { throw "install.ps1: $name.zip is not in SHA256SUMS" }
  if ((Get-FileHash "$tmp\$name.zip" -Algorithm SHA256).Hash -ne $want.ToUpper()) { throw "install.ps1: $name.zip does not match its SHA256SUMS entry" }

  $home_ = Join-Path $env:LOCALAPPDATA 'Programs\clotran'
  Expand-Archive "$tmp\$name.zip" $tmp
  if (Test-Path $home_) { Remove-Item -Recurse -Force $home_ }
  New-Item -ItemType Directory (Split-Path $home_) -Force | Out-Null
  Move-Item "$tmp\$name" $home_
  $bin = "$home_\bin"
  $path = [Environment]::GetEnvironmentVariable('Path', 'User')
  if (($path -split ';') -notcontains $bin) {
    [Environment]::SetEnvironmentVariable('Path', ($(if ($path) { "$path;" }) + $bin), 'User')
    Write-Host "added $bin to the user PATH; open a new terminal to run it as clotran"
  }
  Write-Host "installed: $bin\clotran.cmd"
} finally {
  Remove-Item -Recurse -Force $tmp -ErrorAction SilentlyContinue
}

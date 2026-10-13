# check.ps1 -- a Windows release run on a real Windows machine, as
# scripts/dist-check runs the Linux ones in clean images: a program, a
# future, a Unicode regex, a deps.edn project with a :local/root library.
#
#   powershell -ExecutionPolicy Bypass -File check.ps1 clotran-...-windows-x86_64.zip
#
# Prints pass or FAIL for each, and exits 1 on any FAIL.
param([Parameter(Mandatory=$true)][string]$Zip)
# Continue, not Stop: under Windows PowerShell 5.1 a native command's
# stderr line would otherwise end the script rather than show as a FAIL
$ErrorActionPreference = "Continue"
# clotran writes UTF-8; read what it prints as UTF-8, not the console's code page
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$work = Join-Path $env:TEMP ("clotran-check-" + [guid]::NewGuid())
New-Item -ItemType Directory $work | Out-Null
Expand-Archive -Path $Zip -DestinationPath $work
$top = Get-ChildItem $work | Select-Object -First 1
$clotran = Join-Path $top.FullName "bin\clotran.cmd"
$bad = 0

function Check($name, $want, $got) {
  $g = ($got | Where-Object { $_ -notmatch '^note:' }) -join "`n"
  if ($g -ceq $want) { Write-Output "pass $name" }
  else { Write-Output "FAIL $name"; Write-Output "  want: $want"; Write-Output "  got:  $g"; $script:bad++ }
}

try {
$prog = Join-Path $work "p.cljf"
# UTF-8 with no byte-order mark (.NET's default), the accents as code
# points so this file reads the same under any code page
$hw = "h" + [char]0xE9 + "llo w" + [char]0xF6 + "rld"
function Put($path, $text) { [System.IO.File]::WriteAllText($path, $text) }
Put $prog ("(println (+ 1 2))`n(println @(future (reduce + (range 1000))))`n(println (re-seq #`"\p{L}+`" `"" + $hw + "`"))`n(shutdown-agents)`n")
Check "program, future, regex" "3`n499500`n($hw)" (& $clotran $prog 2>&1)

$lib = Join-Path $work "lib"; $app = Join-Path $work "app"
New-Item -ItemType Directory (Join-Path $lib "src\lib"), (Join-Path $app "src\app") | Out-Null
Put (Join-Path $lib "src\lib\core.cljf") "(ns lib.core)`n(defn twice [x] (* 2 x))"
Put (Join-Path $lib "deps.edn") '{:paths ["src"]}'
Put (Join-Path $app "src\app\main.cljf") "(ns app.main (:require [lib.core :as l]))`n(defn -main [] (println (l/twice 21)))"
$root = $lib.Replace('\', '/')
Put (Join-Path $app "deps.edn") "{:paths [`"src`"] :deps {local/lib {:local/root `"$root`"}}}"
Push-Location $app
Check "deps.edn project" "42" (& $clotran -m app.main 2>&1)
Pop-Location

} finally {
  Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}
if ($bad -gt 0) { exit 1 }

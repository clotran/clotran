#!/bin/sh
# Install a clotran release on macOS or Linux:
#
#   curl -fsSL https://raw.githubusercontent.com/jborden/clotran/main/install.sh | sh
#
# It picks the tarball for this machine (darwin-arm64; linux aarch64 or
# x86_64, glibc or musl), checks it against the release's SHA256SUMS,
# unpacks it under $PREFIX/lib/clotran-VERSION and writes the two commands
# into $PREFIX/bin. PREFIX defaults to ~/.local; CLOTRAN_VERSION picks a
# release (default: the one this script was written for).
set -eu

version=${CLOTRAN_VERSION:-1.0.0-rc.4}
prefix=${PREFIX:-$HOME/.local}
base=${CLOTRAN_BASE_URL:-https://github.com/jborden/clotran/releases/download/v$version}

die() { echo "install.sh: $*" >&2; exit 1; }

os=$(uname -s)
arch=$(uname -m)
case "$os-$arch" in
  Darwin-arm64) target=darwin-arm64 ;;
  Linux-aarch64|Linux-arm64) target=linux-aarch64 ;;
  Linux-x86_64|Linux-amd64) target=linux-x86_64 ;;
  *) die "no release for $os $arch (there are darwin-arm64, linux-aarch64, linux-x86_64; Windows: scoop)" ;;
esac
if [ "$os" = Linux ]; then
  if ls /lib/ld-musl-* >/dev/null 2>&1 || (ldd --version 2>&1 | grep -qi musl); then
    target=$target-musl
  fi
fi

name=clotran-$version-$target
fetch() {
  if command -v curl >/dev/null 2>&1; then curl -fsSL -o "$2" "$1"
  elif command -v wget >/dev/null 2>&1; then wget -qO "$2" "$1"
  else die "needs curl or wget"; fi
}
sha() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1
  else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
echo "clotran $version for $target"
fetch "$base/$name.tar.gz" "$tmp/$name.tar.gz" || die "could not download $base/$name.tar.gz"
fetch "$base/SHA256SUMS" "$tmp/SHA256SUMS" || die "could not download $base/SHA256SUMS"
want=$(grep " $name.tar.gz\$" "$tmp/SHA256SUMS" | cut -d' ' -f1)
[ -n "$want" ] || die "$name.tar.gz is not in SHA256SUMS"
[ "$(sha "$tmp/$name.tar.gz")" = "$want" ] || die "$name.tar.gz does not match its SHA256SUMS entry"

home=$prefix/lib/clotran-$version
mkdir -p "$prefix/lib" "$prefix/bin"
rm -rf "$home"
tar xzf "$tmp/$name.tar.gz" -C "$tmp"
mv "$tmp/$name" "$home"
# wrappers, not symlinks: each command finds its home from where it is
for c in clotran clotran-deps; do
  printf '#!/bin/sh\nexec "%s/bin/%s" "$@"\n' "$home" "$c" > "$prefix/bin/$c"
  chmod 755 "$prefix/bin/$c"
done
echo "installed: $prefix/bin/clotran -> $home"
case ":$PATH:" in
  *":$prefix/bin:"*) ;;
  *) echo "add $prefix/bin to PATH to run it as clotran" ;;
esac

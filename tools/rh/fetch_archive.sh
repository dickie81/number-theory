#!/bin/sh
# Fetch the Lean archive of the proof of the Riemann Hypothesis that Levent Alpöge claimed on 20 November 2026
# (https://alpo.ge/remark.pdf, footnote 1), check it against the pinned SHA-256, and extract it.
#
#   tools/rh/fetch_archive.sh [DEST]      DEST defaults to external/alpoge-rh, which .gitignore excludes
#
# The archive carries no license, so it is not in this repository: this script fetches it instead. It is
# untrusted data. The script only downloads, hashes, lists and extracts it, and it refuses an archive that
# holds anything but regular files and directories under lean/.
#
# It leaves, under DEST:
#   parts/lean.tar.gz.part01 ... part14    the download
#   listing.txt                            the archive's members, as `tar -tv` prints them
#   extract/lean/                          lean-toolchain, lakefile.toml, lake-manifest.json and src/
set -eu

URL=https://alpo.ge/lean.tar.gz.part
PARTS="01 02 03 04 05 06 07 08 09 10 11 12 13 14"
# The concatenation of the 14 parts as first downloaded on 20 November 2026 at about 14:35 UTC.
SHA256=9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
DEST=${1:-$ROOT/external/alpoge-rh}
mkdir -p "$DEST/parts"

# Download four parts at a time; a part that is already there is kept.
n=0
for i in $PARTS; do
  f="$DEST/parts/lean.tar.gz.part$i"
  if [ ! -s "$f" ]; then
    ( curl -fsSL --retry 5 --retry-delay 2 -o "$f.partial" "$URL$i" && mv "$f.partial" "$f" ) &
    n=$((n + 1))
  fi
  if [ "$n" -ge 4 ]; then wait; n=0; fi
done
wait
for i in $PARTS; do
  [ -s "$DEST/parts/lean.tar.gz.part$i" ] || { echo "part$i did not download" >&2; exit 1; }
done

archive() { for i in $PARTS; do cat "$DEST/parts/lean.tar.gz.part$i"; done; }
if command -v sha256sum >/dev/null 2>&1; then sha() { sha256sum | cut -d' ' -f1; }; else sha() { shasum -a 256 | cut -d' ' -f1; }; fi

got=$(archive | sha)
if [ "$got" != "$SHA256" ]; then
  echo "SHA-256 mismatch: the archive on the server is not the one this script pins." >&2
  echo "  got    $got" >&2
  echo "  pinned $SHA256" >&2
  exit 1
fi
echo "SHA-256 matches the pinned value: $got"

# The members: regular files and directories only, all under lean/, no absolute path and no '..'.
archive | tar -tvzf - > "$DEST/listing.txt"
archive | tar -tzf - > "$DEST/names.txt"
if grep -qv '^[-d]' "$DEST/listing.txt"; then
  echo "the archive holds a member that is neither a regular file nor a directory:" >&2
  grep -v '^[-d]' "$DEST/listing.txt" | head -5 >&2
  exit 1
fi
if grep -qvE '^lean(/|$)' "$DEST/names.txt" || grep -qE '(^|/)\.\.(/|$)' "$DEST/names.txt"; then
  echo "the archive holds a member outside lean/:" >&2
  { grep -vE '^lean(/|$)' "$DEST/names.txt"; grep -E '(^|/)\.\.(/|$)' "$DEST/names.txt"; } | head -5 >&2
  exit 1
fi
echo "$(grep -c '^-' "$DEST/listing.txt") regular files, all under lean/"
rm "$DEST/names.txt"

if [ -e "$DEST/extract" ]; then
  echo "$DEST/extract exists already: not extracting again"
else
  mkdir "$DEST/extract"
  archive | tar -xzf - -C "$DEST/extract"
  echo "extracted to $DEST/extract/lean"
fi

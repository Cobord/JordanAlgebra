#!/usr/bin/env bash
# Run comparator on JordanDiagramCheck (Challenge vs Solution), sandboxed.
#
#   COMPARATOR_DIR=/path/to/comparator JordanDiagramCheck/run.sh
#
# COMPARATOR_DIR defaults to ../comparator: a checkout of https://github.com/leanprover/comparator
# at commit fd2e25d (the last one on Lean v4.31.0, this project's toolchain), built with
#   lake build comparator && (cd .lake/packages/lean4export && lake build)
#
# Two sandbox layers (see README.md here):
#   * systemd-run with RestrictAddressFamilies=~AF_UNIX around the whole run (no Unix sockets);
#   * landrun-bwrap.sh as comparator's landrun for every build/export step (read-only filesystem
#     except .lake during the build, private /tmp and /run, no network, cleared environment).
# Set SANDBOX=0 to skip the systemd-run layer.

set -euo pipefail

PROJECT="$(cd "$(dirname "$0")/.." && pwd)"
COMPARATOR_DIR="${COMPARATOR_DIR:-$PROJECT/../comparator}"
COMPARATOR_DIR="$(cd "$COMPARATOR_DIR" && pwd)"
COMPARATOR_BIN="$COMPARATOR_DIR/.lake/build/bin/comparator"
LEAN4EXPORT_BIN="$COMPARATOR_DIR/.lake/packages/lean4export/.lake/build/bin/lean4export"
SHIM="$PROJECT/JordanDiagramCheck/landrun-bwrap.sh"

for f in "$COMPARATOR_BIN" "$LEAN4EXPORT_BIN"; do
  [[ -x "$f" ]] || { echo "missing $f (build comparator first, see header)" >&2; exit 1; }
done

cmd=(lake env "$COMPARATOR_BIN" JordanDiagramCheck/comparator.json)

cd "$PROJECT"
if [[ "${SANDBOX:-1}" == 1 ]]; then
  exec systemd-run --user --wait --pipe --quiet \
    -p RestrictAddressFamilies=~AF_UNIX \
    -E PATH="$PATH" -E HOME="$HOME" \
    -E COMPARATOR_LANDRUN="$SHIM" -E COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT_BIN" \
    --working-directory "$PROJECT" -- "${cmd[@]}"
else
  COMPARATOR_LANDRUN="$SHIM" COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT_BIN" exec "${cmd[@]}"
fi

#!/usr/bin/env bash
# Run `lake comparator` on JordanDiagramCheck (Challenge vs Solution).
#
#   JordanDiagramCheck/run.sh            # lake comparator, inside systemd-run (no Unix sockets)
#   SANDBOX=0 JordanDiagramCheck/run.sh  # lake comparator alone
#
# `lake comparator` (Lean >= v4.35.0) builds and exports the project inside its own bubblewrap
# sandbox. The systemd-run layer additionally forbids Unix sockets (RestrictAddressFamilies),
# so a sandboxed step cannot reach sockets that remain visible on the read-only filesystem.
# Pass extra options (e.g. --paranoid) as arguments.

set -euo pipefail

PROJECT="$(cd "$(dirname "$0")/.." && pwd)"
cmd=(lake comparator --config JordanDiagramCheck/comparator.json "$@")

cd "$PROJECT"
if [[ "${SANDBOX:-1}" == 1 ]]; then
  exec systemd-run --user --wait --pipe --quiet \
    -p RestrictAddressFamilies=~AF_UNIX \
    -E PATH="$PATH" -E HOME="$HOME" \
    --working-directory "$PROJECT" -- "${cmd[@]}"
else
  exec "${cmd[@]}"
fi

#!/usr/bin/env bash
# landrun-compatible sandbox shim built on bubblewrap (bwrap), for kernels without Landlock
# (landrun needs Linux >= 5.13; this machine runs 5.4).
#
# Accepts the landrun command line that comparator emits
#   landrun --best-effort --ro / --rw /dev -ldd -add-exec [--env VAR]... [--ro P]...
#           [--rwx P]... [--rox P]... CMD ARGS...
# and runs CMD under bwrap with the same policy:
#   * the whole filesystem read-only (--ro /), /dev usable (--rw /dev);
#   * write access only to the --rw/--rwx paths (comparator: the project's .lake during build);
#   * a private, empty /tmp and /run (tmpfs) and a fresh /proc: hiding /run (and /var/run, a
#     symlink to it) removes the Unix sockets there (Docker, D-Bus, the user session), which a
#     read-only mount alone does not protect, since connect() needs no write access to the mount;
#   * environment cleared, except the variables named with --env;
#   * no network at all (new network namespace), which is stricter than landrun's TCP rules;
#   * new PID/IPC/UTS namespaces, a new session (no terminal injection), killed with its parent.
# Not reproduced: landrun's per-path *execute* restriction (--rox / -ldd / -add-exec); bwrap has
# no per-mount noexec, so any readable file may be executed. Writes and network are still denied.
#
# Usage with comparator:
#   COMPARATOR_LANDRUN=$(realpath JordanDiagramCheck/landrun-bwrap.sh) \
#   COMPARATOR_LEAN4EXPORT=/path/to/lean4export \
#   lake env /path/to/comparator JordanDiagramCheck/comparator.json

set -euo pipefail

BWRAP="${BWRAP:-$(command -v bwrap)}"

bw=(
  --ro-bind / /
  --dev-bind /dev /dev
  --proc /proc
  --tmpfs /tmp
  --tmpfs /run
  --unshare-net --unshare-pid --unshare-ipc --unshare-uts --unshare-cgroup-try
  --new-session --die-with-parent
  --clearenv
)
envs=()

case "${1:-}" in
  -h|--help) echo "landrun-compatible shim over bwrap; see header of $0"; exit 0 ;;
  -V|--version) echo "landrun-bwrap shim"; exit 0 ;;
esac

while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; break ;;
    # `/` is already bound read-only above; re-binding a read-only path here would cover the
    # private /tmp, /run, /proc and /dev mounts again, so read-only paths need no action.
    --ro|--rox) shift 2 ;;
    --rw|--rwx)
      if [[ "$2" == /dev ]]; then :; elif [[ -e "$2" ]]; then bw+=(--bind "$2" "$2"); fi
      shift 2 ;;
    --env) envs+=("$2"); shift 2 ;;
    --bind-tcp|--connect-tcp|--log-level) shift 2 ;;  # network stays fully disabled
    --best-effort|-ldd|-add-exec|--unrestricted-filesystem|--unrestricted-network) shift ;;
    -*) echo "landrun-bwrap: unknown flag $1" >&2; exit 2 ;;
    *) break ;;
  esac
done

if [[ $# -eq 0 ]]; then
  echo "landrun-bwrap: no command given" >&2
  exit 2
fi

for e in "${envs[@]}"; do
  name="${e%%=*}"
  if [[ "$e" == *=* ]]; then
    bw+=(--setenv "$name" "${e#*=}")
  elif [[ -n "${!name+x}" ]]; then
    bw+=(--setenv "$name" "${!name}")
  fi
done

bw+=(--chdir "$PWD")
exec "$BWRAP" "${bw[@]}" -- "$@"

#!/usr/bin/env bash
# Exercise the evaluated launch job without changing any macOS limits.
set -euo pipefail

script=$(nix eval --raw .#darwinConfigurations.caladan.config.launchd.daemons.file-limits.script)
script=${script//\/bin\/launchctl/mock_launchctl}
script=${script//\/usr\/sbin\/sysctl/mock_sysctl}

mock_launchctl() {
  if [ "$#" -eq 2 ]; then
    printf 'maxfiles %s unlimited\n' "$FD_LIMIT"
  else
    [ "$FAIL_SET" = 0 ] || return 1
    FD_LIMIT=$3
  fi
}

mock_sysctl() {
  case "$*" in
    '-n kern.maxfiles') printf '184320\n' ;;
    '-n kern.maxfilesperproc') printf '92160\n' ;;
    '-w kern.maxfiles=184320 kern.maxfilesperproc=92160') printf 'ceilings restored\n' ;;
    *) return 1 ;;
  esac
}

export -f mock_launchctl mock_sysctl
output=$(FD_LIMIT=256 FAIL_SET=0 bash -c "$script")
[[ "$output" == $'maxfiles 4096 unlimited\nceilings restored' ]]
for limit in 8192 unlimited; do
  output=$(FD_LIMIT=$limit FAIL_SET=0 bash -c "$script")
  [[ -z "$output" ]]
done
if output=$(FD_LIMIT=256 FAIL_SET=1 bash -c "$script"); then
  printf 'Failed to propagate launchctl failure\n' >&2
  exit 1
fi
[[ "$output" == 'ceilings restored' ]]
printf 'File-limit checks passed: raise, preserve higher limits, restore on failure.\n'

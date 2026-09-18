#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export DEPLOY_FLAKE=$PWD

# Exercise the actual script without a Nix store, SSH connection, or activation.
nix() {
  if [[ $1 == flake ]]; then
    [[ ${FAIL_ARCHIVE:-0} == 0 ]] || return 1
    [[ $* == "flake archive --no-update-lock-file --to ssh-ng://builder path:$DEPLOY_FLAKE" ]]
  else
    printf '<%s>\n' "$@"
  fi
}
ssh() {
  [[ ${@: -2:1} == builder ]]
  bash -euo pipefail -c "${@: -1}"
}
# Let exec resolve the mocked commands instead of replacing the test process.
exec() { "$@"; }
export -f nix ssh exec

note=$'spaces, "quotes", an apostrophe\x27, $HOME, $(false); *\nand a newline'
actual=$(bash -euo pipefail apps/deploy-linux builder --dry-activate --targets .#test.home .#other.home -- --argstr note "$note" --argstr literal .#unchanged)
expected=$(printf '<%s>\n' run --no-update-lock-file "path:$DEPLOY_FLAKE#deploy" -- --dry-activate --targets "path:$DEPLOY_FLAKE#test.home" "path:$DEPLOY_FLAKE#other.home" -- --argstr note "$note" --argstr literal .#unchanged)
[[ $actual == "$expected" ]]

for invalid in '-oProxyCommand=false' 'builder;false' ''; do
  if bash -euo pipefail apps/deploy-linux "$invalid" .#test.home >/dev/null 2>&1; then
    echo "Accepted an invalid builder: $invalid" >&2
    exit 1
  fi
done
if FAIL_ARCHIVE=1 bash -euo pipefail apps/deploy-linux builder .#test.home >/dev/null 2>&1; then
  echo 'Continued after archive failure' >&2
  exit 1
fi
echo 'deploy-linux argument forwarding and failure checks passed'

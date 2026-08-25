#!/usr/bin/env bash
set -euo pipefail

state_home="${HEADLONG_HOME:-/root/.headlong}"
app_dir="${HEADLONG_APP_DIR:-/opt/headlong}"
upstream="$app_dir/tools/headlong-web-upstream"

if [[ "${1:-}" == "$app_dir" ]]; then
    shift
    set -- "$state_home" "$@"
fi

exec "$upstream" "$@"

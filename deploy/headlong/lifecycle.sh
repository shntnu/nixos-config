#!/usr/bin/env bash
set -euo pipefail

app_dir="${HEADLONG_APP_DIR:-/opt/headlong}"
name="${1:-}"
action="${2:-status}"

if [[ -z "$name" || ! -d "$app_dir/.identities/$name" ]]; then
    echo "usage: headlong-identity <identity-name> start|stop|status" >&2
    exit 1
fi

start_responder() {
    (
        cd "$app_dir"
        set +eu
        set +o pipefail
        # shellcheck disable=SC1090
        source "$app_dir/.identities/$name/activate" >/dev/null
        set -eu
        set -o pipefail
        thinkers start responder
    )
}

case "$action" in
    start)
        persona "$name" start
        start_responder
        ;;
    stop)
        persona "$name" stop
        ;;
    status)
        persona "$name" status
        ;;
    *)
        echo "usage: headlong-identity <identity-name> start|stop|status" >&2
        exit 1
        ;;
esac

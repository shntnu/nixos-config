#!/usr/bin/env bash
set -euo pipefail

state_home="${HEADLONG_HOME:-/root/.headlong}"
app_dir="${HEADLONG_APP_DIR:-/opt/headlong}"
secret_file="${HEADLONG_SECRET_FILE:-/run/secrets/llm_api_key}"
key_name="${HEADLONG_KEY_ENV:-}"

case "$key_name" in
    ANTHROPIC_API_KEY|OPENAI_API_KEY|GEMINI_API_KEY|OPENROUTER_API_KEY) ;;
    *)
        echo "HEADLONG_KEY_ENV must name a supported provider key variable" >&2
        exit 1
        ;;
esac

if [[ ! -r "$secret_file" ]]; then
    echo "the provider secret is not readable at $secret_file" >&2
    exit 1
fi

key="$(<"$secret_file")"
if [[ -z "$key" || "$key" == *$'\n'* || "$key" == *$'\r'* ]]; then
    echo "the provider secret must contain one nonempty line" >&2
    exit 1
fi

for required in SHELLM_MODEL LLM_API_URL SHELLM_API_URL; do
    if [[ -z "${!required:-}" ]]; then
        echo "$required must be set" >&2
        exit 1
    fi
done

umask 077
mkdir -p "$state_home" "$state_home/.identities" "$state_home/logs" "$state_home/run"
chmod 700 "$state_home" "$state_home/.identities"

env_tmp="$(mktemp "$state_home/.env.XXXXXX")"
trap 'find "$env_tmp" -maxdepth 0 -delete 2>/dev/null || true' EXIT
{
    printf '%s=%q\n' "$key_name" "$key"
    printf 'SHELLM_MODEL=%q\n' "$SHELLM_MODEL"
    printf 'LLM_API_URL=%q\n' "$LLM_API_URL"
    printf 'SHELLM_API_URL=%q\n' "$SHELLM_API_URL"
    printf 'SHELLM_REQUIRE_DOCKER=0\n'
} > "$env_tmp"
chmod 600 "$env_tmp"
mv -f "$env_tmp" "$state_home/.env"
trap - EXIT

printf '%s\n' "$app_dir" > "$state_home/app_dir"

if [[ -L "$app_dir/.identities/default" ]]; then
    identity_name="$(basename "$(readlink "$app_dir/.identities/default")")"
    headlong-identity "$identity_name" start
fi

exec tail -f /dev/null

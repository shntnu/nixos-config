{ config, lib, pkgs, ... }:

let
  cfg = config.services.msgvaultRemote;
  knownHosts = pkgs.writeText "msgvault-caladan-known-hosts" ''
    caladan ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIIHyd9zwLfPGs0W0T5Du1M+xEty5lc3iWanuNq5yp7PA
  '';
  client = pkgs.writeShellApplication {
    name = "msgvault-caladan";
    runtimeInputs = with pkgs; [ coreutils gnused openssh msgvault ];
    text = ''
      source_host=${lib.escapeShellArg cfg.sourceHost}
      case "''${1:-}" in
        search|show-message|stats|list-accounts|list-domains|list-labels|list-senders|query|cache-stats|export-attachment|export-attachments|export-eml|export-messages|tui)
          ;;
        *)
          echo "msgvault-caladan permits remote read, export, and TUI commands only" >&2
          exit 2
          ;;
      esac

      ssh_options=(
        -o BatchMode=yes
        -o ConnectTimeout=15
        -o ServerAliveCountMax=3
        -o ServerAliveInterval=5
        -o StrictHostKeyChecking=yes
        -o UserKnownHostsFile=${knownHosts}
      )

      # The remote shell, not this client, expands HOME.
      # shellcheck disable=SC2016
      remote_status="$(timeout --kill-after=5s 20s \
        ssh "''${ssh_options[@]}" "$source_host" \
          '$HOME/.nix-profile/bin/msgvault --no-log-file daemon status' \
          2>/dev/null)" || {
        remote_status_exit=$?
        if [ "$remote_status_exit" -eq 124 ] || [ "$remote_status_exit" -eq 137 ]; then
          echo "Timed out after 20 seconds while contacting Caladan over SSH" >&2
        else
          echo "Unable to contact Caladan over SSH (exit $remote_status_exit)" >&2
        fi
        exit 1
      }
      remote_port="$(printf '%s\n' "$remote_status" \
        | sed -n 's/.*running at http:\/\/127\.0\.0\.1:\([0-9][0-9]*\).*/\1/p')"
      if [ -z "$remote_port" ]; then
        echo "Caladan's msgvault daemon is unavailable" >&2
        exit 1
      fi

      # The keyless daemon validates the HTTP Host port against its listener
      # port, so the local end of the tunnel must use that same port.
      local_port="$remote_port"
      tunnel_pid=
      cleanup() {
        if [ -n "$tunnel_pid" ]; then
          kill "$tunnel_pid" >/dev/null 2>&1 || true
          wait "$tunnel_pid" >/dev/null 2>&1 || true
        fi
      }
      trap cleanup EXIT

      ssh -NT \
        "''${ssh_options[@]}" \
        -o ExitOnForwardFailure=yes \
        -L "127.0.0.1:$local_port:127.0.0.1:$remote_port" \
        "$source_host" &
      tunnel_pid=$!

      tunnel_ready=false
      for _ in {1..50}; do
        if ! kill -0 "$tunnel_pid" 2>/dev/null; then
          wait "$tunnel_pid"
        fi
        if (exec 3<>"/dev/tcp/127.0.0.1/$local_port") 2>/dev/null; then
          tunnel_ready=true
          break
        fi
        sleep 0.1
      done
      if ! "$tunnel_ready"; then
        echo "Timed out opening the tunnel to Caladan" >&2
        exit 1
      fi

      msgvault --config <(
        printf '[remote]\nurl = "http://127.0.0.1:%s"\nallow_insecure = true\n' \
          "$local_port"
      ) --no-log-file "$@"
    '';
  };
in
{
  options.services.msgvaultRemote = {
    enable = lib.mkEnableOption "on-demand SSH access to Caladan's msgvault daemon";
    sourceHost = lib.mkOption {
      type = lib.types.str;
      default = "caladan";
      description = "SSH host that owns the authoritative msgvault archive.";
    };
  };

  config = lib.mkIf cfg.enable {
    home.packages = [ client ];
  };
}

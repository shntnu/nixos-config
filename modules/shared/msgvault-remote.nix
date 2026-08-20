{ config, lib, pkgs, ... }:

let
  cfg = config.services.msgvaultRemote;
  knownHosts = pkgs.writeText "msgvault-caladan-known-hosts" ''
    caladan ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIIHyd9zwLfPGs0W0T5Du1M+xEty5lc3iWanuNq5yp7PA
  '';
  client = pkgs.writeShellApplication {
    name = "msgvault-caladan";
    runtimeInputs = with pkgs; [ coreutils gnused openssh trash-cli msgvault ];
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
        -o StrictHostKeyChecking=yes
        -o UserKnownHostsFile=${knownHosts}
      )

      remote_status="$(ssh "''${ssh_options[@]}" "$source_host" \
        '$HOME/.nix-profile/bin/msgvault --no-log-file daemon status' 2>/dev/null)"
      remote_port="$(printf '%s\n' "$remote_status" \
        | sed -n 's/.*running at http:\/\/127\.0\.0\.1:\([0-9][0-9]*\).*/\1/p')"
      if [ -z "$remote_port" ]; then
        echo "Caladan's msgvault daemon is unavailable" >&2
        exit 1
      fi

      # The keyless daemon validates the HTTP Host port against its listener
      # port, so the local end of the tunnel must use that same port.
      local_port="$remote_port"
      runtime_dir="$(mktemp -d /tmp/msgvault-caladan.XXXXXX)"
      control_socket="$runtime_dir/ssh"
      config_file="$runtime_dir/config.toml"
      cleanup() {
        ssh "''${ssh_options[@]}" -S "$control_socket" -O exit \
          "$source_host" >/dev/null 2>&1 || true
        trash "$runtime_dir" >/dev/null 2>&1 || true
      }
      trap cleanup EXIT

      {
        echo '[remote]'
        echo "url = \"http://127.0.0.1:$local_port\""
        echo 'allow_insecure = true'
      } > "$config_file"
      chmod 600 "$config_file"

      ssh -M -S "$control_socket" -fNT \
        "''${ssh_options[@]}" \
        -o ExitOnForwardFailure=yes \
        -o ServerAliveInterval=30 \
        -L "127.0.0.1:$local_port:127.0.0.1:$remote_port" \
        "$source_host"

      msgvault --config "$config_file" --no-log-file "$@"
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

{ config, lib, pkgs, ... }:

let
  cfg = config.services.msgvaultReplication;
  stateDir = "${config.home.homeDirectory}/.local/state/msgvault-replication";
  mirrorRoot = "${config.home.homeDirectory}/.local/share/msgvault-mirror";
  publishedLink = "${config.home.homeDirectory}/.local/share/msgvault-published";

  writeStatus = pkgs.writeShellScript "msgvault-write-status" ''
    status_file="$1"
    state="$2"
    snapshot_id="''${3:-none}"
    now="$(${pkgs.coreutils}/bin/date +%s)"
    tmp="$status_file.tmp.$$"
    {
      echo "state=$state"
      echo "snapshot_id=$snapshot_id"
      echo "updated_at_epoch=$now"
      if [ -r "$status_file" ]; then
        ${pkgs.gnugrep}/bin/grep '^last_success_epoch=' "$status_file" \
          | ${pkgs.coreutils}/bin/tail -n 1 || true
      fi
      if [ "$state" = success ]; then
        echo "last_success_epoch=$now"
      fi
    } > "$tmp"
    ${pkgs.coreutils}/bin/mv -f "$tmp" "$status_file"
  '';

  publisher = pkgs.writeShellApplication {
    name = "msgvault-publish-snapshot";
    runtimeInputs = with pkgs; [ coreutils gawk gnugrep sqlite msgvault ];
    text = ''
      repository=${lib.escapeShellArg cfg.publisher.repository}
      published_root=${lib.escapeShellArg cfg.publisher.publishedRoot}
      state_dir=${lib.escapeShellArg stateDir}
      status_file="$state_dir/publisher-status"
      mkdir -p "$state_dir" "$repository" "$published_root"

      ${writeStatus} "$status_file" running
      completed=false
      on_exit() {
        if [ "$completed" != true ]; then
          ${writeStatus} "$status_file" failed
        fi
      }
      trap on_exit EXIT

      if [ ! -f "$repository/config.toml" ]; then
        msgvault backup init --repo "$repository"
      fi

      msgvault backup create --repo "$repository" --tag scheduled
      msgvault backup verify --repo "$repository" --quick
      snapshot_id="$(msgvault backup list --repo "$repository" | awk 'NR > 1 { id = $1 } END { print id }')"
      if [ -z "$snapshot_id" ]; then
        echo "msgvault did not report a completed backup snapshot" >&2
        exit 1
      fi

      current_target=""
      if [ -L "$published_root/current" ]; then
        current_target="$(readlink "$published_root/current")"
      fi
      if [ "$current_target" = slot-a ]; then
        next_slot=slot-b
      else
        next_slot=slot-a
      fi
      target="$published_root/$next_slot"
      mkdir -p "$target"

      msgvault backup restore "$snapshot_id" \
        --repo "$repository" \
        --target "$target" \
        --overwrite
      msgvault --home "$target" --local --no-log-file build-cache --full-rebuild

      for forbidden in config.toml tokens client_secret.json client_secret_personal.json; do
        if [ -e "$target/$forbidden" ]; then
          echo "refusing to publish credential-bearing path: $forbidden" >&2
          exit 1
        fi
      done

      quick_check="$(sqlite3 "$target/msgvault.db" 'PRAGMA quick_check;')"
      if [ "$quick_check" != ok ]; then
        echo "restored database failed PRAGMA quick_check: $quick_check" >&2
        exit 1
      fi
      message_count="$(sqlite3 "$target/msgvault.db" 'SELECT count(*) FROM messages;')"
      attachment_count="$(sqlite3 "$target/msgvault.db" 'SELECT count(*) FROM attachments;')"
      source_count="$(sqlite3 "$target/msgvault.db" 'SELECT count(*) FROM sources;')"
      created_at_epoch="$(date +%s)"
      manifest_tmp="$target/.mirror-manifest.tmp.$$"
      {
        echo "snapshot_id=$snapshot_id"
        echo "created_at_epoch=$created_at_epoch"
        echo "message_count=$message_count"
        echo "attachment_count=$attachment_count"
        echo "source_count=$source_count"
      } > "$manifest_tmp"
      mv -f "$manifest_tmp" "$target/.mirror-manifest"

      link_tmp="$published_root/.current.$snapshot_id"
      ln -s "$next_slot" "$link_tmp"
      mv -f "$link_tmp" "$published_root/current"

      mkdir -p "$(dirname ${lib.escapeShellArg publishedLink})"
      home_link_tmp=${lib.escapeShellArg "${publishedLink}.new"}
      ln -s "$published_root/current" "$home_link_tmp"
      mv -f "$home_link_tmp" ${lib.escapeShellArg publishedLink}

      ${writeStatus} "$status_file" success "$snapshot_id"
      completed=true
      echo "Published msgvault snapshot $snapshot_id ($message_count messages, $attachment_count attachments, $source_count sources)"
    '';
  };

  pullMirror = pkgs.writeShellApplication {
    name = "msgvault-pull-mirror";
    runtimeInputs = with pkgs; [ coreutils gawk gnugrep openssh rsync sqlite msgvault ];
    text = ''
      source_host=${lib.escapeShellArg cfg.mirror.sourceHost}
      source_path=${lib.escapeShellArg cfg.mirror.sourcePath}
      mirror_root=${lib.escapeShellArg mirrorRoot}
      state_dir=${lib.escapeShellArg stateDir}
      status_file="$state_dir/client-status"
      mkdir -p "$state_dir" "$mirror_root"

      ${writeStatus} "$status_file" running
      completed=false
      on_exit() {
        if [ "$completed" != true ]; then
          ${writeStatus} "$status_file" failed
        fi
      }
      trap on_exit EXIT

      remote_manifest="$(ssh -o BatchMode=yes -o ConnectTimeout=15 "$source_host" \
        "cat '$source_path/.mirror-manifest'")"
      snapshot_id="$(printf '%s\n' "$remote_manifest" | awk -F= '$1 == "snapshot_id" { print $2 }')"
      if [ -z "$snapshot_id" ]; then
        echo "source did not report a published snapshot" >&2
        exit 1
      fi

      if [ -r "$mirror_root/current/.mirror-manifest" ]; then
        current_snapshot_id="$(awk -F= '$1 == "snapshot_id" { print $2 }' \
          "$mirror_root/current/.mirror-manifest")"
        if [ "$current_snapshot_id" = "$snapshot_id" ]; then
          ${writeStatus} "$status_file" success "$snapshot_id"
          completed=true
          echo "Msgvault mirror is already current at $snapshot_id"
          exit 0
        fi
      fi

      if [ -L "$mirror_root/current" ] && \
         [ "$(readlink "$mirror_root/current")" = "slot-a" ]; then
        next_slot=slot-b
      else
        next_slot=slot-a
      fi
      target="$mirror_root/$next_slot"
      if [ ! -d "$target" ]; then
        if [ -d "$mirror_root/current" ]; then
          if [ "$(uname -s)" = Darwin ]; then
            mkdir -p "$target"
            cp -cR "$mirror_root/current/." "$target/"
          else
            mkdir -p "$target"
            cp -al "$mirror_root/current/." "$target/"
          fi
        else
          mkdir -p "$target"
        fi
      fi

      rsync_args=(-a --delete --partial)
      if [ "$(uname -s)" = Darwin ]; then
        rsync_args+=(--inplace)
      fi
      rsync "''${rsync_args[@]}" "$source_host:$source_path/" "$target/"

      remote_manifest_after="$(ssh -o BatchMode=yes -o ConnectTimeout=15 "$source_host" \
        "cat '$source_path/.mirror-manifest'")"
      if [ "$remote_manifest" != "$remote_manifest_after" ]; then
        echo "source snapshot changed during transfer; leaving the current mirror untouched" >&2
        exit 1
      fi
      if [ "$(cat "$target/.mirror-manifest")" != "$remote_manifest" ]; then
        echo "transferred manifest does not match the source" >&2
        exit 1
      fi

      for forbidden in config.toml tokens client_secret.json client_secret_personal.json; do
        if [ -e "$target/$forbidden" ]; then
          echo "replica contains forbidden credential-bearing path: $forbidden" >&2
          exit 1
        fi
      done

      quick_check="$(sqlite3 "$target/msgvault.db" 'PRAGMA quick_check;')"
      if [ "$quick_check" != ok ]; then
        echo "replica failed PRAGMA quick_check: $quick_check" >&2
        exit 1
      fi
      message_count="$(sqlite3 "$target/msgvault.db" 'SELECT count(*) FROM messages;')"
      attachment_count="$(sqlite3 "$target/msgvault.db" 'SELECT count(*) FROM attachments;')"
      source_count="$(sqlite3 "$target/msgvault.db" 'SELECT count(*) FROM sources;')"
      expected_messages="$(printf '%s\n' "$remote_manifest" | awk -F= '$1 == "message_count" { print $2 }')"
      expected_attachments="$(printf '%s\n' "$remote_manifest" | awk -F= '$1 == "attachment_count" { print $2 }')"
      expected_sources="$(printf '%s\n' "$remote_manifest" | awk -F= '$1 == "source_count" { print $2 }')"
      if [ "$message_count" != "$expected_messages" ] || \
         [ "$attachment_count" != "$expected_attachments" ] || \
         [ "$source_count" != "$expected_sources" ]; then
        echo "replica counts do not match source manifest" >&2
        exit 1
      fi

      msgvault --home "$target" --local --no-log-file stats >/dev/null
      link_tmp="$mirror_root/.current.$snapshot_id"
      ln -s "$next_slot" "$link_tmp"
      mv -f "$link_tmp" "$mirror_root/current"

      ${writeStatus} "$status_file" success "$snapshot_id"
      completed=true
      echo "Activated msgvault mirror $snapshot_id ($message_count messages, $attachment_count attachments, $source_count sources)"
    '';
  };

  mirror = pkgs.writeShellApplication {
    name = "msgvault-mirror";
    runtimeInputs = [ pkgs.msgvault ];
    text = ''
      mirror_home=${lib.escapeShellArg "${mirrorRoot}/current"}
      if [ ! -r "$mirror_home/msgvault.db" ]; then
        echo "No usable msgvault mirror is installed; run msgvault-pull-mirror" >&2
        exit 1
      fi
      case "''${1:-}" in
        search|show-message|stats|list-accounts|list-domains|list-labels|list-senders|query|cache-stats|export-attachment|export-attachments|export-eml|export-messages)
          ;;
        *)
          echo "msgvault-mirror permits read/export commands only" >&2
          exit 2
          ;;
      esac
      exec msgvault --home "$mirror_home" --local --no-log-file "$@"
    '';
  };

  status = pkgs.writeShellApplication {
    name = "msgvault-mirror-status";
    runtimeInputs = with pkgs; [ coreutils gnugrep gnused ];
    text = ''
      state_dir=${lib.escapeShellArg stateDir}
      now="$(date +%s)"
      found=false
      stale=false
      for role in publisher client; do
        status_file="$state_dir/$role-status"
        if [ ! -r "$status_file" ]; then
          continue
        fi
        found=true
        echo "$role:"
        sed 's/^/  /' "$status_file"
        last_success="$(grep '^last_success_epoch=' "$status_file" | tail -n 1 | cut -d= -f2 || true)"
        max_age=${if cfg.publisher.enable then "129600" else "10800"}
        if [ -z "$last_success" ] || [ "$((now - last_success))" -gt "$max_age" ]; then
          echo "  freshness=stale"
          stale=true
        else
          echo "  freshness=fresh"
        fi
      done
      if [ "$found" = false ]; then
        echo "No msgvault replication status is available" >&2
        exit 1
      fi
      if [ "$stale" = true ]; then
        exit 2
      fi
    '';
  };
in
{
  options.services.msgvaultReplication = {
    publisher = {
      enable = lib.mkEnableOption "publication of consistent msgvault snapshots";
      repository = lib.mkOption {
        type = lib.types.str;
        default = "/Volumes/Backups of caladan/msgvault/repository";
      };
      publishedRoot = lib.mkOption {
        type = lib.types.str;
        default = "/Volumes/Backups of caladan/msgvault/published";
      };
    };
    mirror = {
      enable = lib.mkEnableOption "a local read-only-oriented msgvault mirror";
      sourceHost = lib.mkOption {
        type = lib.types.str;
        default = "caladan";
      };
      sourcePath = lib.mkOption {
        type = lib.types.str;
        default = ".local/share/msgvault-published";
      };
    };
  };

  config = lib.mkIf (cfg.publisher.enable || cfg.mirror.enable) {
    assertions = [
      {
        assertion = !(cfg.publisher.enable && cfg.mirror.enable);
        message = "A host cannot publish and consume the msgvault mirror simultaneously.";
      }
    ];

    home.packages = [ pkgs.msgvault status ]
      ++ lib.optional cfg.publisher.enable publisher
      ++ lib.optionals cfg.mirror.enable [ pullMirror mirror ];

    launchd.agents = lib.mkIf pkgs.stdenv.hostPlatform.isDarwin (lib.mkMerge [
      (lib.mkIf cfg.publisher.enable {
        msgvault-publish-snapshot = {
          enable = true;
          config = {
            ProgramArguments = [ "${publisher}/bin/msgvault-publish-snapshot" ];
            StartCalendarInterval = [{ Hour = 4; Minute = 10; }];
            LowPriorityIO = true;
            StandardErrorPath = "/tmp/msgvault-publish-snapshot.err.log";
            StandardOutPath = "/tmp/msgvault-publish-snapshot.out.log";
          };
        };
      })
      (lib.mkIf cfg.mirror.enable {
        msgvault-pull-mirror = {
          enable = true;
          config = {
            ProgramArguments = [ "${pullMirror}/bin/msgvault-pull-mirror" ];
            RunAtLoad = true;
            StartCalendarInterval = [{ Minute = 40; }];
            LowPriorityIO = true;
            StandardErrorPath = "/tmp/msgvault-pull-mirror.err.log";
            StandardOutPath = "/tmp/msgvault-pull-mirror.out.log";
          };
        };
      })
    ]);

    systemd.user = lib.mkIf pkgs.stdenv.hostPlatform.isLinux (lib.mkIf cfg.mirror.enable {
      services.msgvault-pull-mirror = {
        Unit.Description = "Refresh the local msgvault archive mirror";
        Service = {
          Type = "oneshot";
          ExecStart = "${pullMirror}/bin/msgvault-pull-mirror";
        };
      };
      timers.msgvault-pull-mirror = {
        Unit.Description = "Refresh the local msgvault archive mirror hourly";
        Timer = {
          OnCalendar = "*-*-* *:40:00";
          Persistent = true;
          RandomizedDelaySec = "10m";
        };
        Install.WantedBy = [ "timers.target" ];
      };
    });
  };
}

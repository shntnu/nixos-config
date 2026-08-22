{
  config,
  lib,
  pkgs,
  ...
}:

let
  cfg = config.services.healthGuardrails;
  user = config.system.primaryUser;

  kbPerGib = 1024 * 1024;

  # Test overrides (used to verify each alert path without filling the disk):
  #   DISK_GUARD_FREE_KB    fake free space in KiB
  #   DISK_GUARD_STATE_DIR  alternate throttle-state directory
  #   TM_CHECK_HOST         alternate backup host
  #   TM_CHECK_MAX_AGE_SEC  alternate staleness threshold in seconds
  diskGuard = pkgs.writeShellApplication {
    name = "disk-guard";
    runtimeInputs = [
      pkgs.coreutils
      pkgs.gawk
      pkgs.uv
      config.nix.package
    ];
    text = ''
      set -euo pipefail

      log_file="$HOME/Library/Logs/disk-guard.log"
      state_dir="''${DISK_GUARD_STATE_DIR:-$HOME/Library/Application Support/disk-guard}"
      mkdir -p "$state_dir" "$(dirname "$log_file")"

      log() {
        printf '%s %s\n' "$(date '+%Y-%m-%dT%H:%M:%S%z')" "$1" >> "$log_file"
      }

      notify() {
        log "ALERT $1"
        /usr/bin/osascript -e "display notification \"$1\" with title \"Disk Guard\"" \
          || log "osascript notification failed"
      }

      # Truncate in place (same inode) so concurrent appenders never lose the
      # file; the tail scratch file is reused, never deleted.
      if [ -f "$log_file" ] && [ "$(stat -c %s "$log_file")" -gt 524288 ]; then
        tail -n 500 "$log_file" > "$state_dir/log-tail.tmp"
        cat "$state_dir/log-tail.tmp" > "$log_file"
        log "rotated log"
      fi

      # Returns success at most once per window; alerts stay quiet in between.
      throttle_ok() {
        local stamp="$state_dir/last-$1" now last
        now="$(date +%s)"
        last="$(cat "$stamp" 2>/dev/null || echo 0)"
        [ "$((now - last))" -ge "$2" ] || return 1
        echo "$now" > "$stamp"
      }

      free_kb="''${DISK_GUARD_FREE_KB:-$(/bin/df -k /System/Volumes/Data | awk 'NR==2 {print $4}')}"
      free_gib="$(awk -v kb="$free_kb" 'BEGIN { printf "%.1f", kb / ${toString kbPerGib} }')"
      log "free space: $free_gib GiB"

      if [ "$free_kb" -lt "${toString (cfg.disk.urgentFreeGb * kbPerGib)}" ]; then
        notify "URGENT: only $free_gib GiB free (below ${toString cfg.disk.urgentFreeGb} GiB)"
      elif [ "$free_kb" -lt "${toString (cfg.disk.warnFreeGb * kbPerGib)}" ]; then
        if throttle_ok warn 86400; then
          notify "Low disk space: $free_gib GiB free (below ${toString cfg.disk.warnFreeGb} GiB)"
        fi
      fi

      # Safe cleanup only: expire the user's Nix profile generations and prune
      # the uv cache. Never automatically purge Trash or msgvault data.
      if [ "$free_kb" -lt "${toString (cfg.disk.cleanupFreeGb * kbPerGib)}" ]; then
        if throttle_ok cleanup 21600; then
          log "cleanup: nix-collect-garbage --delete-older-than 14d"
          nix-collect-garbage --delete-older-than 14d >> "$log_file" 2>&1 \
            || log "cleanup: nix-collect-garbage failed"
          log "cleanup: uv cache prune"
          # Fail fast instead of waiting minutes when another uv process
          # holds the cache lock.
          UV_LOCK_TIMEOUT=10 uv cache prune >> "$log_file" 2>&1 \
            || log "cleanup: uv cache prune failed"
          after_kb="$(/bin/df -k /System/Volumes/Data | awk 'NR==2 {print $4}')"
          log "cleanup: done, $(awk -v kb="$after_kb" 'BEGIN { printf "%.1f", kb / ${toString kbPerGib} }') GiB free"
        else
          log "cleanup: wanted but throttled"
        fi
      fi
    '';
  };

  tmFreshness = pkgs.writeShellApplication {
    name = "tm-freshness";
    runtimeInputs = [ pkgs.coreutils ];
    text = ''
      set -euo pipefail

      log_file="$HOME/Library/Logs/tm-freshness.log"
      mkdir -p "$(dirname "$log_file")"

      log() {
        printf '%s %s\n' "$(date '+%Y-%m-%dT%H:%M:%S%z')" "$1" >> "$log_file"
      }

      notify() {
        log "ALERT $1"
        /usr/bin/osascript -e "display notification \"$1\" with title \"Time Machine Check\"" \
          || log "osascript notification failed"
      }

      host="''${TM_CHECK_HOST:-${cfg.timeMachine.host}}"
      max_age_sec="''${TM_CHECK_MAX_AGE_SEC:-${toString (cfg.timeMachine.maxAgeHours * 3600)}}"

      if /usr/bin/nc -z -G 10 "$host" ${toString cfg.timeMachine.port} >/dev/null 2>&1; then
        log "reachable: $host:${toString cfg.timeMachine.port}"
      else
        notify "Backup destination $host is unreachable on SMB port ${toString cfg.timeMachine.port}"
      fi

      # tmutil reports the latest completed backup even while the network
      # destination is unmounted; format is YYYY-MM-DD-HHMMSS in local time.
      ts="$(/usr/bin/tmutil latestbackup -t 2>/dev/null || true)"
      if [ -z "$ts" ]; then
        notify "Cannot determine the latest completed Time Machine backup"
      else
        epoch="$(date -d "''${ts:0:10} ''${ts:11:2}:''${ts:13:2}:''${ts:15:2}" +%s)"
        age_sec="$(( $(date +%s) - epoch ))"
        age_hours="$(( age_sec / 3600 ))"
        if [ "$age_sec" -gt "$max_age_sec" ]; then
          notify "Latest completed backup ($ts) is ''${age_hours}h old"
        else
          log "latest backup $ts is ''${age_hours}h old (fresh)"
        fi
      fi
    '';
  };

  wrapped = script: name: [
    "/bin/sh"
    "-c"
    "/bin/wait4path ${script}/bin/${name} && exec ${script}/bin/${name}"
  ];
in
{
  options.services.healthGuardrails = {
    enable = lib.mkEnableOption "disk-space and Time Machine freshness guardrails";

    disk = {
      warnFreeGb = lib.mkOption {
        type = lib.types.ints.positive;
        default = 20;
        description = "Notify (at most daily) when free space falls below this many GiB.";
      };

      urgentFreeGb = lib.mkOption {
        type = lib.types.ints.positive;
        default = 10;
        description = "Notify on every check while free space stays below this many GiB.";
      };

      cleanupFreeGb = lib.mkOption {
        type = lib.types.ints.positive;
        default = 5;
        description = ''
          Run safe automatic cleanup (user Nix generations older than 14 days,
          uv cache prune) below this many GiB. Trash and msgvault are never
          touched automatically.
        '';
      };
    };

    timeMachine = {
      host = lib.mkOption {
        type = lib.types.str;
        description = "Backup destination hostname probed over SMB (use the .local mDNS name).";
      };

      port = lib.mkOption {
        type = lib.types.port;
        default = 445;
        description = "TCP port probed for backup destination reachability.";
      };

      maxAgeHours = lib.mkOption {
        type = lib.types.ints.positive;
        default = 26;
        description = "Alert when the latest completed backup is older than this many hours.";
      };
    };
  };

  config = lib.mkIf cfg.enable {
    assertions = [
      {
        assertion = cfg.disk.warnFreeGb > cfg.disk.urgentFreeGb && cfg.disk.urgentFreeGb > cfg.disk.cleanupFreeGb;
        message = "services.healthGuardrails disk thresholds must satisfy warn > urgent > cleanup";
      }
    ];

    launchd.user.agents.disk-guard.serviceConfig = {
      ProgramArguments = wrapped diskGuard "disk-guard";
      EnvironmentVariables.HOME = "/Users/${user}";
      StartInterval = 1800;
      RunAtLoad = true;
      StandardErrorPath = "/tmp/disk-guard.err.log";
      StandardOutPath = "/tmp/disk-guard.out.log";
    };

    launchd.user.agents.tm-freshness.serviceConfig = {
      ProgramArguments = wrapped tmFreshness "tm-freshness";
      EnvironmentVariables.HOME = "/Users/${user}";
      StartCalendarInterval = [
        {
          Hour = 9;
          Minute = 5;
        }
      ];
      StandardErrorPath = "/tmp/tm-freshness.err.log";
      StandardOutPath = "/tmp/tm-freshness.out.log";
    };
  };
}

{
  config,
  lib,
  pkgs,
  ...
}:

let
  cfg = config.services.healthGuardrails;
  user = config.system.primaryUser;
  inherit (import ./stable-bin.nix { inherit lib; }) stableBin;

  kbPerGib = 1024 * 1024;

  # Deterministic tests can replace every external input:
  #   DISK_GUARD_FREE_KB       fake free space in KiB; skips real cleanup
  #   DISK_GUARD_DF            alternate df executable when free space is not injected
  #   DISK_GUARD_STATE_DIR     alternate private state directory
  #   DISK_GUARD_LOG_FILE      alternate log file
  #   DISK_GUARD_NOW           alternate Unix timestamp
  #   DISK_GUARD_NOTIFY        local notification executable, message on stdin
  #   DISK_GUARD_REMOTE_NOTIFY remote notification executable, message on stdin
  #   DISK_GUARD_CLEANUP       cleanup test executable; no arguments
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
      umask 077

      state_dir="''${DISK_GUARD_STATE_DIR:-$HOME/Library/Application Support/disk-guard}"
      state_file="$state_dir/state"
      cleanup_stamp="$state_dir/last-cleanup"
      log_file="''${DISK_GUARD_LOG_FILE:-$HOME/Library/Logs/disk-guard.log}"
      notify_override="''${DISK_GUARD_NOTIFY:-}"
      cleanup_override="''${DISK_GUARD_CLEANUP:-}"
      remote_notifier=${
        lib.escapeShellArg (if cfg.remoteNotifier == null then "" else cfg.remoteNotifier)
      }
      if [ "''${DISK_GUARD_REMOTE_NOTIFY+x}" = x ]; then
        remote_notifier="$DISK_GUARD_REMOTE_NOTIFY"
      fi

      persistence_warning_emitted=false
      warn_persistence() {
        if [ "$persistence_warning_emitted" = false ]; then
          printf '%s\n' \
            "Disk Guard persistence unavailable; notifications will continue without durable suppression" \
            >&2 || true
          persistence_warning_emitted=true
        fi
      }

      if ! mkdir -p "$state_dir" 2>/dev/null; then
        warn_persistence
      fi
      if [ -d "$state_dir" ] && ! chmod 700 "$state_dir" 2>/dev/null; then
        warn_persistence
      fi
      if ! mkdir -p "$(dirname "$log_file")" 2>/dev/null; then
        warn_persistence
      fi
      if ! touch "$log_file" 2>/dev/null; then
        warn_persistence
      fi
      if [ -f "$log_file" ] && ! chmod 600 "$log_file" 2>/dev/null; then
        warn_persistence
      fi
      if [ -f "$state_file" ] && ! chmod 600 "$state_file" 2>/dev/null; then
        warn_persistence
      fi
      if [ -f "$cleanup_stamp" ] && ! chmod 600 "$cleanup_stamp" 2>/dev/null; then
        warn_persistence
      fi

      log() {
        if ! {
          printf '%s %s\n' "$(date '+%Y-%m-%dT%H:%M:%S%z')" "$1" >> "$log_file"
        } 2>/dev/null; then
          warn_persistence
        fi
        return 0
      }

      write_state() {
        if {
          printf '%s\n%s\n%s\n' "$category" "$next_alert" "$pending_remote" > "$state_file.next" \
            && chmod 600 "$state_file.next" \
            && mv -f "$state_file.next" "$state_file" \
            && chmod 600 "$state_file"
        } 2>/dev/null; then
          return 0
        fi
        warn_persistence
        log "state persistence failed"
        return 1
      }

      deliver_local() {
        local message="$1"
        log "ALERT category=$category"

        if [ -n "$notify_override" ]; then
          if ! printf '%s\n' "$message" \
            | timeout --kill-after=5s 30s "$notify_override"
          then
            log "local test notification failed"
          fi
          return
        fi

        if ! timeout --kill-after=5s 30s /usr/bin/osascript - "$message" <<'APPLESCRIPT'
on run argv
  display notification (item 1 of argv) with title "Disk Guard"
end run
APPLESCRIPT
        then
          log "local notification failed"
        fi
      }

      message_for_token() {
        case "$1" in
          warn)
            remote_message="Disk space alert: caladan has less than ${
              toString cfg.disk.warnFreeGb
            } GiB free. Free space or move data soon."
            ;;
          urgent)
            remote_message="Disk space urgent: caladan has less than ${
              toString cfg.disk.urgentFreeGb
            } GiB free. Free space now and pause large writes."
            ;;
          check-failed)
            remote_message="Disk space check failed: free space on caladan could not be measured. Check the disk and Disk Guard."
            ;;
          recovered)
            remote_message="Disk space recovered: caladan has at least ${
              toString cfg.disk.warnFreeGb
            } GiB free."
            ;;
          *) return 1 ;;
        esac
      }

      deliver_remote() {
        local message="$1"
        if ! printf '%s\n' "$message" \
          | timeout --kill-after=5s 30s "$remote_notifier"
        then
          log "remote notification failed; will retry on next run"
          return 1
        fi
      }

      # Truncate in place (same inode) so concurrent appenders never lose the
      # file; the tail scratch file is reused, never deleted.
      log_size="$(stat -c %s "$log_file" 2>/dev/null || printf '0')"
      case "$log_size" in
        "" | *[!0-9]*) log_size=0 ;;
      esac
      if [ "$log_size" -gt 524288 ]; then
        if {
          tail -n 500 "$log_file" > "$state_dir/log-tail.tmp" \
            && cat "$state_dir/log-tail.tmp" > "$log_file"
        } 2>/dev/null; then
          log "rotated log"
        else
          warn_persistence
        fi
      fi

      now="''${DISK_GUARD_NOW:-$(date +%s)}"
      case "$now" in
        "" | *[!0-9]*)
          echo "Disk Guard test time must be a non-negative Unix timestamp" >&2
          exit 1
          ;;
      esac
      if [ "''${#now}" -gt 12 ]; then
        echo "Disk Guard test time must be a non-negative Unix timestamp" >&2
        exit 1
      fi

      free_injected=false
      measurement_ok=true
      df_command="''${DISK_GUARD_DF:-/bin/df}"
      if [ "''${DISK_GUARD_FREE_KB+x}" = x ]; then
        free_injected=true
        free_kb="$DISK_GUARD_FREE_KB"
        case "$free_kb" in
          "" | *[!0-9]*)
            echo "Disk Guard free space must be a non-negative integer in KiB" >&2
            exit 1
            ;;
        esac
        if [ "''${#free_kb}" -gt 16 ]; then
          echo "Disk Guard free space must be a non-negative integer in KiB" >&2
          exit 1
        fi
      else
        if ! free_kb="$(
          timeout --kill-after=5s 30s "$df_command" -k /System/Volumes/Data 2>/dev/null \
            | awk 'NR==2 {print $4}'
        )"; then
          free_kb=""
          measurement_ok=false
        fi
        if [ "$measurement_ok" = true ]; then
          case "$free_kb" in
            "" | *[!0-9]*) measurement_ok=false ;;
          esac
          if [ "''${#free_kb}" -gt 16 ]; then
            measurement_ok=false
          fi
        fi
      fi

      category=healthy
      alert_message=""
      free_gib=""
      if [ "$measurement_ok" = true ] && ! free_gib="$(
        awk -v kb="$free_kb" 'BEGIN { printf "%.1f", kb / ${toString kbPerGib} }'
      )"; then
        measurement_ok=false
      fi

      if [ "$measurement_ok" = false ]; then
        category=check-failed
        alert_message="Disk space check failed: free space on caladan could not be measured. Check the disk and Disk Guard."
        log "free-space measurement failed"
      elif [ "$free_kb" -lt "${toString (cfg.disk.urgentFreeGb * kbPerGib)}" ]; then
        category=urgent
        alert_message="Disk space urgent: only $free_gib GiB is free (below ${
          toString cfg.disk.urgentFreeGb
        } GiB). Free space now and pause large writes."
      elif [ "$free_kb" -lt "${toString (cfg.disk.warnFreeGb * kbPerGib)}" ]; then
        category=warn
        alert_message="Disk space alert: only $free_gib GiB is free (below ${
          toString cfg.disk.warnFreeGb
        } GiB). Free space or move data soon."
      fi
      if [ "$measurement_ok" = true ]; then
        log "free space: $free_gib GiB"
      fi

      previous_category=""
      previous_alert=0
      previous_pending=none
      if [ -f "$state_file" ]; then
        if ! {
          IFS= read -r previous_category || previous_category=""
          IFS= read -r previous_alert || previous_alert=0
          IFS= read -r previous_pending || previous_pending=none
        } < "$state_file" 2>/dev/null; then
          previous_category=""
          previous_alert=0
          previous_pending=none
          warn_persistence
        fi
        case "$previous_category" in
          healthy | check-failed | warn | urgent) ;;
          *)
            previous_category=""
            previous_alert=0
            previous_pending=none
            ;;
        esac
        case "$previous_alert" in
          "" | *[!0-9]*) previous_alert=0 ;;
        esac
        if [ "''${#previous_alert}" -gt 12 ]; then
          previous_alert=0
        fi
        case "$previous_pending" in
          none | recovered | check-failed | warn | urgent) ;;
          *) previous_pending=none ;;
        esac
      fi

      should_alert=false
      alert_token=none
      next_alert="$previous_alert"
      pending_remote="$previous_pending"
      if [ "$category" = healthy ]; then
        next_alert=0
        if [ -n "$previous_category" ] && [ "$previous_category" != healthy ]; then
          should_alert=true
          alert_token=recovered
          alert_message="Disk space recovered: $free_gib GiB is free."
        fi
      elif [ "$category" != "$previous_category" ]; then
        should_alert=true
        alert_token="$category"
      elif [ "$previous_alert" -eq 0 ] \
        || [ "$now" -lt "$previous_alert" ] \
        || [ "$((now - previous_alert))" -ge 86400 ]; then
        should_alert=true
        alert_token="$category"
      fi

      if [ "$category" = healthy ]; then
        if [ "$pending_remote" != recovered ]; then
          pending_remote=none
        fi
      elif [ "$pending_remote" != "$category" ]; then
        pending_remote=none
      fi
      if [ -z "$remote_notifier" ]; then
        pending_remote=none
      fi

      if [ "$should_alert" = true ]; then
        deliver_local "$alert_message"
        if [ "$category" != healthy ]; then
          next_alert="$now"
        fi
        if [ -n "$remote_notifier" ]; then
          pending_remote="$alert_token"
        else
          pending_remote=none
        fi
      fi

      # Save local delivery state before the network call. A failed remote send
      # retries on the next run without repeating the desktop alert.
      if ! write_state; then
        :
      fi
      if [ -n "$remote_notifier" ] && [ "$pending_remote" != none ]; then
        if message_for_token "$pending_remote" && deliver_remote "$remote_message"; then
          pending_remote=none
          if ! write_state; then
            :
          fi
        fi
      fi

      log "category=$category previous=''${previous_category:-none}"

      # Cleanup uses its own six-hour stamp instead of the alert state.
      cleanup_throttle_ok() {
        local last
        last="$(cat "$cleanup_stamp" 2>/dev/null || echo 0)"
        case "$last" in
          "" | *[!0-9]*) last=0 ;;
        esac
        if [ "''${#last}" -gt 12 ]; then
          last=0
        fi
        if [ "$last" -ne 0 ] && [ "$now" -lt "$last" ]; then
          last=0
        fi
        if [ "$last" -ne 0 ]; then
          if [ "$((now - last))" -lt 21600 ]; then
            return 1
          fi
        fi
        if {
          printf '%s\n' "$now" > "$cleanup_stamp.next" \
            && chmod 600 "$cleanup_stamp.next" \
            && mv -f "$cleanup_stamp.next" "$cleanup_stamp" \
            && chmod 600 "$cleanup_stamp"
        } 2>/dev/null; then
          return 0
        fi
        # Safe cleanup must still get a chance to free space when the disk is
        # too full to persist its throttle stamp. Each command is bounded.
        warn_persistence
        return 0
      }

      # Safe cleanup only: expire the user's Nix profile generations and prune
      # the uv cache. Never automatically purge Trash or msgvault data.
      if [ "$measurement_ok" = true ] \
        && [ "$free_kb" -lt "${toString (cfg.disk.cleanupFreeGb * kbPerGib)}" ]; then
        if [ "$free_injected" = true ] && [ -z "$cleanup_override" ]; then
          log "cleanup: skipped because test free space is injected"
        elif cleanup_throttle_ok; then
          if [ -n "$cleanup_override" ]; then
            log "cleanup: test override"
            timeout --kill-after=5s 30s "$cleanup_override" >/dev/null 2>&1 \
              || log "cleanup: test override failed"
            log "cleanup: test override done"
          else
            log "cleanup: nix-collect-garbage --delete-older-than 14d"
            timeout --kill-after=30s 15m \
              nix-collect-garbage --delete-older-than 14d >/dev/null 2>&1 \
              || log "cleanup: nix-collect-garbage failed"
            log "cleanup: uv cache prune"
            # Fail fast instead of waiting minutes when another uv process
            # holds the cache lock.
            UV_LOCK_TIMEOUT=10 timeout --kill-after=30s 5m \
              uv cache prune >/dev/null 2>&1 \
              || log "cleanup: uv cache prune failed"
            after_kb=""
            if after_kb="$(
              timeout --kill-after=5s 30s "$df_command" -k /System/Volumes/Data 2>/dev/null \
                | awk 'NR==2 {print $4}'
            )"; then
              case "$after_kb" in
                "" | *[!0-9]*) after_kb="" ;;
              esac
            else
              after_kb=""
            fi
            if [ -n "$after_kb" ] && [ "''${#after_kb}" -le 16 ]; then
              after_gib="$(
                awk -v kb="$after_kb" 'BEGIN { printf "%.1f", kb / ${
                  toString kbPerGib
                } }'
              )"
              log "cleanup: done, $after_gib GiB free"
            else
              log "cleanup: done, free-space measurement unavailable"
            fi
          fi
        else
          log "cleanup: wanted but throttled"
        fi
      fi
    '';
  };

  # Deterministic tests can replace every external input:
  #   TM_CHECK_PLIST        alternate Time Machine preferences plist
  #   TM_CHECK_STATE_DIR    alternate private state directory
  #   TM_CHECK_LOG_FILE     alternate log file
  #   TM_CHECK_NOW          alternate Unix timestamp
  #   TM_CHECK_MAX_AGE_SEC  alternate staleness threshold
  #   TM_CHECK_HOST         alternate backup host
  #   TM_CHECK_REACHABLE    0/false or 1/true instead of an SMB probe
  #   TM_CHECK_NOTIFY       local notification executable, message on stdin
  #   TM_CHECK_REMOTE_NOTIFY
  #                         remote notification executable, message on stdin
  tmFreshness = pkgs.writeShellApplication {
    name = "tm-freshness";
    runtimeInputs = [ pkgs.coreutils pkgs.curl ];
    text = ''
            set -euo pipefail
            umask 077

            state_dir="''${TM_CHECK_STATE_DIR:-$HOME/Library/Application Support/tm-freshness}"
            state_file="$state_dir/state"
            log_file="''${TM_CHECK_LOG_FILE:-$HOME/Library/Logs/tm-freshness.log}"
            notify_override="''${TM_CHECK_NOTIFY:-}"
            remote_notifier=${
              lib.escapeShellArg (if cfg.remoteNotifier == null then "" else cfg.remoteNotifier)
            }
            if [ "''${TM_CHECK_REMOTE_NOTIFY+x}" = x ]; then
              remote_notifier="$TM_CHECK_REMOTE_NOTIFY"
            fi

            heartbeat_url_file=${
              lib.escapeShellArg (if cfg.heartbeatDir == null then "" else "${cfg.heartbeatDir}/tm-freshness.url")
            }
            ping_heartbeat() {
              if [ -n "$heartbeat_url_file" ] && [ -r "$heartbeat_url_file" ]; then
                curl -fsS --retry 3 --max-time 10 "$(cat "$heartbeat_url_file")" >/dev/null 2>&1 || true
              fi
            }

            persistence_warning_emitted=false
            warn_persistence() {
              if [ "$persistence_warning_emitted" = false ]; then
                printf '%s\n' \
                  "Time Machine Check persistence unavailable; notifications will continue without durable suppression" \
                  >&2 || true
                persistence_warning_emitted=true
              fi
            }

            if ! mkdir -p "$state_dir" 2>/dev/null; then
              warn_persistence
            fi
            if [ -d "$state_dir" ] && ! chmod 700 "$state_dir" 2>/dev/null; then
              warn_persistence
            fi
            if ! mkdir -p "$(dirname "$log_file")" 2>/dev/null; then
              warn_persistence
            fi
            if ! touch "$log_file" 2>/dev/null; then
              warn_persistence
            fi
            if [ -f "$log_file" ] && ! chmod 600 "$log_file" 2>/dev/null; then
              warn_persistence
            fi
            if [ -f "$state_file" ] && ! chmod 600 "$state_file" 2>/dev/null; then
              warn_persistence
            fi

            log() {
              if ! {
                printf '%s %s\n' "$(date '+%Y-%m-%dT%H:%M:%S%z')" "$1" >> "$log_file"
              } 2>/dev/null; then
                warn_persistence
              fi
              return 0
            }

            write_state() {
              if {
                printf '%s\n%s\n%s\n' "$category" "$next_alert" "$pending_remote" > "$state_file.next" \
                  && chmod 600 "$state_file.next" \
                  && mv -f "$state_file.next" "$state_file" \
                  && chmod 600 "$state_file"
              } 2>/dev/null; then
                return 0
              fi
              warn_persistence
              log "state persistence failed"
              return 1
            }

            deliver_local() {
              local message="$1"
              log "ALERT category=$category"

              if [ -n "$notify_override" ]; then
                if ! printf '%s\n' "$message" \
                  | timeout --kill-after=5s 30s "$notify_override"
                then
                  log "local test notification failed"
                fi
                return
              fi

              # Pass the message as argv instead of interpolating it into AppleScript.
              # Every message is selected from the fixed strings below.
              if ! timeout --kill-after=5s 30s /usr/bin/osascript - "$message" <<'APPLESCRIPT'
      on run argv
        display notification (item 1 of argv) with title "Time Machine Check"
      end run
      APPLESCRIPT
              then
                log "local notification failed"
              fi
            }

            message_for_token() {
              case "$1" in
                history-missing)
                  remote_message="Time Machine alert: backup history is missing. Check Time Machine settings on caladan."
                  ;;
                history-unreadable)
                  remote_message="Time Machine alert: backup history cannot be read. Check Time Machine settings on caladan."
                  ;;
                destination-missing)
                  remote_message="Time Machine alert: no destination matches the configured backup server. Check Time Machine settings on caladan."
                  ;;
                snapshot-missing)
                  remote_message="Time Machine alert: no completed backup is recorded. Check Time Machine settings on caladan."
                  ;;
                snapshot-invalid)
                  remote_message="Time Machine alert: the completed backup time is invalid. Check Time Machine settings on caladan."
                  ;;
                stale-unreachable)
                  remote_message="Time Machine alert: no recent backup, and the backup server is unreachable. Check the server and Time Machine on caladan."
                  ;;
                stale)
                  remote_message="Time Machine alert: no backup completed within ${toString cfg.timeMachine.maxAgeHours} hours. Open Time Machine settings on caladan."
                  ;;
                unreachable)
                  remote_message="Time Machine alert: the backup server is unreachable over SMB. Check its power and network."
                  ;;
                recovered)
                  remote_message="Time Machine recovered: the backup is recent, and the backup server is reachable."
                  ;;
                *) return 1 ;;
              esac
            }

            deliver_remote() {
              local message="$1"
              if ! printf '%s\n' "$message" \
                | timeout --kill-after=5s 30s "$remote_notifier"
              then
                log "remote notification failed; will retry on next run"
                return 1
              fi
            }

            default_host=${lib.escapeShellArg cfg.timeMachine.host}
            host="''${TM_CHECK_HOST:-$default_host}"
            plist="''${TM_CHECK_PLIST:-/Library/Preferences/com.apple.TimeMachine.plist}"
            max_age_sec="''${TM_CHECK_MAX_AGE_SEC:-${toString (cfg.timeMachine.maxAgeHours * 3600)}}"
            now="''${TM_CHECK_NOW:-$(date +%s)}"

            case "$now" in
              "" | *[!0-9]*)
                echo "Time Machine test time must be a non-negative Unix timestamp" >&2
                exit 1
                ;;
            esac
            if [ "''${#now}" -gt 12 ]; then
              echo "Time Machine test time must be a non-negative Unix timestamp" >&2
              exit 1
            fi

            case "$max_age_sec" in
              "" | *[!0-9]*)
                echo "Time Machine maximum age must be a positive integer" >&2
                exit 1
                ;;
            esac
            if [ "$max_age_sec" -eq 0 ] || [ "''${#max_age_sec}" -gt 12 ]; then
              echo "Time Machine maximum age must be a positive integer" >&2
              exit 1
            fi

            reachable=false
            case "''${TM_CHECK_REACHABLE:-}" in
              "")
                probe_attempt=1
                while [ "$probe_attempt" -le 3 ]; do
                  if /usr/bin/nc -z -G 5 "$host" ${toString cfg.timeMachine.port} >/dev/null 2>&1; then
                    reachable=true
                    break
                  fi
                  if [ "$probe_attempt" -lt 3 ]; then
                    sleep 2
                  fi
                  probe_attempt="$((probe_attempt + 1))"
                done
                ;;
              1 | true) reachable=true ;;
              0 | false) reachable=false ;;
              *)
                echo "TM_CHECK_REACHABLE must be 0, 1, false, or true" >&2
                exit 1
                ;;
            esac

            category=""
            alert_message=""
            age_hours=""
            if [ ! -f "$plist" ]; then
              category="history-missing"
              alert_message="Time Machine alert: backup history is missing. Check Time Machine settings on caladan."
            elif [ ! -r "$plist" ]; then
              category="history-unreadable"
              alert_message="Time Machine alert: backup history cannot be read. Check Time Machine settings on caladan."
            else
              # Find the destination whose SMB URL host matches the configured
              # host, so an old destination cannot make the active one look fresh.
              destination_count="$(
                /usr/bin/plutil -extract Destinations raw -o - "$plist" 2>/dev/null
              )" || destination_count=0
              case "$destination_count" in
                "" | *[!0-9]*) destination_count=0 ;;
              esac
              if [ "''${#destination_count}" -gt 3 ] || [ "$destination_count" -gt 100 ]; then
                destination_count=0
              fi

              wanted_host="$(printf '%s' "$host" | tr '[:upper:]' '[:lower:]')"
              wanted_host="''${wanted_host%.}"
              destination_index=""
              index=0
              while [ "$index" -lt "$destination_count" ]; do
                destination_url="$(
                  /usr/bin/plutil \
                    -extract "Destinations.$index.NetworkURL" raw -o - "$plist" 2>/dev/null
                )" || destination_url=""
                destination_authority="''${destination_url#*://}"
                destination_authority="''${destination_authority%%/*}"
                destination_host="''${destination_authority##*@}"
                destination_host="''${destination_host%%:*}"
                destination_host="$(
                  printf '%s' "$destination_host" | tr '[:upper:]' '[:lower:]'
                )"
                destination_host="''${destination_host%.}"
                if [ -n "$destination_host" ] && [ "$destination_host" = "$wanted_host" ]; then
                  destination_index="$index"
                  break
                fi
                index="$((index + 1))"
              done

              if [ -z "$destination_index" ]; then
                category="destination-missing"
                alert_message="Time Machine alert: no destination matches the configured backup server. Check Time Machine settings on caladan."
              else
                # SnapshotDates contains durable UTC completion dates. Reading the
                # plist avoids mounting the backup or waiting for tmutil to contact it.
                snapshot_dates="$(
                  /usr/bin/plutil \
                    -extract "Destinations.$destination_index.SnapshotDates" xml1 -o - "$plist" 2>/dev/null \
                    | /usr/bin/xmllint --xpath '/plist/array/date/text()' - 2>/dev/null
                )" || snapshot_dates=""
              fi

              if [ -n "$category" ]; then
                :
              elif [ -z "$snapshot_dates" ]; then
                category="snapshot-missing"
                alert_message="Time Machine alert: no completed backup is recorded. Check Time Machine settings on caladan."
              else
                # UTC ISO 8601 dates sort chronologically, so this remains correct
                # even if the plist array is not in order.
                latest_snapshot="$(printf '%s\n' "$snapshot_dates" | LC_ALL=C sort | tail -n 1)"
                snapshot_epoch="$(date -d "$latest_snapshot" +%s 2>/dev/null || true)"

                case "$snapshot_epoch" in
                  "" | *[!0-9]*) snapshot_epoch=0 ;;
                esac

                if [ "$snapshot_epoch" -eq 0 ] || [ "$snapshot_epoch" -gt "$((now + 300))" ]; then
                  category="snapshot-invalid"
                  alert_message="Time Machine alert: the completed backup time is invalid. Check Time Machine settings on caladan."
                else
                  age_sec="$((now - snapshot_epoch))"
                  if [ "$age_sec" -lt 0 ]; then
                    age_sec=0
                  fi
                  age_hours="$((age_sec / 3600))"

                  if [ "$age_sec" -gt "$max_age_sec" ] && [ "$reachable" = false ]; then
                    category="stale-unreachable"
                    alert_message="Time Machine alert: no recent backup, and the backup server is unreachable. Check the server and Time Machine on caladan."
                  elif [ "$age_sec" -gt "$max_age_sec" ]; then
                    category="stale"
                    alert_message="Time Machine alert: no backup completed within ${toString cfg.timeMachine.maxAgeHours} hours. Open Time Machine settings on caladan."
                  elif [ "$reachable" = false ]; then
                    category="unreachable"
                    alert_message="Time Machine alert: the backup server is unreachable over SMB. Check its power and network."
                  else
                    category="healthy"
                  fi
                fi
              fi
            fi

            previous_category=""
            previous_alert=0
            previous_pending=none
            if [ -f "$state_file" ]; then
              if ! {
                IFS= read -r previous_category || previous_category=""
                IFS= read -r previous_alert || previous_alert=0
                IFS= read -r previous_pending || previous_pending=none
              } < "$state_file" 2>/dev/null; then
                previous_category=""
                previous_alert=0
                previous_pending=none
                warn_persistence
              fi
              case "$previous_category" in
                healthy | history-missing | history-unreadable | destination-missing | snapshot-missing | snapshot-invalid | stale-unreachable | stale | unreachable)
                  ;;
                *)
                  previous_category=""
                  previous_alert=0
                  previous_pending=none
                  ;;
              esac
              case "$previous_alert" in
                "" | *[!0-9]*) previous_alert=0 ;;
              esac
              if [ "''${#previous_alert}" -gt 12 ]; then
                previous_alert=0
              fi
              case "$previous_pending" in
                none | recovered | history-missing | history-unreadable | destination-missing | snapshot-missing | snapshot-invalid | stale-unreachable | stale | unreachable)
                  ;;
                *) previous_pending=none ;;
              esac
            fi

            should_alert=false
            alert_token=none
            next_alert="$previous_alert"
            pending_remote="$previous_pending"
            if [ "$category" = healthy ]; then
              next_alert=0
              if [ -n "$previous_category" ] && [ "$previous_category" != healthy ]; then
                should_alert=true
                alert_token=recovered
                alert_message="Time Machine recovered: the backup is recent, and the backup server is reachable."
              fi
            elif [ "$category" != "$previous_category" ]; then
              should_alert=true
              alert_token="$category"
            elif [ "$previous_alert" -eq 0 ] \
              || [ "$now" -lt "$previous_alert" ] \
              || [ "$((now - previous_alert))" -ge 86400 ]; then
              should_alert=true
              alert_token="$category"
            fi

            # A pending token is useful only while it still describes the
            # current state. Category changes supersede an undelivered message.
            if [ "$category" = healthy ]; then
              if [ "$pending_remote" != recovered ]; then
                pending_remote=none
              fi
            elif [ "$pending_remote" != "$category" ]; then
              pending_remote=none
            fi
            if [ -z "$remote_notifier" ]; then
              pending_remote=none
            fi

            if [ "$should_alert" = true ]; then
              deliver_local "$alert_message"
              if [ "$category" != healthy ]; then
                next_alert="$now"
              fi
              if [ -n "$remote_notifier" ]; then
                pending_remote="$alert_token"
              else
                pending_remote=none
              fi
            fi

            # Save local delivery state before the network call. A failed remote
            # send therefore retries hourly without repeating the desktop alert.
            if ! write_state; then
              :
            fi
            if [ -n "$remote_notifier" ] && [ "$pending_remote" != none ]; then
              if message_for_token "$pending_remote" && deliver_remote "$remote_message"; then
                pending_remote=none
                if ! write_state; then
                  :
                fi
              fi
            fi

            if [ "$category" = healthy ]; then
              log "category=healthy age_hours=$age_hours reachable=true"
              ping_heartbeat
            else
              log "category=$category previous=''${previous_category:-none}"
            fi
    '';
  };

  # tm-freshness reads a system Time Machine preferences file that macOS gates
  # by the calling binary's TCC identity. That identity is the resolved real
  # path (Nix store paths and symlinks to them both change on every rebuild,
  # which silently drops a Full Disk Access grant); see stable-bin.nix.
  tmFreshnessStable = stableBin {
    name = "tm-freshness";
    package = tmFreshness;
  };

  # Off-site (cloud) backup freshness. Generic: reads a last-success date out
  # of whatever plist the configured agent maintains, so the module carries no
  # account identity. Deterministic test overrides:
  #   OFFSITE_CHECK_PLIST        alternate backup status plist
  #   OFFSITE_CHECK_STATE_DIR    alternate private state directory
  #   OFFSITE_CHECK_LOG_FILE     alternate log file
  #   OFFSITE_CHECK_NOW          alternate Unix timestamp
  #   OFFSITE_CHECK_MAX_AGE_SEC  alternate staleness threshold
  #   OFFSITE_CHECK_NOTIFY       local notification executable, message on stdin
  #   OFFSITE_CHECK_REMOTE_NOTIFY
  #                              remote notification executable, message on stdin
  #   OFFSITE_CHECK_COVERAGE     coverage executable; nonzero means incomplete
  offsiteFreshness = pkgs.writeShellApplication {
    name = "offsite-freshness";
    runtimeInputs = [ pkgs.coreutils ];
    text = ''
            set -euo pipefail
            umask 077

            state_dir="''${OFFSITE_CHECK_STATE_DIR:-$HOME/Library/Application Support/offsite-freshness}"
            state_file="$state_dir/state"
            log_file="''${OFFSITE_CHECK_LOG_FILE:-$HOME/Library/Logs/offsite-freshness.log}"
            notify_override="''${OFFSITE_CHECK_NOTIFY:-}"
            remote_notifier=${
              lib.escapeShellArg (if cfg.remoteNotifier == null then "" else cfg.remoteNotifier)
            }
            if [ "''${OFFSITE_CHECK_REMOTE_NOTIFY+x}" = x ]; then
              remote_notifier="$OFFSITE_CHECK_REMOTE_NOTIFY"
            fi
            coverage_checker=${
              lib.escapeShellArg (
                if cfg.offsite.coverageCheck == null then "" else cfg.offsite.coverageCheck
              )
            }
            if [ "''${OFFSITE_CHECK_COVERAGE+x}" = x ]; then
              coverage_checker="$OFFSITE_CHECK_COVERAGE"
            fi

            persistence_warning_emitted=false
            warn_persistence() {
              if [ "$persistence_warning_emitted" = false ]; then
                printf '%s\n' \
                  "Off-site Backup Check persistence unavailable; notifications will continue without durable suppression" \
                  >&2 || true
                persistence_warning_emitted=true
              fi
            }

            if ! mkdir -p "$state_dir" 2>/dev/null; then
              warn_persistence
            fi
            if [ -d "$state_dir" ] && ! chmod 700 "$state_dir" 2>/dev/null; then
              warn_persistence
            fi
            if ! mkdir -p "$(dirname "$log_file")" 2>/dev/null; then
              warn_persistence
            fi
            if ! touch "$log_file" 2>/dev/null; then
              warn_persistence
            fi
            if [ -f "$log_file" ] && ! chmod 600 "$log_file" 2>/dev/null; then
              warn_persistence
            fi
            if [ -f "$state_file" ] && ! chmod 600 "$state_file" 2>/dev/null; then
              warn_persistence
            fi

            log() {
              if ! {
                printf '%s %s\n' "$(date '+%Y-%m-%dT%H:%M:%S%z')" "$1" >> "$log_file"
              } 2>/dev/null; then
                warn_persistence
              fi
              return 0
            }

            write_state() {
              if {
                printf '%s\n%s\n%s\n' "$category" "$next_alert" "$pending_remote" > "$state_file.next" \
                  && chmod 600 "$state_file.next" \
                  && mv -f "$state_file.next" "$state_file" \
                  && chmod 600 "$state_file"
              } 2>/dev/null; then
                return 0
              fi
              warn_persistence
              log "state persistence failed"
              return 1
            }

            deliver_local() {
              local message="$1"
              log "ALERT category=$category"

              if [ -n "$notify_override" ]; then
                if ! printf '%s\n' "$message" \
                  | timeout --kill-after=5s 30s "$notify_override"
                then
                  log "local test notification failed"
                fi
                return
              fi

              if ! timeout --kill-after=5s 30s /usr/bin/osascript - "$message" <<'APPLESCRIPT'
      on run argv
        display notification (item 1 of argv) with title "Off-site Backup Check"
      end run
      APPLESCRIPT
              then
                log "local notification failed"
              fi
            }

            message_for_token() {
              case "$1" in
                state-missing)
                  remote_message="Off-site backup alert: the backup status file is missing. Check the backup app on caladan."
                  ;;
                state-unreadable)
                  remote_message="Off-site backup alert: the backup status cannot be read. Check the backup app on caladan."
                  ;;
                success-missing)
                  remote_message="Off-site backup alert: no successful backup time is recorded. Check the backup app on caladan."
                  ;;
                success-invalid)
                  remote_message="Off-site backup alert: the recorded success time is invalid. Check the backup app on caladan."
                  ;;
                stale)
                  remote_message="Off-site backup alert: no successful backup completed within ${toString cfg.offsite.maxAgeHours} hours. Open the backup app on caladan."
                  ;;
                coverage-incomplete)
                  remote_message="Off-site backup alert: coverage is incomplete or cannot be verified. Run the local coverage and status checks on caladan."
                  ;;
                recovered)
                  remote_message="Off-site backup recovered: the latest success is recent, and no material backup queue is idle. An active upload may still be completing."
                  ;;
                *) return 1 ;;
              esac
            }

            deliver_remote() {
              local message="$1"
              if ! printf '%s\n' "$message" \
                | timeout --kill-after=5s 30s "$remote_notifier"
              then
                log "remote notification failed; will retry on next run"
                return 1
              fi
            }

            default_plist=${lib.escapeShellArg (toString cfg.offsite.successPlist)}
            plist="''${OFFSITE_CHECK_PLIST:-$default_plist}"
            max_age_sec="''${OFFSITE_CHECK_MAX_AGE_SEC:-${toString (cfg.offsite.maxAgeHours * 3600)}}"
            now="''${OFFSITE_CHECK_NOW:-$(date +%s)}"

            case "$now" in
              "" | *[!0-9]*)
                echo "Off-site backup test time must be a non-negative Unix timestamp" >&2
                exit 1
                ;;
            esac
            if [ "''${#now}" -gt 12 ]; then
              echo "Off-site backup test time must be a non-negative Unix timestamp" >&2
              exit 1
            fi

            case "$max_age_sec" in
              "" | *[!0-9]*)
                echo "Off-site backup maximum age must be a positive integer" >&2
                exit 1
                ;;
            esac
            if [ "$max_age_sec" -eq 0 ] || [ "''${#max_age_sec}" -gt 12 ]; then
              echo "Off-site backup maximum age must be a positive integer" >&2
              exit 1
            fi

            category=""
            alert_message=""
            age_hours=""
            if [ ! -f "$plist" ]; then
              category="state-missing"
              alert_message="Off-site backup alert: the backup status file is missing. Check the backup app on caladan."
            elif [ ! -r "$plist" ]; then
              category="state-unreadable"
              alert_message="Off-site backup alert: the backup status cannot be read. Check the backup app on caladan."
            else
              raw="$(/usr/bin/plutil -extract ${lib.escapeShellArg cfg.offsite.successKey} raw -o - "$plist" 2>/dev/null || true)"
              if [ -z "$raw" ]; then
                category="success-missing"
                alert_message="Off-site backup alert: no successful backup time is recorded. Check the backup app on caladan."
              else
                epoch="$(date -d "$raw" +%s 2>/dev/null || true)"
                case "$epoch" in
                  "" | *[!0-9]*) epoch=0 ;;
                esac

                if [ "$epoch" -eq 0 ] || [ "$epoch" -gt "$((now + 300))" ]; then
                  category="success-invalid"
                  alert_message="Off-site backup alert: the recorded success time is invalid. Check the backup app on caladan."
                else
                  age_sec="$((now - epoch))"
                  if [ "$age_sec" -lt 0 ]; then
                    age_sec=0
                  fi
                  age_hours="$((age_sec / 3600))"
                  if [ "$age_sec" -gt "$max_age_sec" ]; then
                    category="stale"
                    alert_message="Off-site backup alert: no successful backup completed within ${toString cfg.offsite.maxAgeHours} hours. Open the backup app on caladan."
                  else
                    category="healthy"
                  fi
                fi
              fi
            fi

            if [ "$category" = healthy ] && [ -n "$coverage_checker" ]; then
              if ! timeout --kill-after=5s 30s "$coverage_checker" >/dev/null 2>&1; then
                category="coverage-incomplete"
                alert_message="Off-site backup alert: coverage is incomplete or cannot be verified. Run the local coverage and status checks on caladan."
              fi
            fi

            previous_category=""
            previous_alert=0
            previous_pending=none
            if [ -f "$state_file" ]; then
              if ! {
                IFS= read -r previous_category || previous_category=""
                IFS= read -r previous_alert || previous_alert=0
                IFS= read -r previous_pending || previous_pending=none
              } < "$state_file" 2>/dev/null; then
                previous_category=""
                previous_alert=0
                previous_pending=none
                warn_persistence
              fi
              case "$previous_category" in
                healthy | state-missing | state-unreadable | success-missing | success-invalid | stale | coverage-incomplete)
                  ;;
                *)
                  previous_category=""
                  previous_alert=0
                  previous_pending=none
                  ;;
              esac
              case "$previous_alert" in
                "" | *[!0-9]*) previous_alert=0 ;;
              esac
              if [ "''${#previous_alert}" -gt 12 ]; then
                previous_alert=0
              fi
              case "$previous_pending" in
                none | recovered | state-missing | state-unreadable | success-missing | success-invalid | stale | coverage-incomplete)
                  ;;
                *) previous_pending=none ;;
              esac
            fi

            should_alert=false
            alert_token=none
            next_alert="$previous_alert"
            pending_remote="$previous_pending"
            if [ "$category" = healthy ]; then
              next_alert=0
              if [ -n "$previous_category" ] && [ "$previous_category" != healthy ]; then
                should_alert=true
                alert_token=recovered
                alert_message="Off-site backup recovered: the latest success is recent, and no material backup queue is idle. An active upload may still be completing."
              fi
            elif [ "$category" != "$previous_category" ]; then
              should_alert=true
              alert_token="$category"
            elif [ "$previous_alert" -eq 0 ] \
              || [ "$now" -lt "$previous_alert" ] \
              || [ "$((now - previous_alert))" -ge 86400 ]; then
              should_alert=true
              alert_token="$category"
            fi

            if [ "$category" = healthy ]; then
              if [ "$pending_remote" != recovered ]; then
                pending_remote=none
              fi
            elif [ "$pending_remote" != "$category" ]; then
              pending_remote=none
            fi
            if [ -z "$remote_notifier" ]; then
              pending_remote=none
            fi

            if [ "$should_alert" = true ]; then
              deliver_local "$alert_message"
              if [ "$category" != healthy ]; then
                next_alert="$now"
              fi
              if [ -n "$remote_notifier" ]; then
                pending_remote="$alert_token"
              else
                pending_remote=none
              fi
            fi

            if ! write_state; then
              :
            fi
            if [ -n "$remote_notifier" ] && [ "$pending_remote" != none ]; then
              if message_for_token "$pending_remote" && deliver_remote "$remote_message"; then
                pending_remote=none
                if ! write_state; then
                  :
                fi
              fi
            fi

            if [ "$category" = healthy ]; then
              log "category=healthy age_hours=$age_hours"
            else
              log "category=$category previous=''${previous_category:-none}"
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
    enable = lib.mkEnableOption "disk-space and backup freshness guardrails";

    remoteNotifier = lib.mkOption {
      type = lib.types.nullOr lib.types.str;
      default = null;
      description = ''
        Optional absolute path to a notification program. Each disk-space or
        backup guardrail passes one fixed alert line on standard input. A
        failed send leaves a small pending token so the next run retries the
        remote delivery without repeating the local macOS notification.
      '';
    };

    heartbeatDir = lib.mkOption {
      type = lib.types.nullOr lib.types.str;
      default = null;
      description = ''
        Optional absolute path to a directory of per-job dead-man's-switch
        ping URLs (e.g. Healthchecks.io), one owner-only file per job named
        "<job>.url" - never in Nix or Git, since the URL itself is a
        capability token. A guardrail pings its own file's URL only from the
        same code path that already decided its outcome is healthy, and
        silently does nothing if the file for its job is absent, so this is
        safe to enable before every check-generating job has a file yet.
      '';
    };

    disk = {
      warnFreeGb = lib.mkOption {
        type = lib.types.ints.positive;
        default = 20;
        description = "Notify on entry and at most daily while free space stays below this many GiB.";
      };

      urgentFreeGb = lib.mkOption {
        type = lib.types.ints.positive;
        default = 10;
        description = "Notify on entry and at most daily while free space stays below this many GiB.";
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

    offsite = {
      successPlist = lib.mkOption {
        type = lib.types.nullOr lib.types.str;
        default = null;
        description = ''
          Path to a plist whose successKey date records the last successful
          off-site (cloud) backup. Null disables the check. The value usually
          names an account, so set it from the private repo.
        '';
      };

      successKey = lib.mkOption {
        type = lib.types.str;
        default = "BackupSuccessTime";
        description = "Plist key holding the last-success date.";
      };

      maxAgeHours = lib.mkOption {
        type = lib.types.ints.positive;
        default = 30;
        description = "Alert when the last off-site backup success is older than this many hours.";
      };

      coverageCheck = lib.mkOption {
        type = lib.types.nullOr lib.types.str;
        default = null;
        description = ''
          Optional absolute path to a read-only coverage check. A nonzero exit
          status marks an otherwise fresh off-site backup incomplete. Put
          provider- and account-specific inspection in the private config.
        '';
      };
    };
  };

  config = lib.mkIf cfg.enable {
    assertions = [
      {
        assertion =
          cfg.disk.warnFreeGb > cfg.disk.urgentFreeGb && cfg.disk.urgentFreeGb > cfg.disk.cleanupFreeGb;
        message = "services.healthGuardrails disk thresholds must satisfy warn > urgent > cleanup";
      }
      {
        assertion = cfg.remoteNotifier == null || lib.hasPrefix "/" cfg.remoteNotifier;
        message = "services.healthGuardrails.remoteNotifier must be an absolute program path";
      }
      {
        assertion = cfg.offsite.coverageCheck == null || lib.hasPrefix "/" cfg.offsite.coverageCheck;
        message = "services.healthGuardrails.offsite.coverageCheck must be an absolute program path";
      }
    ];

    launchd.user.agents.disk-guard.serviceConfig = {
      ProgramArguments = wrapped diskGuard "disk-guard";
      EnvironmentVariables.HOME = "/Users/${user}";
      StartInterval = 1800;
      RunAtLoad = true;
      Umask = 63;
      StandardErrorPath = "/Users/${user}/Library/Logs/disk-guard.launchd.err.log";
      StandardOutPath = "/Users/${user}/Library/Logs/disk-guard.launchd.out.log";
    };

    system.activationScripts.postActivation.text = tmFreshnessStable.activationScript;

    launchd.user.agents.tm-freshness.serviceConfig = {
      ProgramArguments = [
        "/bin/sh"
        "-c"
        "/bin/wait4path ${tmFreshnessStable.stablePath} && exec ${tmFreshnessStable.stablePath}"
      ];
      EnvironmentVariables.HOME = "/Users/${user}";
      StartInterval = 3600;
      RunAtLoad = true;
      Umask = 63;
      StandardErrorPath = "/Users/${user}/Library/Logs/tm-freshness.launchd.err.log";
      StandardOutPath = "/Users/${user}/Library/Logs/tm-freshness.launchd.out.log";
    };

    launchd.user.agents.offsite-freshness = lib.mkIf (cfg.offsite.successPlist != null) {
      serviceConfig = {
        ProgramArguments = wrapped offsiteFreshness "offsite-freshness";
        EnvironmentVariables.HOME = "/Users/${user}";
        StartInterval = 3600;
        RunAtLoad = true;
        Umask = 63;
        StandardErrorPath = "/Users/${user}/Library/Logs/offsite-freshness.launchd.err.log";
        StandardOutPath = "/Users/${user}/Library/Logs/offsite-freshness.launchd.out.log";
      };
    };
  };
}

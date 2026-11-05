{
  config,
  lib,
  pkgs,
  ...
}:

let
  cfg = config.services.kata;
  inherit (pkgs.stdenv.hostPlatform) isDarwin isLinux;
  tomlFormat = pkgs.formats.toml { };
  logDirectory = "${config.home.homeDirectory}/Library/Logs";

  configData =
    lib.optionalAttrs cfg.client.enable {
      active_daemon = cfg.client.daemonName;
      daemon = [
        {
          name = cfg.client.daemonName;
          url = cfg.client.url;
          token_env = cfg.client.tokenEnvironment;
        }
      ];
    }
    // lib.optionalAttrs cfg.server.enable {
      listen = cfg.server.listen;
      # The daemon already opts in through KATA_TRUST_PRIVATE_NETWORK=1 in its
      # unit, but CLI clients on the server host read this same config.toml and
      # reject the non-loopback web.public_origin unless the shared file also
      # carries the non-secret opt-in.
      auth.trust_private_network = true;
      web = {
        public_origin = cfg.server.publicOrigin;
        allowed_hosts = cfg.server.allowedHosts;
      };
    };

  configFile = tomlFormat.generate "kata-config.toml" configData;

  backupScript = pkgs.writeShellApplication {
    name = "kata-backup";
    runtimeInputs = [
      cfg.package
      pkgs.coreutils
      pkgs.trash-cli
    ]
    ++ lib.optionals cfg.backup.offHost.enable [ pkgs.openssh ];
    text = ''
      set -euo pipefail
      umask 077

      # Export is host-local and must not inherit client routing or credentials.
      unset KATA_AUTH_TOKEN KATA_SERVER

      backup_dir=${lib.escapeShellArg cfg.backup.directory}
      database_path=${lib.escapeShellArg "${cfg.homeDirectory}/kata.db"}
      install -d -m 0700 "$backup_dir"

      staging_dir="$(mktemp -d "$backup_dir/.kata-backup.XXXXXXXX")"
      export_home="$staging_dir/home"
      install -d -m 0700 "$export_home"
      cleanup() {
        if [[ -d "$staging_dir" ]]; then
          trash-put -- "$staging_dir" >/dev/null
        fi
      }
      trap cleanup EXIT

      timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
      export_file="$staging_dir/kata.jsonl"
      final_file="$backup_dir/kata-$timestamp.jsonl"
      if [[ -e "$final_file" ]]; then
        echo "Refusing to replace an existing Kata backup: $final_file" >&2
        exit 1
      fi

      (
        cd "$staging_dir"
        KATA_HOME="$export_home" KATA_DSN="$database_path" \
          kata export --allow-running-daemon --output "$export_file"
      )
      if [[ ! -s "$export_file" ]]; then
        echo "Kata export did not create a nonempty backup" >&2
        exit 1
      fi

      chmod 0600 "$export_file"
      mv "$export_file" "$final_file"
      trash-put -- "$staging_dir" >/dev/null
      trap - EXIT

      echo "Created owner-only Kata backup: $final_file"

      ${lib.optionalString cfg.backup.offHost.enable ''
        off_host=${lib.escapeShellArg cfg.backup.offHost.host}
        off_host_directory=${lib.escapeShellArg cfg.backup.offHost.directory}
        identity_file=${lib.escapeShellArg cfg.backup.offHost.identityFile}
        ssh_options=(
          -F /dev/null
          -o BatchMode=yes
          -o ConnectTimeout=15
          -o IdentitiesOnly=yes
          -o StrictHostKeyChecking=yes
          -o "UserKnownHostsFile=$HOME/.ssh/known_hosts"
          -i "$identity_file"
        )

        transfer_backup() {
          local local_file="$1"
          local file_name
          local remote_staging
          local remote_final
          local prepare_command
          local local_checksum
          local remote_checksum
          local finalize_command

          file_name="$(basename "$local_file")"
          # Reuse one staging path per immutable backup. If a transfer is
          # interrupted, the next attempt overwrites the partial instead of
          # leaking a new remote file on every retry.
          remote_staging="$off_host_directory/.$file_name.partial"
          remote_final="$off_host_directory/$file_name"

          if env -u KATA_AUTH_TOKEN -u SSH_AUTH_SOCK \
            ssh "''${ssh_options[@]}" "$off_host" "test -e '$remote_final'"; then
            echo "Off-host Kata backup already exists: $off_host:$remote_final"
            return
          fi

          prepare_command="umask 077; mkdir -p '$off_host_directory' && chmod 0700 '$off_host_directory' && test ! -d '$remote_staging' && test ! -e '$remote_final'"
          env -u KATA_AUTH_TOKEN -u SSH_AUTH_SOCK \
            ssh "''${ssh_options[@]}" "$off_host" "$prepare_command"

          env -u KATA_AUTH_TOKEN -u SSH_AUTH_SOCK \
            scp -q "''${ssh_options[@]}" "$local_file" "$off_host:$remote_staging"

          local_checksum="$(sha256sum "$local_file" | cut -d ' ' -f 1)"
          remote_checksum="$(
            env -u KATA_AUTH_TOKEN -u SSH_AUTH_SOCK \
              ssh "''${ssh_options[@]}" "$off_host" "cat '$remote_staging'" \
              | sha256sum | cut -d ' ' -f 1
          )"
          if [[ "$local_checksum" != "$remote_checksum" ]]; then
            echo "Off-host Kata backup checksum mismatch" >&2
            exit 1
          fi

          finalize_command="test -s '$remote_staging' && chmod 0600 '$remote_staging' && test ! -e '$remote_final' && mv '$remote_staging' '$remote_final'"
          env -u KATA_AUTH_TOKEN -u SSH_AUTH_SOCK \
            ssh "''${ssh_options[@]}" "$off_host" "$finalize_command"

          echo "Created checksummed off-host Kata backup: $off_host:$remote_final"
        }

        shopt -s nullglob
        for local_file in "$backup_dir"/kata-*.jsonl; do
          transfer_backup "$local_file"
        done
      ''}
      ${lib.optionalString (cfg.backup.successCommand != null) cfg.backup.successCommand}
    '';
  };

  # launchd has no EnvironmentFile, so the macOS daemon starts through this
  # launcher. It loads only the owner-only token file and first waits up to
  # two minutes for the private listen address, because an overlay network
  # such as Tailscale can assign it after launchd starts login agents.
  serverLauncher = pkgs.writeShellApplication {
    name = "kata-server";
    runtimeInputs = [
      pkgs.coreutils
      pkgs.gnugrep
    ];
    text = ''
      environment_file=${lib.escapeShellArg cfg.server.environmentFile}
      listen=${lib.escapeShellArg cfg.server.listen}

      if [[ ! -f "$environment_file" || -L "$environment_file" ]]; then
        echo "Kata server environment file is missing or is not a regular file" >&2
        exit 1
      fi
      if [[ "$(/usr/bin/stat -f '%u' "$environment_file")" != "$(id -u)" ||
        "$(/usr/bin/stat -f '%Lp' "$environment_file")" != 600 ]]; then
        echo "Kata server environment file must be owned by the service user with mode 0600" >&2
        exit 1
      fi

      listen_host="''${listen%:*}"
      for _ in $(seq 60); do
        if /sbin/ifconfig | grep -Fq "inet $listen_host "; then
          break
        fi
        sleep 2
      done

      set -a
      # shellcheck source=/dev/null
      source "$environment_file"
      set +a
      if [[ -z "''${KATA_AUTH_TOKEN:-}" ]]; then
        echo "Kata server environment file does not set KATA_AUTH_TOKEN" >&2
        exit 1
      fi

      exec ${cfg.package}/bin/kata daemon start --foreground --listen "$listen"
    '';
  };
in
{
  options.services.kata = {
    enable = lib.mkEnableOption "a managed Kata work-ledger deployment";

    package = lib.mkOption {
      type = lib.types.package;
      default = pkgs.callPackage ./kata.nix { };
      defaultText = lib.literalExpression "pkgs.callPackage ./kata.nix { }";
      description = "Pinned Kata package used by the client, daemon, and backup job.";
    };

    homeDirectory = lib.mkOption {
      type = lib.types.str;
      default = "${config.home.homeDirectory}/.kata";
      description = "Runtime KATA_HOME containing the config and live SQLite database.";
    };

    client = {
      enable = lib.mkEnableOption "the named-daemon client catalog";

      daemonName = lib.mkOption {
        type = lib.types.str;
        description = "Name of the active shared Kata daemon.";
      };

      url = lib.mkOption {
        type = lib.types.str;
        description = "Non-secret URL of the shared Kata daemon.";
      };

      tokenEnvironment = lib.mkOption {
        type = lib.types.str;
        default = "KATA_AUTH_TOKEN";
        description = "Runtime environment variable containing the bearer token.";
      };
    };

    server = {
      enable = lib.mkEnableOption "the foreground Kata user service";

      listen = lib.mkOption {
        type = lib.types.str;
        description = "Exact private address and port on which Kata listens.";
      };

      publicOrigin = lib.mkOption {
        type = lib.types.str;
        description = "Exact browser origin accepted by Kata.";
      };

      allowedHosts = lib.mkOption {
        type = lib.types.listOf lib.types.str;
        description = "Exact HTTP Host authorities accepted by Kata.";
      };

      environmentFile = lib.mkOption {
        type = lib.types.str;
        description = ''
          Runtime file containing KATA_AUTH_TOKEN, provisioned outside Nix
          and owner-only. On Linux it is the systemd EnvironmentFile and may
          use specifiers such as %h; on macOS it must be an absolute path,
          which the launchd launcher requires to be a mode-0600 regular file.
        '';
      };
    };

    backup = {
      enable = lib.mkEnableOption "scheduled local online JSONL exports";

      directory = lib.mkOption {
        type = lib.types.str;
        default = "${config.home.homeDirectory}/.local/state/kata/backups";
        description = "Owner-only local directory for timestamped JSONL exports.";
      };

      onCalendar = lib.mkOption {
        type = lib.types.str;
        default = "daily";
        description = "systemd OnCalendar expression for the backup timer.";
      };

      randomizedDelaySec = lib.mkOption {
        type = lib.types.str;
        default = "15m";
        description = "Maximum randomized delay applied to each scheduled backup.";
      };

      calendarInterval = lib.mkOption {
        type = lib.types.listOf (lib.types.attrsOf lib.types.int);
        default = [
          {
            Hour = 0;
            Minute = 0;
          }
        ];
        description = "launchd StartCalendarInterval entries for the macOS backup job.";
      };

      successCommand = lib.mkOption {
        type = lib.types.nullOr lib.types.lines;
        default = null;
        description = ''
          Shell commands run after each successful export and off-host copy,
          such as a dead-man's-switch heartbeat.
        '';
      };

      offHost = {
        enable = lib.mkEnableOption "an atomic checksummed SSH copy of each export";

        host = lib.mkOption {
          type = lib.types.str;
          description = "SSH host receiving a durable copy of each export.";
        };

        directory = lib.mkOption {
          type = lib.types.str;
          description = "Absolute owner-only destination directory on the SSH host.";
        };

        identityFile = lib.mkOption {
          type = lib.types.str;
          description = ''
            Absolute runtime path to the SSH identity used in batch mode.
            The identity remains outside Git and the Nix store.
          '';
        };
      };
    };
  };

  config = lib.mkIf cfg.enable {
    assertions = [
      {
        assertion = cfg.client.enable || cfg.server.enable;
        message = "services.kata must enable the client, the server, or both";
      }
      {
        assertion = !cfg.backup.enable || cfg.server.enable;
        message = "services.kata.backup requires services.kata.server";
      }
      {
        assertion = !cfg.backup.enable || cfg.backup.directory != cfg.homeDirectory;
        message = "Kata backups must not be stored inside the live KATA_HOME";
      }
      {
        assertion = !cfg.backup.offHost.enable || cfg.backup.enable;
        message = "services.kata.backup.offHost requires services.kata.backup";
      }
      {
        assertion =
          !cfg.backup.offHost.enable || builtins.match "[A-Za-z0-9._-]+" cfg.backup.offHost.host != null;
        message = "Kata off-host SSH host contains unsupported characters";
      }
      {
        assertion =
          !cfg.backup.offHost.enable
          || builtins.match "/[A-Za-z0-9._/-]+" cfg.backup.offHost.directory != null;
        message = "Kata off-host backup directory must be a simple absolute path";
      }
      {
        assertion =
          !cfg.backup.offHost.enable
          || builtins.match "/[A-Za-z0-9._/-]+" cfg.backup.offHost.identityFile != null;
        message = "Kata off-host SSH identity must be a simple absolute path";
      }
      {
        assertion = !(isDarwin && cfg.server.enable) || lib.hasPrefix "/" cfg.server.environmentFile;
        message = "On macOS, services.kata.server.environmentFile must be an absolute path";
      }
    ];

    # Home Manager's normal home.file entries are world-readable Nix-store
    # symlinks. The TOML is non-secret, but Kata's acceptance contract requires
    # an owner-only regular file, so install it during activation instead.
    # On macOS, install it before launchd loads the daemon so the first start
    # reads the current listener and browser origin.
    home.activation.kataConfiguration =
      (
        if isDarwin then
          lib.hm.dag.entryBetween [ "setupLaunchAgents" ] [ "writeBoundary" ]
        else
          lib.hm.dag.entryAfter [ "writeBoundary" ]
      )
        ''
          $DRY_RUN_CMD ${pkgs.coreutils}/bin/install -d -m 0700 \
            ${lib.escapeShellArg cfg.homeDirectory}
          $DRY_RUN_CMD ${pkgs.coreutils}/bin/install -m 0600 \
            ${configFile} ${lib.escapeShellArg "${cfg.homeDirectory}/config.toml"}

          for state_file in \
            ${lib.escapeShellArg "${cfg.homeDirectory}/kata.db"} \
            ${lib.escapeShellArg "${cfg.homeDirectory}/kata.db-wal"} \
            ${lib.escapeShellArg "${cfg.homeDirectory}/kata.db-shm"}; do
            if [[ -e "$state_file" ]]; then
              $DRY_RUN_CMD ${pkgs.coreutils}/bin/chmod 0600 "$state_file"
            fi
          done
        '';

    systemd.user.services = lib.mkIf (isLinux && cfg.server.enable) {
      kata = {
        Unit = {
          Description = "Kata shared work-ledger daemon";
          After = [ "network-online.target" ];
        };
        Service = {
          Type = "simple";
          Environment = [
            "HOME=%h"
            "KATA_HOME=${cfg.homeDirectory}"
            "KATA_TELEMETRY_ENABLED=0"
            "KATA_TRUST_PRIVATE_NETWORK=1"
          ];
          EnvironmentFile = cfg.server.environmentFile;
          WorkingDirectory = config.home.homeDirectory;
          ExecStart = "${cfg.package}/bin/kata daemon start --foreground --listen ${cfg.server.listen}";
          Restart = "on-failure";
          RestartSec = "5s";
          TimeoutStopSec = "30s";
          UMask = "0077";
          NoNewPrivileges = true;
          PrivateTmp = true;
        };
        Install.WantedBy = [ "default.target" ];
      };

      kata-backup = lib.mkIf cfg.backup.enable {
        Unit = {
          Description = "Export the live Kata ledger to owner-only JSONL";
          Wants = [ "kata.service" ];
          After = [ "kata.service" ];
        };
        Service = {
          Type = "oneshot";
          Environment = [
            "HOME=%h"
            "KATA_TELEMETRY_ENABLED=0"
          ];
          WorkingDirectory = config.home.homeDirectory;
          ExecStart = "${backupScript}/bin/kata-backup";
          UMask = "0077";
          NoNewPrivileges = true;
          PrivateTmp = true;
        };
      };
    };

    systemd.user.timers.kata-backup = lib.mkIf (isLinux && cfg.backup.enable) {
      Unit.Description = "Schedule owner-only Kata JSONL exports";
      Timer = {
        OnCalendar = cfg.backup.onCalendar;
        Persistent = true;
        RandomizedDelaySec = cfg.backup.randomizedDelaySec;
        Unit = "kata-backup.service";
      };
      Install.WantedBy = [ "timers.target" ];
    };

    # macOS has no linger: these agents run in the logged-in user's GUI
    # domain, so an unattended server needs that session to stay logged in.
    # KeepAlive restarts the daemon after any exit; stop it deliberately with
    # launchctl bootout rather than kata daemon stop.
    launchd.agents = lib.mkIf (isDarwin && cfg.server.enable) {
      kata = {
        enable = true;
        config = {
          ProgramArguments = [ "${serverLauncher}/bin/kata-server" ];
          EnvironmentVariables = {
            HOME = config.home.homeDirectory;
            KATA_HOME = cfg.homeDirectory;
            KATA_TELEMETRY_ENABLED = "0";
            KATA_TRUST_PRIVATE_NETWORK = "1";
          };
          WorkingDirectory = config.home.homeDirectory;
          RunAtLoad = true;
          KeepAlive = true;
          ThrottleInterval = 10;
          Umask = 63; # 0077
          StandardOutPath = "${logDirectory}/kata.out.log";
          StandardErrorPath = "${logDirectory}/kata.err.log";
        };
      };

      kata-backup = lib.mkIf cfg.backup.enable {
        enable = true;
        config = {
          ProgramArguments = [ "${backupScript}/bin/kata-backup" ];
          EnvironmentVariables = {
            HOME = config.home.homeDirectory;
            KATA_TELEMETRY_ENABLED = "0";
          };
          WorkingDirectory = config.home.homeDirectory;
          StartCalendarInterval = cfg.backup.calendarInterval;
          ProcessType = "Background";
          Umask = 63; # 0077
          StandardOutPath = "${logDirectory}/kata-backup.out.log";
          StandardErrorPath = "${logDirectory}/kata-backup.err.log";
        };
      };
    };
  };
}

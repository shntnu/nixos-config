{
  config,
  lib,
  pkgs,
  ...
}:

let
  cfg = config.services.kata;
  tomlFormat = pkgs.formats.toml { };

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
          remote_staging="$off_host_directory/.$file_name.partial.$(date -u +%s).$$"
          remote_final="$off_host_directory/$file_name"

          if env -u KATA_AUTH_TOKEN -u SSH_AUTH_SOCK \
            ssh "''${ssh_options[@]}" "$off_host" "test -e '$remote_final'"; then
            echo "Off-host Kata backup already exists: $off_host:$remote_final"
            return
          fi

          prepare_command="umask 077; mkdir -p '$off_host_directory' && chmod 0700 '$off_host_directory' && test ! -e '$remote_staging' && test ! -e '$remote_final'"
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
    '';
  };
in
{
  options.services.kata = {
    enable = lib.mkEnableOption "a managed Kata work-ledger deployment";

    package = lib.mkOption {
      type = lib.types.package;
      default = pkgs.callPackage ../shared/kata.nix { };
      defaultText = lib.literalExpression "pkgs.callPackage ../shared/kata.nix { }";
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
          Runtime systemd EnvironmentFile containing KATA_AUTH_TOKEN.
          The file is provisioned outside Nix and must be owner-only.
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
    ];

    # Home Manager's normal home.file entries are world-readable Nix-store
    # symlinks. The TOML is non-secret, but Kata's acceptance contract requires
    # an owner-only regular file, so install it during activation instead.
    home.activation.kataConfiguration = lib.hm.dag.entryAfter [ "writeBoundary" ] ''
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

    systemd.user.services = lib.mkIf cfg.server.enable {
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
          Requires = [ "kata.service" ];
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

    systemd.user.timers.kata-backup = lib.mkIf cfg.backup.enable {
      Unit.Description = "Schedule owner-only Kata JSONL exports";
      Timer = {
        OnCalendar = cfg.backup.onCalendar;
        Persistent = true;
        RandomizedDelaySec = cfg.backup.randomizedDelaySec;
        Unit = "kata-backup.service";
      };
      Install.WantedBy = [ "timers.target" ];
    };
  };
}

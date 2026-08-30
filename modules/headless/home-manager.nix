# Home Manager profile for lab servers (oppy, spirit, karkinos) and other
# SSH-first Linux machines. Also re-exported as homeModules.shsingh-headless
# for neusis to consume. Imports the shared shell/git/tmux/ssh module plus
# nixpkgs settings, then layers server-only deltas.
{ config, pkgs, lib, user, ... }@args:

let
  marimoLspNixos = pkgs.writeShellApplication {
    name = "marimo-lsp-nixos";
    runtimeInputs = [ pkgs.coreutils pkgs.findutils ];
    text = ''
      extension_dir="$(${pkgs.findutils}/bin/find "$HOME/.vscode-server/extensions" \
        -mindepth 1 -maxdepth 1 -type d \
        -name 'marimo-team.vscode-marimo-*-linux-x64' -print \
        | ${pkgs.coreutils}/bin/sort -V | ${pkgs.coreutils}/bin/tail -n 1)"
      if [[ -z "$extension_dir" ]]; then
        echo "No remote marimo VS Code extension installation found" >&2
        exit 1
      fi

      lsp_source="$(${pkgs.findutils}/bin/find "$extension_dir/dist" \
        -mindepth 1 -maxdepth 1 -type d -name 'marimo_lsp-*' -print \
        | ${pkgs.coreutils}/bin/sort -V | ${pkgs.coreutils}/bin/tail -n 1)"
      if [[ -z "$lsp_source" ]]; then
        echo "No bundled marimo-lsp source found below $extension_dir/dist" >&2
        exit 1
      fi

      uv_bin="$extension_dir/bundled/libs/bin/uv"
      if [[ ! -x "$uv_bin" ]]; then
        echo "Bundled marimo uv executable not found: $uv_bin" >&2
        exit 1
      fi

      nix_runtime="''${NIX_LD_LIBRARY_PATH:-/run/current-system/sw/share/nix-ld/lib}"
      export LD_LIBRARY_PATH="$nix_runtime''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
      exec "$uv_bin" tool run --python 3.13 --from "$lsp_source" marimo-lsp "$@"
    '';
  };

  # `gio mount` exits 2 when the location is already mounted, which makes the
  # oneshot unit below report failed even though the mount is present and fine.
  # Anything else mounting sftp://spirit/ first (a Files bookmark, an earlier
  # activation) therefore left a spurious failed unit after every switch or
  # login. Tolerate only that one message; real errors still fail the unit,
  # unlike a blanket SuccessExitStatus=2.
  mountSpirit = pkgs.writeShellScript "mount-spirit" ''
    if out=$(${pkgs.glib.bin}/bin/gio mount sftp://spirit/ 2>&1); then
      exit 0
    fi

    case "$out" in
      *"already mounted"*)
        echo "sftp://spirit/ is already mounted"
        exit 0
        ;;
    esac

    echo "$out" >&2
    exit 1
  '';
in
{
  imports = [
    ./kata.nix
    ../shared/msgvault-remote.nix
    ../shared/nixpkgs.nix
    ../shared/home-manager.nix
  ];

  home = {
    username = lib.mkDefault user;
    homeDirectory = lib.mkDefault "/home/${user}";
    stateVersion = lib.mkDefault "24.11";
    sessionVariables = {
      # Local ChEMBL SQLite copy for the chembl-data Claude skill (avoids the
      # flaky public REST API). Points at the shared reference-data home per the
      # imaging-server-maintenance data-storage policy; the skill checks for the
      # dir and falls back to download if a given host has no copy yet.
      CHEMBL_DIR = "/work/datasets/chembl";
    };
    packages =
      (pkgs.callPackage ../shared/packages.nix { })
      ++ (pkgs.callPackage ./packages.nix { host = args.host or null; })
      ++ [ marimoLspNixos ];
  };

  # VS Code strips LD_LIBRARY_PATH from its remote extension host. Launch the
  # bundled marimo language server through a narrow wrapper that restores the
  # Nix runtime only for marimo-lsp and its notebook-kernel children.
  home.file.".vscode-server/data/Machine/settings.json" = {
    text = builtins.toJSON {
      "marimo.lsp.path" = [ "${marimoLspNixos}/bin/marimo-lsp-nixos" ];
    };
  };

  programs = {
    home-manager.enable = true;

    zsh = {
      autosuggestion.enable = true;
      syntaxHighlighting.enable = true;
      initContent = lib.mkAfter ''
        bindkey -e
        unsetopt auto_menu

        export EDITOR="nvim"
        export VISUAL="nvim"

        # `code file` from a plain ssh or tmux shell. The VS Code integrated
        # terminal puts the Remote-SSH server's CLI on PATH and exports
        # VSCODE_IPC_HOOK_CLI; any other shell gets neither. Resolve both at
        # call time, not at shell startup, since a long-lived tmux shell
        # outlives any one window. An attached window beats the locally
        # installed app, and a closed window can leave a stale socket behind -
        # probe each socket for a live listener if that ever bites.
        code() {
          local cli=(~/.vscode-server/cli/servers/*/server/bin/remote-cli/code(N.om))
          # An exported hook wins, else the newest socket.
          local sock=($VSCODE_IPC_HOOK_CLI /run/user/$UID/vscode-ipc-*.sock(N=om))
          if (( $#cli && $#sock )); then
            VSCODE_IPC_HOOK_CLI="$sock[1]" "$cli[1]" "$@"
          else
            command code "$@"
          fi
        }
      '';
    };

    fzf = {
      enable = true;
      enableZshIntegration = true;
      defaultOptions = [ "--style full" ];
      fileWidget.options = [ "--preview='bat --color=always {}'" ];
      historyWidget.command = "";
    };

    delta = {
      enable = true;
      enableGitIntegration = true;
      options = {
        features = "side-by-side line-numbers decorations";
        syntax-theme = "dracula";
        decorations = {
          commit-decoration-style = "bold yellow box ul";
          file-decoration-style = "none";
          file-style = "bold yellow ul";
          hunk-header-decoration-style = "cyan box ul";
        };
        plus-style = "syntax '#003800'";
        minus-style = "syntax '#3f0001'";
        line-numbers = {
          line-numbers-left-style = "cyan";
          line-numbers-right-style = "cyan";
          line-numbers-minus-style = "124";
          line-numbers-plus-style = "28";
        };
      };
    };

    gh = {
      enable = true;
      extensions = [ pkgs.gh-dash ];
    };

    yazi = {
      enable = true;
      enableZshIntegration = true;
      shellWrapperName = "yy"; # keep legacy default; new default becomes "y" at stateVersion 26.05
      settings = {
        mgr.show_hidden = true;
        preview = {
          max_width = 2000;
          max_height = 2000;
        };
      };
    };
  };

  services.ssh-agent.enable = true;

  # GNOME Files: only useful on karkinos (it has a display); inert on oppy/spirit.
  # Nautilus defaults show-image-thumbnails to 'local-only', which skips anything
  # on a remote mount, so browsing spirit over sftp:// showed no image previews.
  # thumbnail-limit is in MB and must be a uint64 to match the schema type.
  dconf.settings."org/gnome/nautilus/preferences" = {
    show-image-thumbnails = "always";
    thumbnail-limit = lib.hm.gvariant.mkUint64 200;
  };

  # Screenshots, same karkinos-only story. GNOME binds these to Print and
  # Shift+Print, which a NuPhy Air75 V2 does not have. See LEARNING_LOG.md.
  dconf.settings."org/gnome/shell/keybindings" = {
    show-screenshot-ui = [ "<Shift><Super>s" ];
    screenshot = [ "<Shift><Super>f" ];
  };

  # Keep spirit's /work mounted over gvfs sftp so the FUSE path under
  # $XDG_RUNTIME_DIR/gvfs exists at login for terminal tools (yazi, bat, ripgrep)
  # and not just when a Files bookmark is clicked. Bound to graphical-session
  # rather than a hostname check: oppy and spirit have no graphical session, so
  # the unit simply never starts there and needs no per-host guard.
  systemd.user.services.mount-spirit = {
    Unit = {
      Description = "Mount spirit over gvfs sftp";
      After = [ "graphical-session.target" ];
      PartOf = [ "graphical-session.target" ];
    };
    Service = {
      Type = "oneshot";
      RemainAfterExit = true;
      ExecStart = "${mountSpirit}";
      # No ExecStop. The user manager does not linger, so logout tears down
      # /run/user/$UID with gvfsd-fuse and the mount inside it; an explicit
      # unmount buys nothing at session end. What it did buy was a mid-session
      # unmount on every stop or restart, including the restart home-manager
      # performs on switch, which pulled the mount out from under whatever was
      # using it - and out from under a Files bookmark the unit never created.
      # Leaving it out makes restart a no-op over an existing mount, since
      # ExecStart is idempotent.
    };
    Install.WantedBy = [ "graphical-session.target" ];
  };

  # Marked broken Oct 20, 2022; keep disabled for standalone Linux targets too.
  # https://github.com/nix-community/home-manager/issues/3344
  manual.manpages.enable = false;
}

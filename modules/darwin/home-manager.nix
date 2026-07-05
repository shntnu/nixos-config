{ config, pkgs, lib, user, ... }:

let
  # GUI launcher: opens a new Emacs client frame (used by the dock entry).
  myEmacsLauncher = pkgs.writeScript "emacs-launcher.command" ''
    #!/bin/sh
    emacsclient -c -n &
  '';
in
{
  imports = [
   ./dock
  ];

  # It me
  users.users.${user} = {
    name = "${user}";
    home = "/Users/${user}";
    isHidden = false;
    shell = pkgs.zsh;
  };

  homebrew = {
    enable = true;
    casks = import ./casks.nix;
    # taps managed by nix-homebrew in flake.nix (mutableTaps = false)
    brews = [ "awscli" "agent-browser" ];
    onActivation.upgrade = true;
  };

  home-manager.useGlobalPkgs = true;
  home-manager.users.${user} = { config, pkgs, lib, ... }: {
    imports = [ ../shared/home-manager.nix ];

    home = {
      enableNixpkgsReleaseCheck = false;
      packages = import ../shared/packages.nix { inherit pkgs; } ++ [ pkgs.msgvault ];
      stateVersion = "23.11";
      file = {
        "emacs-launcher.command".source = myEmacsLauncher;

        # Emacs bootstraps org-mode then tangles ~/.config/emacs/config.org
        ".emacs.d/init.el".source = ./emacs/init.el;

        # ssh-terminfo auto-installs xterm-ghostty terminfo on remote hosts on
        # first SSH, so SSHing into caladan / oppy / spirit / etc. doesn't warn
        # about the missing terminal definition. ssh-env falls back to
        # xterm-256color if the install fails (e.g., remote lacks tic).
        "Library/Application Support/com.mitchellh.ghostty/config".text = ''
          shell-integration-features = cursor,sudo,title,ssh-env,ssh-terminfo
        '';
      };
    };

    # macOS-only shell additions (merged after the shared zsh init)
    programs.zsh.initContent = lib.mkAfter ''
      # Emacs is my editor
      export ALTERNATE_EDITOR=""
      export EDITOR="emacsclient -t"

      e() {
          emacsclient -t "$@"
      }

      alias emacs='emacs -nw'

      # OpenRouter key for pi-coding-agent. Sourced from macOS Keychain (auto-
      # unlocked at login) rather than 1Password - Mac mini has no Touch ID,
      # so `op` requires `op signin` per shell which breaks fresh sessions.
      # Seed once with: security add-generic-password -a "$USER" -s openrouter -w "$(op read 'op://Personal/OpenRouter/credential')"
      # Pi 0.73.0 ignores auth.json `!command` resolvers (LEARNING_LOG.md), so env var is the only working path.
      export OPENROUTER_API_KEY="$(security find-generic-password -ws openrouter 2>/dev/null)"

      # Obsidian CLI (v1.12+, installed via Homebrew cask)
      if [ -d "/Applications/Obsidian.app/Contents/MacOS" ]; then
        export PATH="$PATH:/Applications/Obsidian.app/Contents/MacOS"
      fi
    '';
  };

  # Fully declarative dock using the latest from Nix Store
  local.dock = {
    enable = true;
    username = user;
    entries = [
      { path = "/System/Applications/Messages.app/"; }
      { path = "/System/Applications/Notes.app/"; }
      { path = "/System/Applications/Photos.app/"; }
      { path = "/System/Applications/System Settings.app/"; }
      {
        path = toString myEmacsLauncher;
        section = "others";
      }
      {
        path = "/Users/${user}/Downloads/";
        section = "others";
        options = "--sort name --view grid --display stack";
      }
    ];
  };
}

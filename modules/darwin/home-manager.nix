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
    imports = [
      ../shared/home-manager.nix
      ../shared/msgvault-remote.nix
    ];

    home = {
      enableNixpkgsReleaseCheck = false;
      packages = import ../shared/packages.nix { inherit pkgs; };
      stateVersion = "23.11";
      file = {
        "emacs-launcher.command".source = myEmacsLauncher;

        # Same repo path on Macs as on the lab servers: make ~/work/GitHub mirror
        # ~/Documents/GitHub so `cd ~/work/GitHub/server/nixos-config` resolves
        # everywhere (servers already keep checkouts under ~/work/GitHub/server).
        # Out-of-store symlink: points at the live dir, not a nix-store copy.
        "work/GitHub".source =
          config.lib.file.mkOutOfStoreSymlink "${config.home.homeDirectory}/Documents/GitHub";

        ".emacs.d/init.el".source = ./emacs/init.el;

        # ssh-terminfo auto-installs xterm-ghostty terminfo on remote hosts on
        # first SSH, so SSHing into caladan / oppy / spirit / etc. doesn't warn
        # about the missing terminal definition. ssh-env falls back to
        # xterm-256color if the install fails (e.g., remote lacks tic).
        "Library/Application Support/com.mitchellh.ghostty/config".text = ''
          shell-integration-features = cursor,sudo,title,ssh-env,ssh-terminfo
        '';

        # agent-browser (Homebrew, see brews above) launches Chrome headless by
        # default, so agents drive a browser the user cannot see. The flag is
        # sticky to the per-session daemon: once it starts headless, a later
        # --headed is silently ignored until `agent-browser close`. Default it
        # to headed here; pass `--headed false` for anything that must be
        # headless. Config file, not AGENT_BROWSER_HEADED, because the env var
        # has no documented off-switch.
        ".agent-browser/config.json".text = builtins.toJSON { headed = true; };
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

      # User-managed tools installed outside Nix land here.
      export PATH="$HOME/.local/bin:$PATH"

      # agent-browser daemons never exit on their own (auto-shutdown is off by
      # default), so a stale one outlives its browser and silently ignores the
      # launch options of the next `open`. Let them expire instead.
      export AGENT_BROWSER_IDLE_TIMEOUT_MS=3600000

      # Without this every agent lands in the session literally named
      # "default", so two concurrent Claude conversations drive one browser and
      # fight over the active tab. Give each conversation its own session, which
      # also makes `agent-browser close` safe: the caller provably owns it.
      # Plain human shells have no session id and keep "default".
      if [ -n "$CLAUDE_CODE_SESSION_ID" ]; then
        export AGENT_BROWSER_SESSION="cc-''${CLAUDE_CODE_SESSION_ID%%-*}"
      fi

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

{ config, pkgs, ... }:

let user = "shsingh"; in

{
  imports = [
    ../../modules/darwin/home-manager.nix
    ../../modules/shared/nixpkgs.nix
  ];

  nix = {
    package = pkgs.nix;

    settings = {
      trusted-users = [ "@admin" "${user}" ];
      substituters = [ "https://nix-community.cachix.org" "https://cache.nixos.org" ];
      trusted-public-keys = [
        "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="
        "nix-community.cachix.org-1:mB9FSh9qf2dCimDSUo8Zy7bkq5CX+/rkCWyvRCYg3Fs="
      ];
    };

    gc = {
      automatic = true;
      interval = { Weekday = 0; Hour = 2; Minute = 0; };
      options = "--delete-older-than 30d";
    };

    extraOptions = ''
      experimental-features = nix-command flakes
    '';
  };

  services.tailscale.enable = true;

  environment.systemPackages = with pkgs; [
    emacs30  # Pinned to Emacs 30.x stable (Darwin only - NixOS config TBD)
  ] ++ (import ../../modules/shared/packages.nix { inherit pkgs; });

  launchd.user.agents.emacs.path = [ config.environment.systemPath ];
  launchd.user.agents.emacs.serviceConfig = {
    KeepAlive = true;
    ProgramArguments = [
      "/bin/sh"
      "-c"
      "/bin/wait4path ${pkgs.emacs30}/bin/emacs && exec ${pkgs.emacs30}/bin/emacs --fg-daemon"
    ];
    StandardErrorPath = "/tmp/emacs.err.log";
    StandardOutPath = "/tmp/emacs.out.log";
  };

  # Incremental Gmail sync every 15 minutes (syncs all configured accounts)
  # msgvault is managed via Nix flake input; update with: nix flake update msgvault
  launchd.user.agents.msgvault-sync.serviceConfig = {
    ProgramArguments = [
      "${pkgs.msgvault}/bin/msgvault"
      "sync"
    ];
    StartCalendarInterval = [
      { Minute = 0; }
      { Minute = 15; }
      { Minute = 30; }
      { Minute = 45; }
    ];
    StandardErrorPath = "/tmp/msgvault-sync.err.log";
    StandardOutPath = "/tmp/msgvault-sync.out.log";
  };

  # Hourly qmd re-index + embed (refreshes configured collections)
  # qmd installed outside Nix: npm install -g @tobilu/qmd
  # Launcher exec's node, so nix-profile must be on PATH
  launchd.user.agents.qmd-reindex.serviceConfig = {
    ProgramArguments = [
      "/bin/sh"
      "-c"
      "/Users/${user}/.npm-packages/bin/qmd update && /Users/${user}/.npm-packages/bin/qmd embed"
    ];
    EnvironmentVariables = {
      PATH = "/Users/${user}/.nix-profile/bin:/usr/bin:/bin";
      HOME = "/Users/${user}";
    };
    StartCalendarInterval = [
      { Minute = 20; }
    ];
    StandardErrorPath = "/tmp/qmd-reindex.err.log";
    StandardOutPath = "/tmp/qmd-reindex.out.log";
  };

  # Start the tmux server at login so it is always up. tmux-continuum's
  # @continuum-restore fires when config is sourced on a fresh server, so this
  # also restores the saved sessions. Without it, `tmux ls` shows nothing until
  # the first bare `tmux` starts the server.
  launchd.user.agents.tmux-server.serviceConfig = {
    ProgramArguments = [
      "/Users/${user}/.nix-profile/bin/tmux"
      "start-server"
    ];
    EnvironmentVariables = {
      PATH = "/Users/${user}/.nix-profile/bin:/usr/bin:/bin";
      HOME = "/Users/${user}";
    };
    RunAtLoad = true;
    StandardErrorPath = "/tmp/tmux-server.err.log";
    StandardOutPath = "/tmp/tmux-server.out.log";
  };

  system = {
    checks.verifyNixPath = false;
    primaryUser = user;
    stateVersion = 5;

    defaults = {
      NSGlobalDomain = {
        AppleShowAllExtensions = true;
        ApplePressAndHoldEnabled = false;

        KeyRepeat = 2; # Values: 120, 90, 60, 30, 12, 6, 2
        InitialKeyRepeat = 15; # Values: 120, 94, 68, 35, 25, 15

        "com.apple.mouse.tapBehavior" = 1;
        "com.apple.sound.beep.volume" = 0.0;
        "com.apple.sound.beep.feedback" = 0;
      };

      dock = {
        autohide = false;
        show-recents = false;
        launchanim = true;
        orientation = "bottom";
        tilesize = 48;
      };

      finder = {
        _FXShowPosixPathInTitle = false;
      };

      trackpad = {
        Clicking = true;
        TrackpadThreeFingerDrag = true;
      };
    };
  };
}

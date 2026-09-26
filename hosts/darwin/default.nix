{ pkgs, ... }:

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

  # Raise the inherited limit for GUI and SSH processes without wrapping
  # self-updating executables. Existing processes need a new login/startup.
  launchd.daemons.file-limits = {
    script = ''
      # Split launchctl's three whitespace-separated columns intentionally.
      # shellcheck disable=SC2046
      set -eu
      set -- $(/bin/launchctl limit maxfiles)
      if [ "$2" = unlimited ] || [ "$2" -ge 4096 ]; then
        exit 0
      fi
      kernel_max=$(/usr/sbin/sysctl -n kern.maxfiles)
      kernel_per_process=$(/usr/sbin/sysctl -n kern.maxfilesperproc)
      # launchctl may also change the kernel ceilings; preserve them.
      trap '/usr/sbin/sysctl -w kern.maxfiles="$kernel_max" kern.maxfilesperproc="$kernel_per_process"' EXIT
      /bin/launchctl limit maxfiles 4096 "$kernel_per_process"
      /bin/launchctl limit maxfiles
      set -- $(/bin/launchctl limit maxfiles)
      test "$2" -ge 4096
    '';
    serviceConfig = {
      RunAtLoad = true;
      StandardOutPath = "/var/log/org.nixos.file-limits.log";
      StandardErrorPath = "/var/log/org.nixos.file-limits.log";
    };
  };

  environment.systemPackages = with pkgs; [
    emacs # Current stable Emacs (Darwin only - NixOS config TBD)
  ] ++ (import ../../modules/shared/packages.nix { inherit pkgs; });

  launchd.user.agents.emacs.serviceConfig = {
    KeepAlive = true;
    ProgramArguments = [
      "${pkgs.emacs}/bin/emacs"
      "--quick"
      "--fg-daemon"
    ];
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
    StandardErrorPath = "/Users/${user}/Library/Logs/qmd-reindex.err.log";
    StandardOutPath = "/Users/${user}/Library/Logs/qmd-reindex.out.log";
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

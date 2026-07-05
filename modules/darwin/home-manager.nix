{ config, pkgs, lib, home-manager, ... }:

let
  user = "shsingh";
  # Define the content of your file as a derivation
  myEmacsLauncher = pkgs.writeScript "emacs-launcher.command" ''
    #!/bin/sh
    emacsclient -c -n &
  '';
  sharedFiles = import ../shared/files.nix { inherit config pkgs; };
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
    casks = pkgs.callPackage ./casks.nix {};
    # taps managed by nix-homebrew in flake.nix (mutableTaps = false)
    brews = [ "awscli" "agent-browser" ];
    onActivation.upgrade = true;
  };

  # Enable home-manager
  home-manager = {
    useGlobalPkgs = true;
    users.${user} = { pkgs, config, lib, ... }:{
      home = {
        enableNixpkgsReleaseCheck = false;
        packages = pkgs.callPackage ./packages.nix {};
        file = lib.mkMerge [
          sharedFiles
          { "emacs-launcher.command".source = myEmacsLauncher; }
          {
            # ssh-terminfo auto-installs xterm-ghostty terminfo on remote hosts
            # on first SSH, so SSHing into caladan / oppy / spirit / etc. doesn't
            # warn about the missing terminal definition. ssh-env falls back to
            # xterm-256color if the install fails (e.g., remote lacks tic).
            "Library/Application Support/com.mitchellh.ghostty/config".text = ''
              shell-integration-features = cursor,sudo,title,ssh-env,ssh-terminfo
            '';
          }
        ];
        stateVersion = "23.11";
      };
      programs = {} // import ../shared/home-manager.nix { inherit config pkgs lib; };

      # Marked broken Oct 20, 2022 check later to remove this
      # https://github.com/nix-community/home-manager/issues/3344
      manual.manpages.enable = false;
    };
  };

  # Fully declarative dock using the latest from Nix Store
  local.dock = {
    enable = true;
    username = user;
    entries = [
      # { path = "/Applications/Safari.app/"; }
      { path = "/System/Applications/Messages.app/"; }
      { path = "/System/Applications/Notes.app/"; }
      { path = "/System/Applications/Photos.app/"; }
      { path = "/System/Applications/System Settings.app/"; }
      {
        path = toString myEmacsLauncher;
        section = "others";
      }
      {
        path = "${config.users.users.${user}.home}/Downloads/";
        section = "others";
        options = "--sort name --view grid --display stack";
      }
    ];
  };

}

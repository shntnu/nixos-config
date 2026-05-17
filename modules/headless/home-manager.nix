{
  config,
  pkgs,
  lib,
  ...
}:

let
  user = "shsingh";
  sharedPrograms = import ../shared/home-manager.nix { inherit config pkgs lib; };
in
{
  imports = [
    ../shared
  ];

  home = {
    username = lib.mkDefault user;
    homeDirectory = lib.mkDefault "/home/${user}";
    stateVersion = lib.mkDefault "24.11";
    packages =
      (pkgs.callPackage ../shared/packages.nix { })
      ++ (pkgs.callPackage ./packages.nix { });
    file = lib.mkMerge [
      (import ../shared/files.nix { inherit pkgs config; })
    ];
  };

  programs = lib.recursiveUpdate sharedPrograms {
    home-manager.enable = true;

    zsh = {
      initContent = lib.mkAfter ''
        # Server defaults: keep interactive editing predictable over SSH.
        bindkey -e
        unsetopt auto_menu

        export EDITOR="nvim"
        export VISUAL="nvim"
      '';
    };

    git.settings.core.editor = "nvim";
  };

  services.ssh-agent.enable = true;

  # Marked broken Oct 20, 2022; keep disabled for standalone Linux targets too.
  # https://github.com/nix-community/home-manager/issues/3344
  manual.manpages.enable = false;
}

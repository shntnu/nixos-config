# Home Manager profile for lab servers (oppy, spirit, karkinos) and other
# SSH-first Linux machines. Also re-exported as homeModules.shsingh-headless
# for neusis to consume. Imports the shared shell/git/tmux/ssh module plus
# nixpkgs settings, then layers server-only deltas.
{ config, pkgs, lib, user, ... }:

{
  imports = [
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

      # VS Code Remote extensions run outside project direnv shells. Make the
      # NixOS runtime libraries visible to uv/manylinux binaries such as pyzmq,
      # while retaining any library path inherited from the login environment.
      LD_LIBRARY_PATH =
        "$NIX_LD_LIBRARY_PATH\${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}";
    };
    packages =
      (pkgs.callPackage ../shared/packages.nix { })
      ++ (pkgs.callPackage ./packages.nix { });
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
      '';
    };

    git.settings = {
      commit.gpgsign = true;
      gpg = {
        format = "ssh";
        ssh.allowedSignersFile = "~/.ssh/allowed_signers";
      };
      user.signingkey = "~/.ssh/id_ed25519.pub";
    };

    fzf = {
      enable = true;
      enableZshIntegration = true;
      defaultOptions = [ "--style full" ];
      fileWidgetOptions = [ "--preview='bat --color=always {}'" ];
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
      shellWrapperName = "yy";  # keep legacy default; new default becomes "y" at stateVersion 26.05
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

  # Marked broken Oct 20, 2022; keep disabled for standalone Linux targets too.
  # https://github.com/nix-community/home-manager/issues/3344
  manual.manpages.enable = false;
}

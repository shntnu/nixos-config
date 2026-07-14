# Home Manager profile for lab servers (oppy, spirit, karkinos) and other
# SSH-first Linux machines. Also re-exported as homeModules.shsingh-headless
# for neusis to consume. Imports the shared shell/git/tmux/ssh module plus
# nixpkgs settings, then layers server-only deltas.
{ config, pkgs, lib, user, ... }:

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
in
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
    };
    packages =
      (pkgs.callPackage ../shared/packages.nix { })
      ++ (pkgs.callPackage ./packages.nix { })
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

{
  description = "Starter Configuration for MacOS and NixOS";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    home-manager.url = "github:nix-community/home-manager";
    darwin = {
      url = "github:LnL7/nix-darwin/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    nix-homebrew = {
      url = "github:zhaofengli-wip/nix-homebrew";
    };
    homebrew-bundle = {
      url = "github:homebrew/homebrew-bundle";
      flake = false;
    };
    homebrew-core = {
      url = "github:homebrew/homebrew-core";
      flake = false;
    };
    homebrew-cask = {
      url = "github:homebrew/homebrew-cask";
      flake = false;
    };
    disko = {
      url = "github:nix-community/disko";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, darwin, nix-homebrew, homebrew-bundle, homebrew-core, homebrew-cask, home-manager, nixpkgs, disko } @inputs:
    let
      user = "shsingh";
      linuxSystems = [ "x86_64-linux" "aarch64-linux" ];
      darwinSystems = [ "aarch64-darwin" "x86_64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs (linuxSystems ++ darwinSystems) f;
      devShell = system: let pkgs = nixpkgs.legacyPackages.${system}; in {
        default = with pkgs; mkShell {
          nativeBuildInputs = with pkgs; [ bashInteractive git ];
          shellHook = with pkgs; ''
            export EDITOR=vim
          '';
        };
      };
      mkApp = scriptName: system: {
        type = "app";
        program = "${(nixpkgs.legacyPackages.${system}.writeScriptBin scriptName ''
          #!/usr/bin/env bash
          PATH=${nixpkgs.legacyPackages.${system}.git}/bin:$PATH
          echo "Running ${scriptName} for ${system}"
          exec ${self}/apps/${system}/${scriptName}
        '')}/bin/${scriptName}";
      };
      mkLinuxApps = system: {
        "apply" = mkApp "apply" system;
        "build-switch" = mkApp "build-switch" system;
        "copy-keys" = mkApp "copy-keys" system;
        "create-keys" = mkApp "create-keys" system;
        "check-keys" = mkApp "check-keys" system;
        "install" = mkApp "install" system;
      };
      mkDarwinApps = system: {
        "apply" = mkApp "apply" system;
        "build" = mkApp "build" system;
        "build-switch" = mkApp "build-switch" system;
        "copy-keys" = mkApp "copy-keys" system;
        "create-keys" = mkApp "create-keys" system;
        "check-keys" = mkApp "check-keys" system;
        "rollback" = mkApp "rollback" system;
      };
    in
    {
      devShells = forAllSystems devShell;
      apps = nixpkgs.lib.genAttrs linuxSystems mkLinuxApps // nixpkgs.lib.genAttrs darwinSystems mkDarwinApps;

      darwinConfigurations = nixpkgs.lib.genAttrs darwinSystems (system: let
        user = "shsingh";
        overlays = import ./modules/shared/overlays.nix { pkgs = nixpkgs.legacyPackages.${system}; };
      in
        darwin.lib.darwinSystem {
          inherit system;
          specialArgs = inputs;
          modules = [
            home-manager.darwinModules.home-manager
            nix-homebrew.darwinModules.nix-homebrew
            {
              nixpkgs.overlays = overlays;
              nix-homebrew = {
                inherit user;
                enable = true;
                taps = {
                  "homebrew/homebrew-core" = homebrew-core;
                  "homebrew/homebrew-cask" = homebrew-cask;
                  "homebrew/homebrew-bundle" = homebrew-bundle;
                };
                mutableTaps = false;
                autoMigrate = true;
              };
            }
            ./hosts/darwin
          ];
        }
      );

      nixosConfigurations = nixpkgs.lib.genAttrs linuxSystems (system: nixpkgs.lib.nixosSystem {
        inherit system;
        specialArgs = inputs;
        modules = [
          disko.nixosModules.disko
          home-manager.nixosModules.home-manager {
            home-manager = {
              useGlobalPkgs = true;
              useUserPackages = true;
              users.${user} = import ./modules/nixos/home-manager.nix;
            };
          }
          ./hosts/nixos
        ];
     });

    # Home Manager standalone configuration for non-NixOS Linux (Ubuntu, WSL, etc.)
    #
    # HOME MANAGER HAS TWO MODES:
    # 1. Integrated mode (NixOS/Darwin): Runs as part of system rebuild
    #    - Loaded as modules in darwinConfigurations and nixosConfigurations above
    #    - Managed via 'nix run .#build-switch' (nixos-rebuild/darwin-rebuild)
    # 2. Standalone mode (Ubuntu/WSL): Runs independently
    #    - Defined here in homeConfigurations
    #    - Managed via 'home-manager switch' command directly
    #
    # WHAT YOU GET vs WHAT YOU DON'T:
    # Included: CLI tools, development environments (from modules/shared/packages.nix)
    # Included: Shell configs (zsh, git, starship) and dotfiles
    # NOT included: GUI applications (install via apt: chrome, keepassxc, etc.)
    # NOT included: System services, desktop environment tools (polybar, rofi, etc.)
    #
    # HOW THIS WORKS ON UBUNTU (not NixOS):
    # - Home Manager runs in "standalone" mode, managing only user-level files
    # - Installs packages to ~/.nix-profile/ instead of system-wide
    # - Creates symlinks from your home directory to Nix store for configs
    # - Your Ubuntu system remains unchanged - only your user environment is managed
    # - You get the same declarative package/config management as NixOS, but only for your user
    #
    # SETUP ON UBUNTU/WSL:
    # Prerequisites: Nix with flakes (curl -L https://nixos.org/nix/install | sh)
    #
    # 1. Clone this repo and cd into it
    # 2. Run initial setup WITH BACKUP FLAG (important!):
    #    nix run 'home-manager/master' -- switch --flake '.#shsingh' -b backup
    #    (Note: 'shsingh' is the username - replace with yours)
    #
    # WHAT THE BACKUP DOES:
    # Home Manager will detect existing files that conflict and rename them:
    #   ~/.zshrc → ~/.zshrc.backup
    #   ~/.zshenv → ~/.zshenv.backup
    #   ~/.config/git/ignore → ~/.config/git/ignore.backup
    #   (any other managed files...)
    # Then creates symlinks to Nix-managed versions in /nix/store/
    #
    # AFTER SETUP:
    # - All packages from modules/shared/packages.nix available in PATH
    # - Shell/program configs from modules/shared/home-manager.nix active
    # - Same declarative management as NixOS, but user-level only
    #
    # DAILY USAGE:
    # - Update config: nix run 'home-manager/master' -- switch --flake '.#shsingh'
    #   (Replace 'shsingh' with your username)
    # - Faster builds: add --max-jobs auto --cores 0
    # - Changes require: git add . (flake only sees tracked files)
    #
    # ROLLBACK IF NEEDED:
    # - home-manager generations  # list previous versions
    # - home-manager rollback     # revert to previous
    homeConfigurations = {
      "${user}" = home-manager.lib.homeManagerConfiguration {
        pkgs = nixpkgs.legacyPackages.x86_64-linux;
        modules = [
          ./modules/shared
          ({ pkgs, config, lib, ... }: {
            home = {
              username = user;
              homeDirectory = "/home/${user}";
              stateVersion = "24.11";  # Use latest stable
              packages = pkgs.callPackage ./modules/shared/packages.nix {};
              file = lib.mkMerge [
                (import ./modules/shared/files.nix { inherit pkgs config; })
              ];
            };

            programs = (import ./modules/shared/home-manager.nix { inherit config pkgs lib; }) // {
              home-manager.enable = true;
            };

            # Nix configuration
            nix = {
              package = pkgs.nix;
              settings = {
                experimental-features = [ "nix-command" "flakes" ];
                warn-dirty = false;
              };
            };
          })
        ];
        extraSpecialArgs = { inherit inputs; };
      };
    };

    # Templates for creating new projects
    templates = {
      basic = {
        path = ./templates/basic;
        description = "Basic development environment";
      };
      python = {
        path = ./templates/python;
        description = "Python development environment with uv";
      };
      node = {
        path = ./templates/node;
        description = "Node.js development environment";
      };
      rust = {
        path = ./templates/rust;
        description = "Rust development environment";
      };
      lean-mathlib = {
        path = ./templates/lean-mathlib;
        description = "Lean 4 development with Mathlib";
      };
    };

  };
}

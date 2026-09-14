{
  description = "Nix configuration for macOS (nix-darwin) and Linux (Home Manager)";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    home-manager = {
      url = "github:nix-community/home-manager";
      inputs.nixpkgs.follows = "nixpkgs";
    };
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
    msgvault = {
      url = "github:wesm/msgvault";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    deploy-rs = {
      url = "github:serokell/deploy-rs";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    private.url = "git+ssh://git@github.com/shntnu/nixos-config-private";
  };

  outputs = { self, darwin, nix-homebrew, homebrew-bundle, homebrew-core, homebrew-cask, home-manager, nixpkgs, msgvault, private, deploy-rs } @inputs:
    let
      user = "shsingh";
      linuxSystems = [ "x86_64-linux" "aarch64-linux" ];
      darwinSystems = [ "aarch64-darwin" "x86_64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs (linuxSystems ++ darwinSystems) f;
      # Use the cached nixpkgs executable with the upstream activation helpers.
      deployPkgs = forAllSystems (system: import nixpkgs {
        inherit system;
        overlays = [
          deploy-rs.overlays.default
          (_: prev: {
            deploy-rs = prev.deploy-rs // {
              inherit (nixpkgs.legacyPackages.${system}) deploy-rs;
            };
          })
        ];
      });
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
          exec ${self}/apps/${system}/${scriptName} "$@"
        '')}/bin/${scriptName}";
      };
      mkDarwinApps = system: {
        "build" = mkApp "build" system;
        "build-switch" = mkApp "build-switch" system;
        "rollback" = mkApp "rollback" system;
      };
      mkDarwinConfig = { hostModule, system ? "aarch64-darwin" }:
        darwin.lib.darwinSystem {
          inherit system;
          specialArgs = inputs // { inherit user; };
          modules = [
            home-manager.darwinModules.home-manager
            nix-homebrew.darwinModules.nix-homebrew
            {
              # Home Manager aborts the WHOLE file-linking phase on the first
              # pre-existing file it would clobber, so one stray hand-edited
              # dotfile silently discards every home.file change while the
              # build still reports success. Rename the offender instead.
              home-manager.backupFileExtension = "hm-bak";
            }
            {
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
            hostModule
          ];
        };
      mkHeadlessHomeConfiguration = host: system: home-manager.lib.homeManagerConfiguration {
        pkgs = nixpkgs.legacyPackages.${system};
        modules =
          [
            ./modules/headless/home-manager.nix
            private.homeModules.default
            {
              home.homeDirectory = "/home/${user}";
            }
          ]
          ++ nixpkgs.lib.optional
            (builtins.hasAttr host private.homeModules)
            private.homeModules.${host};
        extraSpecialArgs = inputs // { inherit host user; };
      };
    in
    {
      devShells = forAllSystems devShell;
      apps = forAllSystems (system: {
        deploy = {
          type = "app";
          meta.description = "Deploy selected Darwin or standalone Home Manager profiles over SSH";
          program = "${deployPkgs.${system}.deploy-rs.deploy-rs}/bin/deploy";
        };
        deploy-linux = {
          type = "app";
          meta.description = "Build and deploy Linux profiles from an SSH builder without a checkout";
          program = "${nixpkgs.legacyPackages.${system}.writeShellApplication {
            name = "deploy-linux";
            runtimeInputs = with nixpkgs.legacyPackages.${system}; [ nix openssh ];
            text = ''
              export DEPLOY_FLAKE=${self}
              ${builtins.readFile ./apps/deploy-linux}
            '';
          }}/bin/deploy-linux";
        };
      } // nixpkgs.lib.optionalAttrs (system == "aarch64-darwin") (mkDarwinApps system));

      deploy = {
        sshUser = user;
        autoRollback = true;
        magicRollback = true;
        confirmTimeout = 60;
        activationTimeout = 1800;
        sshOpts = [
          "-o" "ConnectTimeout=10"
          "-o" "ServerAliveInterval=15"
          "-o" "ServerAliveCountMax=3"
        ];
        nodes = nixpkgs.lib.mapAttrs (host: configuration: {
          hostname = if host == "laptop" then "wm89a-c9c" else host;
          profiles.system = {
            user = "root";
            interactiveSudo = true;
            path = deployPkgs.${configuration.pkgs.stdenv.hostPlatform.system}.deploy-rs.lib.activate.darwin configuration;
          };
        }) self.darwinConfigurations // builtins.listToAttrs (
          nixpkgs.lib.mapAttrsToList (name: configuration: {
            name = nixpkgs.lib.removePrefix "${user}@" name;
            value = {
              hostname = nixpkgs.lib.removePrefix "${user}@" name;
              # Keep deploy-rs history separate from Home Manager's own profile.
              profiles.home = {
                inherit user;
                path = deployPkgs.${configuration.pkgs.stdenv.hostPlatform.system}.deploy-rs.lib.activate.home-manager configuration;
              };
            };
          }) self.homeConfigurations
        );
      };

      # Check each platform's activators on that platform, without forcing Mac
      # builds into Linux-only deployments or Linux builds into Mac-only checks.
      checks = nixpkgs.lib.genAttrs [ "aarch64-darwin" "x86_64-linux" ] (system:
        deployPkgs.${system}.deploy-rs.lib.deployChecks (self.deploy // {
          nodes = nixpkgs.lib.filterAttrs (_: node:
            nixpkgs.lib.all (profile: profile.path.system == system)
              (builtins.attrValues node.profiles)
          ) self.deploy.nodes;
        }) // {
          deploy-linux-arguments = nixpkgs.legacyPackages.${system}.runCommand "deploy-linux-arguments" {} ''
            cd ${self}
            bash tests/deploy-linux.sh
            touch "$out"
          '';
        }
      );

      darwinConfigurations = {
        caladan = mkDarwinConfig { hostModule = ./hosts/darwin/caladan.nix; };
        laptop = mkDarwinConfig { hostModule = ./hosts/darwin/laptop.nix; };
      };

      homeModules = {
        shsingh-headless = ./modules/headless/home-manager.nix;
      };

    # Lab-server Home Manager profiles (standalone mode: `home-manager switch`,
    # run on the server itself). System config for oppy/spirit/karkinos lives in
    # shntnu/neusis. See README.md for workflows.
    homeConfigurations = nixpkgs.lib.genAttrs
      (builtins.map (host: "${user}@${host}") [ "oppy" "spirit" "karkinos" ])
      (name:
        mkHeadlessHomeConfiguration
          (nixpkgs.lib.removePrefix "${user}@" name)
          "x86_64-linux");

  };
}

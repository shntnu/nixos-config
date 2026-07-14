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
    private.url = "git+ssh://git@github.com/shntnu/nixos-config-private";
  };

  outputs = { self, darwin, nix-homebrew, homebrew-bundle, homebrew-core, homebrew-cask, home-manager, nixpkgs, msgvault, private } @inputs:
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
      mkHeadlessHomeConfiguration = system: home-manager.lib.homeManagerConfiguration {
        pkgs = nixpkgs.legacyPackages.${system};
        modules = [
          ./modules/headless/home-manager.nix
          {
            home.homeDirectory = "/home/${user}";
          }
        ];
        extraSpecialArgs = inputs // { inherit user; };
      };
    in
    {
      devShells = forAllSystems devShell;
      apps = nixpkgs.lib.genAttrs [ "aarch64-darwin" ] mkDarwinApps;

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
      (_: mkHeadlessHomeConfiguration "x86_64-linux");

  };
}

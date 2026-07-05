# Shared nixpkgs settings: unfree allowance + overlays.
#
# Imported at two different levels, which both expose the same `nixpkgs.*`
# options:
#   - darwin system level: hosts/darwin/default.nix
#   - Home Manager standalone level: modules/headless/home-manager.nix
#     (standalone HM re-imports nixpkgs with these settings applied)
#
# `msgvault` arrives via specialArgs/extraSpecialArgs in flake.nix.
{ msgvault, ... }:

{
  nixpkgs = {
    config.allowUnfree = true;
    overlays = import ./overlays.nix { inherit msgvault; };
  };
}

# All overlays, applied on every machine via modules/shared/nixpkgs.nix.
{ msgvault }:

[
  # msgvault flake input -> pkgs.msgvault (installed on macOS only, run by the
  # msgvault-sync launchd agent). Update: nix flake update msgvault
  (final: prev: {
    msgvault = msgvault.packages.${prev.stdenv.hostPlatform.system}.default;
  })

  # No nextflow overlay: nixpkgs now ships >= the 25.08 we once pinned it
  # ahead to (retired 2026-07-05). If nixpkgs ever falls too far behind what a
  # pipeline needs, add a fetchurl override back here.
]

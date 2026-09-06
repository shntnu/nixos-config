# All overlays, applied on every machine via modules/shared/nixpkgs.nix.
{ msgvault }:

[
  # One pinned source build for the installed CLI, services, and remote client.
  (final: prev: {
    msgvault = prev.callPackage ./msgvault-package.nix { msgvaultSrc = msgvault; };
  })

  # No nextflow overlay: nixpkgs now ships >= the 25.08 we once pinned it
  # ahead to (retired 2026-07-05). If nixpkgs ever falls too far behind what a
  # pipeline needs, add a fetchurl override back here.
]

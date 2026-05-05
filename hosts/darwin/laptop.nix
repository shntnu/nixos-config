{ private, ... }:

{
  imports = [
    ./default.nix
    private.darwinModules.laptop
  ];
}

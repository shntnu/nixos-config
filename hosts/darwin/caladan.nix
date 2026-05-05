{ private, ... }:

{
  imports = [
    ./default.nix
    private.darwinModules.caladan
  ];

  homebrew.casks = [
    "google-drive"
    "dropbox"
    "slack"
    "zoom"
  ];
}

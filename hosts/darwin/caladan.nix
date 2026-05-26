{ private, ... }:

{
  imports = [
    ./default.nix
    private.darwinModules.caladan
  ];

  power.sleep.computer = 0;
  power.sleep.display = 15;
  power.restoreOnPowerFailure = true;

  homebrew.casks = [
    "google-drive"
    "dropbox"
    "slack"
    "zoom"
  ];
}

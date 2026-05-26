{ private, ... }:

{
  imports = [
    ./default.nix
    private.darwinModules.caladan
  ];

  power.sleep.computer = "never";
  power.sleep.display = 15;
  power.restartAfterPowerFailure = true;
  power.restartAfterFreeze = true;

  homebrew.casks = [
    "google-drive"
    "dropbox"
    "slack"
    "zoom"
  ];
}

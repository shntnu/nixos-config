{ private, ... }:

{
  imports = [
    ./default.nix
    private.darwinModules.caladan
    ../../modules/darwin/health-guardrails.nix
  ];

  # Grozier is caladan's Time Machine destination; the bare hostname does not
  # resolve, so probe the mDNS name over SMB.
  services.healthGuardrails = {
    enable = true;
    timeMachine.host = "Grozier.local";
  };

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

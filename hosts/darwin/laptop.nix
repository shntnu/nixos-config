{ private, ... }:

let user = "shsingh"; in

{
  imports = [
    ./default.nix
    private.darwinModules.laptop
  ];

  # Weekly OneDrive SharePoint backup for OASIS consortium (work -> laptop only;
  # the OneDriveBackup.app wrapper exists only on this machine, and running the
  # agent on caladan just failed weekly with exit 78 / spawn error)
  # Uses OneDriveBackup.app wrapper (grant it Full Disk Access, not bash)
  # Calls the app's executable directly (not via 'open') to capture stdout/stderr
  launchd.user.agents.onedrive-archive.serviceConfig = {
    ProgramArguments = [
      "/Users/${user}/Applications/OneDriveBackup.app/Contents/MacOS/applet"
    ];
    StartCalendarInterval = [
      { Weekday = 0; Hour = 3; Minute = 0; }  # Sunday 3am (nix gc runs at 2am)
    ];
    StandardErrorPath = "/tmp/onedrive-archive.err.log";
    StandardOutPath = "/tmp/onedrive-archive.out.log";
  };
}

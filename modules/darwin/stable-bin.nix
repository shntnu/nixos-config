# macOS TCC (Full Disk Access, Automation, etc.) keys a command-line tool's
# identity off its resolved real path, not the path used to invoke it or its
# code signature content. A Nix store path changes on every rebuild, and a
# symlink such as ~/.nix-profile/bin/<name> still resolves through to that
# changing store path, so any grant tied to either one is silently lost the
# next time the referenced derivation changes.
#
# stableBin installs a real copy of a package's binary at a fixed path
# outside the Nix store, refreshed on every activation. Grant TCC access to
# that fixed path once; it survives rebuilds because the path itself never
# changes, only the file contents underneath it.
{ lib, ... }:

let
  stableBinDir = "/usr/local/libexec/nix-stable-bin";
in
{
  stableBinDir = stableBinDir;

  # name: stable file name under stableBinDir (also the TCC-visible identity)
  # package: derivation providing bin/${binName}
  # binName: executable name inside package/bin, defaults to name
  stableBin =
    { name, package, binName ? name }:
    let
      stablePath = "${stableBinDir}/${name}";
    in
    {
      inherit stablePath;
      activationScript = ''
        /bin/mkdir -p ${stableBinDir}
        /usr/sbin/chown root:wheel ${stableBinDir}
        /bin/chmod 0755 ${stableBinDir}
        /usr/bin/install -m 0755 ${package}/bin/${binName} ${stablePath}
      '';
    };
}

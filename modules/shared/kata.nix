{ fetchurl, lib, stdenvNoCC }:

let
  version = "0.14.3";
  sources = {
    aarch64-darwin = {
      hash = "sha256-auloMBtpbJBa1jHP8gtURWeBWidTLsLrJx2RzyTBKQY=";
      suffix = "darwin_arm64";
    };
    x86_64-linux = {
      hash = "sha256-1Wnu/3D7b6n2fbPFHEO7OnraqgzTECdKS9CkLKL/PsA=";
      suffix = "linux_amd64";
    };
  };
  source = sources.${stdenvNoCC.hostPlatform.system};
in
stdenvNoCC.mkDerivation {
  pname = "kata";
  inherit version;

  src = fetchurl {
    url = "https://github.com/kenn-io/kata/releases/download/v${version}/kata_${version}_${source.suffix}.tar.gz";
    inherit (source) hash;
  };

  dontUnpack = true;

  installPhase = ''
    runHook preInstall
    mkdir -p "$out/bin"
    tar -xzf "$src" kata
    install -m 0755 kata "$out/bin/kata"
    runHook postInstall
  '';

  meta = {
    description = "Local-first issue tracker for coding agents and their human supervisors";
    homepage = "https://www.katatracker.com/";
    license = lib.licenses.mit;
    mainProgram = "kata";
    platforms = builtins.attrNames sources;
  };
}

{ lib, stdenvNoCC, fetchurl, unzip }:

stdenvNoCC.mkDerivation {
  pname = "imsg";
  version = "0.15.6";

  src = fetchurl {
    url = "https://github.com/openclaw/imsg/releases/download/v0.15.6/imsg-macos.zip";
    sha256 = "a91bf50a568878b4aca68391dcd24368c687261bf6c0c252af82bd8b2eb796b1";
  };
  nativeBuildInputs = [ unzip ];
  sourceRoot = ".";
  # Preserve upstream signatures and the adjacent Swift resource bundles.
  dontFixup = true;
  installPhase = ''
    runHook preInstall
    mkdir -p "$out/libexec/imsg" "$out/bin"
    cp -R imsg *.bundle "$out/libexec/imsg/"
    if [ -f imsg-bridge-helper.dylib ]; then
      cp imsg-bridge-helper.dylib "$out/libexec/imsg/"
    fi
    ln -s "$out/libexec/imsg/imsg" "$out/bin/imsg"
    runHook postInstall
  '';
  meta = {
    description = "Send and read iMessage and SMS through Messages.app";
    homepage = "https://github.com/openclaw/imsg";
    license = lib.licenses.mit;
    platforms = lib.platforms.darwin;
    mainProgram = "imsg";
  };
}

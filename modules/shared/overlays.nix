# All overlays, applied on every machine via modules/shared/nixpkgs.nix.
{ msgvault }:

[
  # msgvault flake input -> pkgs.msgvault (listed in packages.nix, run by the
  # msgvault-sync launchd agent on macOS). Update: nix flake update msgvault
  (final: prev: {
    msgvault = msgvault.packages.${prev.stdenv.hostPlatform.system}.default;
  })

  # nixpkgs carries 24.08.0-edge; plugins need a newer Nextflow, so fetch the
  # release dist directly. Drop this when nixpkgs catches up.
  (final: prev: {
    nextflow = prev.stdenv.mkDerivation rec {
      pname = "nextflow";
      version = "25.08.0-edge";

      src = prev.fetchurl {
        url = "https://github.com/nextflow-io/nextflow/releases/download/v${version}/nextflow-${version}-dist";
        sha256 = "0gy67a19x1wcs55nd142szw7183wqk50hqp8bbnni2ymgxin7k0i";
      };

      nativeBuildInputs = [ prev.makeWrapper ];

      dontUnpack = true;
      dontBuild = true;

      installPhase = ''
        runHook preInstall

        mkdir -p $out/bin
        install -m755 $src $out/bin/nextflow

        # Wrap to ensure Java is available
        wrapProgram $out/bin/nextflow \
          --prefix PATH : ${prev.lib.makeBinPath [ prev.jdk17 prev.bash ]}

        runHook postInstall
      '';

      meta = with prev.lib; {
        description = "A DSL for data-driven computational pipelines";
        homepage = "https://www.nextflow.io/";
        license = licenses.asl20;
        platforms = platforms.unix;
      };
    };
  })
]

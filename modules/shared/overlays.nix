{ pkgs }:

[
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

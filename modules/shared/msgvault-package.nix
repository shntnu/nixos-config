{
  lib,
  stdenvNoCC,
  buildGoModule,
  go_1_27,
  bun,
  fetchurl,
  nodejs,
  cacert,
  sqlite,
  msgvaultSrc,
}:
let
  version = "0.19.3-unstable-2026-09-05";
  revision = msgvaultSrc.rev;
  system = stdenvNoCC.hostPlatform.system;

  # Keep toolchain changes local to this package.
  go = go_1_27.overrideAttrs (_: {
    version = "1.27.0";
    src = fetchurl {
      url = "https://go.dev/dl/go1.27.0.src.tar.gz";
      hash = "sha256-cAJAPXzERSnvbSb2mkSBgmM5Xq18FsBaWAiuBH6+sOU=";
    };
  });
  bunSources = {
    aarch64-darwin = {
      suffix = "darwin-aarch64";
      hash = "sha256-2LliIYKK1vl6x6wKt+lYcjQa92MAHogD6CZ2UsJlJiA=";
    };
    aarch64-linux = {
      suffix = "linux-aarch64";
      hash = "sha256-on/7Y6gxA3WDbg1vZorhf6jY0YuIw3yCHGUzGXOhmjs=";
    };
    x86_64-darwin = {
      suffix = "darwin-x64-baseline";
      hash = "sha256-PjWtb1OXGpg0v55nhuKt9ytfGSHMmpxf3gc9KXKUQHY=";
    };
    x86_64-linux = {
      suffix = "linux-x64";
      hash = "sha256-lR7iruhV8IWVruxiJSJqKY0/6oOj3NZGXAnLzN9+hI8=";
    };
  };
  bunPinned = bun.overrideAttrs (_: {
    version = "1.3.14";
    src = fetchurl {
      url = "https://github.com/oven-sh/bun/releases/download/bun-v1.3.14/bun-${bunSources.${system}.suffix}.zip";
      inherit (bunSources.${system}) hash;
    };
  });

  # Download the locked dependencies once, including optional packages for all
  # supported platforms. The application build below has no network access.
  webDependencies = stdenvNoCC.mkDerivation {
    pname = "msgvault-web-dependencies";
    inherit version;
    src = msgvaultSrc;
    nativeBuildInputs = [
      bunPinned
      cacert
    ];
    dontConfigure = true;
    dontFixup = true;
    buildPhase = ''
      runHook preBuild
      cd web
      bun install --frozen-lockfile --ignore-scripts --no-progress \
        --linker=hoisted --backend=copyfile --cache-dir "$TMPDIR/bun-cache" \
        --os '*' --cpu '*'
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      cp -R node_modules "$out"
      runHook postInstall
    '';
    outputHashMode = "recursive";
    outputHash = "sha256-d0wvfqXK+4mOro2Hj62u2mkTnJU8MHuU3v0mZZjUoWA=";
  };
in
(buildGoModule.override { inherit go; }) {
  pname = "msgvault";
  inherit version;
  src = msgvaultSrc;
  vendorHash = "sha256-G/55LAWHJIJ8bF+uSuy1CnWyzOJoZJ+89qoGQ1ia7t0=";
  proxyVendor = true;
  subPackages = [ "cmd/msgvault" ];
  nativeBuildInputs = [
    bunPinned
    nodejs
  ];
  buildInputs = [ sqlite ];
  env.CGO_ENABLED = 1;
  tags = [
    "fts5"
    "sqlite_vec"
  ];
  ldflags = [
    "-s"
    "-w"
    "-X go.kenn.io/msgvault/cmd/msgvault/cmd.Version=${version}"
    "-X go.kenn.io/msgvault/cmd/msgvault/cmd.Commit=${revision}"
  ];
  preBuild = ''
    cp -R ${webDependencies} web/node_modules
    chmod -R u+w web/node_modules
    patchShebangs web/node_modules
    pushd web
    bun run generate
    bun run build
    popd
    mkdir -p internal/web/dist
    cp -R web/dist/. internal/web/dist/
    node scripts/check-web-assets.mjs
  '';
  overrideModAttrs = _: {
    preBuild = "";
  };
  doCheck = false;
  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck
    "$out/bin/msgvault" version
    node scripts/check-web-assets.mjs --binary "$out/bin/msgvault"
    runHook postInstallCheck
  '';
  passthru = {
    inherit
      revision
      webDependencies
      go
      bunPinned
      ;
  };
  meta = {
    description = "Offline message archive with search and analytics";
    homepage = "https://github.com/kenn-io/msgvault";
    license = lib.licenses.mit;
    mainProgram = "msgvault";
    platforms = builtins.attrNames bunSources;
  };
}

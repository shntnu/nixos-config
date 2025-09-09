{
  description = "Lean 4 development environment with Mathlib";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            # Lean toolchain manager - automatically downloads the correct Lean version
            # based on the lean-toolchain file in your project
            elan

            # Essential tools for Lake package management
            git
            curl

            # Optional: useful development tools
            ripgrep
            fd
          ];

          shellHook = ''
            echo "Lean 4 development environment with Mathlib"
            echo ""
            echo "Elan will automatically download Lean based on your lean-toolchain file."
            echo ""
            echo "Available commands:"
            echo "  lake build       - Build your Lean project"
            echo "  lake exe <name>  - Run an executable"
            echo "  lake update      - Update dependencies (including Mathlib)"
            echo "  lake clean       - Remove build artifacts"
            echo ""
            echo "For VS Code: Install the 'Lean 4' extension for the best experience."

            # Verify elan is available
            if command -v elan &> /dev/null; then
              echo ""
              echo "Elan version: $(elan --version)"

              # If lean-toolchain exists, show which Lean version will be used
              if [ -f "lean-toolchain" ]; then
                echo "Project Lean version: $(cat lean-toolchain)"
              fi
            fi
          '';
        };
      });
}

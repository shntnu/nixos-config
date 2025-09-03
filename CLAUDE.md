# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Context

This is a Nix flake configuration for macOS (using nix-darwin) and NixOS, created from dustinlyons/nixos-config simplified starter template without secrets management. The configuration manages system packages, settings, and user environments declaratively.

## Primary User Configuration

- Username: `shsingh`
- Primary system: `aarch64-darwin` (Apple Silicon Mac)
- Template source: https://github.com/dustinlyons/nixos-config (simplified starter version)

## Essential Commands

### Building and Switching Configuration

```bash
# Build and switch to new configuration (most common command)
nix run .#build-switch

# Build only (without switching)
nix run .#build

# Apply user information (replaces %USER%, %EMAIL%, %NAME% tokens)
nix run .#apply

# Rollback to previous generation
nix run .#rollback
```

### Development Commands

```bash
# Update flake dependencies
nix flake update

# Check flake configuration
nix flake check

# Enter development shell
nix develop

# Try a package without installing
nix shell nixpkgs#<package-name>
```

## Architecture Overview

### Flake Structure

The `flake.nix` defines:
- **darwinConfigurations**: macOS configurations using nix-darwin
- **nixosConfigurations**: NixOS configurations (for Linux systems)
- **Apps**: Helper scripts for building, applying, and managing configurations
- **DevShells**: Development environments

### Module Organization

- **`hosts/`**: System-specific configurations
  - `darwin/default.nix`: macOS system configuration
  - `nixos/default.nix`: NixOS system configuration

- **`modules/`**: Reusable configuration modules
  - `shared/`: Cross-platform packages and configurations
    - `packages.nix`: Common packages for all systems
    - `home-manager.nix`: User shell and program configurations
  - `darwin/`: macOS-specific modules
    - `packages.nix`: macOS-only packages
    - `casks.nix`: Homebrew cask applications
    - `dock/`: Dock configuration module
  - `nixos/`: Linux-specific modules

- **`apps/`**: Platform-specific build and management scripts
  - Each platform directory contains: `apply`, `build`, `build-switch`, `rollback`

### Key Integration Points

1. **Home Manager**: Manages user-level configurations (dotfiles, shell, programs)
2. **nix-darwin**: Provides macOS system configuration capabilities
3. **nix-homebrew**: Declaratively manages Homebrew packages and casks
4. **disko**: Handles disk partitioning for NixOS installations

## Configuration Workflow

1. **Adding Packages**:
   - System packages: Edit `modules/shared/packages.nix` (cross-platform) or `modules/darwin/packages.nix` (macOS-specific)
   - Homebrew casks: Edit `modules/darwin/casks.nix`
   - User packages: Edit `modules/darwin/home-manager.nix`

2. **Modifying System Settings**:
   - macOS: Edit `hosts/darwin/default.nix` for system preferences
   - User settings: Edit `modules/shared/home-manager.nix` or `modules/darwin/home-manager.nix`

3. **After Changes**:
   - Always run `git add .` before building (only tracked files are copied to Nix store)
   - Run `nix run .#build-switch` to apply changes
   - If build fails, check for syntax errors or missing dependencies

## Important Files to Modify

- `modules/shared/packages.nix`: Add/remove common packages
- `modules/darwin/casks.nix`: Manage GUI applications via Homebrew
- `modules/shared/home-manager.nix`: Shell configuration (zsh, git, etc.)
- `hosts/darwin/default.nix`: System-level macOS settings

## Python Development

UV is installed for Python package management. UV can download Python versions as needed, allowing flexible development without Nix-Python conflicts. For reproducible builds requiring Nix integration, consider adding uv2nix when specifically needed.

## Troubleshooting

- If `build-switch` requires sudo password: This is normal for darwin-rebuild
- If encountering "experimental features" errors: Ensure Nix flakes are enabled
- For file permission issues: Scripts in `apps/` must be executable (`chmod +x`)

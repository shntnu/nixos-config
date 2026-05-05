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

# For Home Manager standalone (experimental - see flake.nix homeConfigurations)
nix run 'home-manager/master' -- switch --flake '.#shsingh' -b backup
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
- **homeConfigurations**: Home Manager standalone for non-NixOS Linux (Ubuntu, WSL, etc.)
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

### Updating Homebrew Tap Packages

`homebrew.onActivation.upgrade = true` is set in `modules/darwin/home-manager.nix`, so `build-switch` upgrades all Homebrew formulae and casks automatically. For tap-only source updates (without waiting for a full rebuild):

```bash
nix flake update <tap-input-name>   # e.g., nix flake update some-tap
nix run .#build-switch              # syncs tap sources and upgrades formulae/casks
```

Trade-off: rebuilds are slightly slower due to upgrade checks. To revert to manual upgrades, remove the `onActivation.upgrade` line.

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

## pi-coding-agent

Pi reads `OPENROUTER_API_KEY` from the env, exported in `modules/shared/home-manager.nix` zsh init from the `openrouter` macOS Keychain entry. 1Password (`op://Personal/OpenRouter/credential`) is the upstream copy, used only to seed/rotate the keychain - not in the runtime path. Re-seed with `security add-generic-password -U -a "$USER" -s openrouter -w "$(op read 'op://Personal/OpenRouter/credential')"`. Keychain is **per-machine** (not iCloud-synced) - run the seed on each Mac (macmini and laptop) independently.

If pi reports "No API key for provider: openrouter": check `security find-generic-password -ws openrouter` returns the key, and that the env var is set in a fresh shell (`echo "${#OPENROUTER_API_KEY}"` should be 73). Two paths that look right but don't work: `auth.json` `!command` resolvers are ignored by pi 0.73.0 despite docs claiming support, and a custom `openrouter` provider in `models.json` hangs silently per [pi-mono #3168](https://github.com/badlogic/pi-mono/issues/3168). If either bug closes, the curated-list-in-models.json approach would be more elegant. Full convergence story in `LEARNING_LOG.md`.

## Python Development

UV is installed for Python package management. UV can download Python versions as needed, allowing flexible development without Nix-Python conflicts. For reproducible builds requiring Nix integration, consider adding uv2nix when specifically needed.

## Troubleshooting

- If `build-switch` requires sudo password: This is normal for darwin-rebuild
- If encountering "experimental features" errors: Ensure Nix flakes are enabled
- For file permission issues: Scripts in `apps/` must be executable (`chmod +x`)
- Homebrew cask operations (`brew reinstall --cask`, `brew install --cask`) require sudo for `/Applications` — suggest user run via `!` prefix since Claude's sandbox can't provide a password
- Auto-updating apps (e.g., Obsidian) can outgrow their cask installer; `brew upgrade` won't help if no new cask version exists — use `brew reinstall --cask <app>`

## Learning Log

`LEARNING_LOG.md` tracks Nix/Homebrew/system learnings. Update it when encountering new gotchas or non-obvious behavior worth preserving for future reference.

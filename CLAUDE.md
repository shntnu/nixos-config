# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Context

This is a Nix flake configuration for macOS (using nix-darwin) and NixOS, created from dustinlyons/nixos-config simplified starter template without secrets management. The configuration manages system packages, settings, and user environments declaratively.

## Primary User Configuration

- Username: `shsingh`
- Primary system: `aarch64-darwin` (Apple Silicon Mac)
- Template source: https://github.com/dustinlyons/nixos-config (simplified starter version)

## Essential Commands

See [README.md](./README.md) for platform-specific build/switch workflows (macOS, lab servers, Ubuntu/WSL).

Key detail for Claude: `build` / `build-switch` dispatch on `scutil --get LocalHostName` (case statement in `apps/aarch64-darwin/build{,-switch}`) into a `darwinConfigurations.<host>` key in `flake.nix`. Renaming a Mac requires updating both.

On neusis-managed lab servers (oppy, karkinos, spirit), this flake only manages the Home Manager profile — do not attempt `nix run .#build-switch` or `nixos-rebuild` from this repo on those machines.

## Architecture Overview

### Flake Structure

The `flake.nix` defines:
- **darwinConfigurations**: per-host macOS configurations (`caladan`, `laptop`) — each loads `hosts/darwin/default.nix` (shared base) plus a host-specific file that imports a `darwinModules.<host>` from the `private` input
- **homeConfigurations**: Home Manager standalone. Includes plain `shsingh` (for Ubuntu/WSL) plus lab-server entries `shsingh@oppy`, `shsingh@spirit`, `shsingh@karkinos` built via `mkHeadlessHomeConfiguration` from `modules/headless/`
- **homeModules**: exposes `shsingh-headless` (= `modules/headless/home-manager.nix`) for downstream consumers
- **Apps**: helper scripts for building, applying, and managing configurations. Darwin platforms expose `apply`, `build`, `build-switch`, `rollback`.
- **DevShells**: development environments
- **Templates**: `basic`, `lean-mathlib`

Notable flake inputs:
- `private` (`git+ssh://git@github.com/shntnu/nixos-config-private`) — provides per-host darwinModules (caladan, laptop) and other private config. Required for darwin builds.
- `msgvault` (`github:wesm/msgvault`) — provides the `msgvault` package used by the `msgvault-sync` launchd agent in `hosts/darwin/default.nix`.

NixOS system-level configuration is not managed here - lab servers (oppy, karkinos, spirit) use `shntnu/neusis` for NixOS system config and only consume the `homeConfigurations` from this flake for user-level setup.

### Module Organization

- **`hosts/`**: System-specific configurations
  - `darwin/default.nix`: shared macOS base (nix settings, common launchd agents — emacs, onedrive-archive, msgvault-sync, qmd-reindex — and `system.defaults`)
  - `darwin/caladan.nix`, `darwin/laptop.nix`: per-host entry points; each imports `./default.nix` plus `private.darwinModules.<host>` and may layer host-specific casks (e.g., caladan adds google-drive, dropbox, slack, zoom)
- **`modules/`**: Reusable configuration modules
  - `shared/`: Cross-platform packages and configurations
    - `packages.nix`: Common packages for all systems
    - `home-manager.nix`: User shell and program configurations (zsh init, including the `OPENROUTER_API_KEY` keychain pull)
    - `overlays.nix`: shared nixpkgs overlays (e.g., pinned `nextflow`)
  - `darwin/`: macOS-specific modules
    - `packages.nix`: macOS-only packages
    - `casks.nix`: Homebrew cask applications
    - `dock/`: Dock configuration module
  - `headless/`: Home Manager profile for lab servers (oppy/spirit/karkinos). Imports `../shared`, adds headless-only packages from `headless/packages.nix`, and layers server-specific program configs (fzf, delta, gh, yazi, zsh autosuggestion/syntax-highlighting, git SSH signing). Also re-exported as `homeModules.shsingh-headless`. Git SSH signing uses `~/.ssh/id_ed25519` with `~/.ssh/allowed_signers`. On a new server, create the signers file once: `echo "shsingh@broadinstitute.org $(cat ~/.ssh/id_ed25519.pub)" > ~/.ssh/allowed_signers`.

- **`apps/`**: Platform-specific build and management scripts
  - `aarch64-darwin/`, `x86_64-darwin/`: `apply`, `build`, `build-switch`, `rollback`

- **`overlays/`** (top-level): legacy starter-template overlays (e.g., `10-feather-font.nix`); not referenced by `flake.nix`. The active overlays live in `modules/shared/overlays.nix`.

### Key Integration Points

1. **Home Manager**: Manages user-level configurations (dotfiles, shell, programs)
2. **nix-darwin**: Provides macOS system configuration capabilities
3. **nix-homebrew**: Declaratively manages Homebrew packages and casks

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
- `modules/darwin/casks.nix`: Manage GUI applications via Homebrew (applies to all darwin hosts)
- `modules/shared/home-manager.nix`: Shell configuration (zsh, git, etc.)
- `hosts/darwin/default.nix`: Shared macOS settings (nix config, launchd agents, `system.defaults`)
- `hosts/darwin/{caladan,laptop}.nix`: Per-host overrides (e.g., host-specific casks). For private/secret host config, edit the corresponding module in the `private` flake input repo.
- `modules/headless/`: Headless lab-server profile (`shsingh@oppy`, `shsingh@spirit`, `shsingh@karkinos`)

## pi-coding-agent

Pi reads `OPENROUTER_API_KEY` from the env, exported in `modules/shared/home-manager.nix` zsh init from the `openrouter` macOS Keychain entry. 1Password (`op://Personal/OpenRouter/credential`) is the upstream copy, used only to seed/rotate the keychain - not in the runtime path. Re-seed with `security add-generic-password -U -a "$USER" -s openrouter -w "$(op read 'op://Personal/OpenRouter/credential')"`. Keychain is **per-machine** (not iCloud-synced) - run the seed on each Mac (caladan and laptop) independently.

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

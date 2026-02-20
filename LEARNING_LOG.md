# Nix Learning Log

## 2025-01-21: System vs User Level Management

**Key Insight:** Ubuntu needs different commands than NixOS/macOS because it lacks system-level rebuild tools.

Three management approaches exist:

- NixOS: `nixos-rebuild` manages entire Linux system (kernel, services, packages)
- macOS: `darwin-rebuild` manages macOS system settings and packages
- Ubuntu: Home Manager standalone manages user environment only

Commands differ by platform:

```bash
# NixOS/macOS - system-level
nix run .#build-switch

# Ubuntu/WSL - user-level only
nix run 'home-manager/master' -- switch --flake '.#shsingh'
```

Ubuntu gets CLI tools and dotfiles but not GUI apps or system services. Those need `apt install`.

## 2025-01-21: Home Manager's Two Modes

**Key Insight:** Home Manager runs in integrated mode on NixOS/macOS (inside system rebuild) but standalone mode on Ubuntu.

Home Manager isn't just for Ubuntu - it's used everywhere, differently:

- NixOS/macOS: Loaded as a module in system configurations, runs during `nixos-rebuild`/`darwin-rebuild`
- Ubuntu: Runs standalone via `home-manager switch` since no system rebuild exists

Same Home Manager, different delivery mechanism. System rebuild carries it on NixOS/macOS; Ubuntu runs it directly.

## 2025-01-26: Nix Overlays for Package Version Updates

**Key Insight:** Overlays let you override package versions when nixpkgs is behind upstream releases.

Encountered Nextflow 24.08.0-edge in nixpkgs but needed 25.08.0-edge for plugin compatibility. Solution: create an overlay that fetches the latest version directly from GitHub releases. Overlays modify the package set before it's used, allowing version updates without waiting for nixpkgs.

```nix
# modules/shared/overlays.nix
nextflow = prev.stdenv.mkDerivation rec {
  version = "25.08.0-edge";
  src = prev.fetchurl { url = "...github release..."; };
  # Custom build instructions
};
```

Key learnings:
- Git-track overlay files before building (flakes only see tracked files)
- Use `nix-prefetch-url` to get SHA256 for new sources
- Set `dontUnpack = true` for self-contained scripts
- Override completely with `mkDerivation` when patches conflict

## 2025-11-25: Flake Input Follows and Hash Mismatches

**Key Insight:** Use `inputs.nixpkgs.follows = "nixpkgs"` for consistency, but hash mismatches in nixpkgs require different solutions.

Hit hash mismatch building `awscli2` because nixpkgs had a stale hash for `prompt-toolkit` dependency. Adding `home-manager.inputs.nixpkgs.follows = "nixpkgs"` is good practice (prevents multiple nixpkgs versions, reduces disk usage) but didn't fix this upstream package issue. Solution: moved `awscli` to Homebrew brews instead of nixpkgs.

```nix
# flake.nix - Best practice for consistency
home-manager = {
  url = "github:nix-community/home-manager";
  inputs.nixpkgs.follows = "nixpkgs";
};

# modules/darwin/home-manager.nix - Workaround for broken packages
brews = [ "awscli" ];  # Use Homebrew when nixpkgs broken
```

When nixpkgs has broken packages: overlays, downgrade nixpkgs, or use alternative package managers (Homebrew, pip via uv).

## 2025-11-25: Imperative vs Declarative Package Installation

**Key Insight:** Use `nix profile install` for fast-updating packages instead of adding flake inputs to avoid configuration complexity.

For packages that update frequently (like `claude-code` with hourly releases), imperative installation is simpler than declarative flake-based management. Adding a package as a flake input requires passing it through multiple configuration layers, while `nix profile install github:owner/repo` installs directly to your user profile. Update independently with `nix profile upgrade` without rebuilding your entire system configuration.

```bash
# Simple imperative install
nix profile install github:sadjow/claude-code-nix

# Update when needed (use profile name, not URL; --refresh bypasses cache)
nix profile upgrade claude-code-nix --refresh
```

Use declarative (flake-based) for system packages that change with your config; use imperative for tools you want to update independently.

## 2026-02-14: Why Nix Flake Wrappers Over npm/Homebrew for CLI Tools

**Key Insight:** Third-party nix flake wrappers (like `sadjow/claude-code-nix` and `sadjow/gemini-cli-nix`) solve problems that `npm install -g` and Homebrew cannot.

When adding `gemini-cli`, considered Homebrew (macOS-only, won't work on NixOS), npm global install, and nixpkgs (version 0.17.0 vs latest 0.28.2 — same lag problem as claude-code). The `sadjow` flake wrappers provide: Node.js version isolation (survives runtime switches), disabled auto-update (respects Nix store immutability), rollback via `nix profile rollback`, and hourly CI-driven version updates with hash verification. These aren't thin npm wrappers — they fundamentally repackage the tools for Nix compatibility.

```bash
# Both tools follow the same pattern
nix profile install github:sadjow/gemini-cli-nix
nix profile upgrade gemini-cli-nix --refresh
```

## 2026-02-19: nix-darwin's `brew bundle --no-upgrade` Default

**Key Insight:** `build-switch` won't upgrade already-installed Homebrew formulae because nix-darwin runs `brew bundle install --no-upgrade` by default.

Tried updating specstory from 1.0.0 to 1.7.0. Two separate systems are involved: nix-homebrew (zhaofengli) manages Homebrew itself and tap availability only ("does not manage any package installed by it"), while nix-darwin's `homebrew.*` module manages installed formulae via `brew bundle`. The `--no-upgrade` flag means missing formulae get installed but existing ones are never upgraded. Required a manual `brew upgrade specstoryai/tap/specstory`.

```bash
# Full update flow for custom tap brews (with default settings)
nix flake update specstoryai-tap
nix run .#build-switch
brew upgrade specstoryai/tap/specstory

# Or set in modules/darwin/home-manager.nix to auto-upgrade on rebuild:
# homebrew.onActivation.upgrade = true;
```

Key distinction: nix-homebrew = tap sources; nix-darwin `homebrew.*` = installed packages. The `onActivation.upgrade` default of `false` is intentional for idempotent rebuilds.

---

## Entry Guidelines

Keep entries brief. Structure each as:

- Date and descriptive title
- **Key Insight:** One sentence capturing the core learning
- 2-4 sentences of essential context
- Optional: Relevant command or code snippet
- Optional: Link to docs for deeper dive

Focus on "what" and "why", not detailed "how". Reader can consult docs for implementation details.

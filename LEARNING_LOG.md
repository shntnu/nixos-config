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

---

## Entry Guidelines

Keep entries brief. Structure each as:

- Date and descriptive title
- **Key Insight:** One sentence capturing the core learning
- 2-4 sentences of essential context
- Optional: Relevant command or code snippet
- Optional: Link to docs for deeper dive

Focus on "what" and "why", not detailed "how". Reader can consult docs for implementation details.

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

**Key Insight:** Third-party nix flake wrappers (like `sadjow/claude-code-nix`, `sadjow/gemini-cli-nix`, and `sadjow/codex-cli-nix`) solve problems that `npm install -g` and Homebrew cannot.

When adding `gemini-cli`, considered Homebrew (macOS-only, won't work on NixOS), npm global install, and nixpkgs (version 0.17.0 vs latest 0.28.2 — same lag problem as claude-code). The `sadjow` flake wrappers provide: disabled auto-update (respects Nix store immutability), rollback via `nix profile rollback`, and hourly CI-driven version updates with hash verification. For Node.js tools (claude-code, gemini-cli), they also provide Node.js version isolation. Codex CLI is a native Rust binary so the wrapper just fetches the prebuilt release — no Node.js needed.

```bash
# All three tools follow the same pattern
nix profile install github:sadjow/codex-cli-nix
nix profile upgrade codex-cli-nix --refresh
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

## 2026-03-21: Homebrew Cask Reinstall vs Upgrade for Auto-Updating Apps

**Key Insight:** Apps that auto-update internally (like Obsidian) can outgrow their Homebrew cask installer, requiring `brew reinstall --cask` rather than a version upgrade.

Obsidian's app bundle auto-updates its asar package (1.10.3 → 1.12.4) independently of Homebrew. The cask version stayed at 1.10.3, leaving the old installer wrapper in place — missing the new CLI (`obsidian.wrapper.sh`). `homebrew.onActivation.upgrade = true` only triggers upgrades when a new cask *version* exists; it doesn't detect that the installed app has self-updated past its cask. `brew reinstall --cask` replaces the entire app bundle and links the current CLI entry point.

```bash
# When cask version lags behind the app's self-update
brew reinstall --cask obsidian
# Not: brew upgrade --cask obsidian (no new cask version to upgrade to)
```

## 2026-05-04: Claude Subscription OAuth Blocked in Third-Party Coding Agents

**Key Insight:** Anthropic blocked Claude Pro/Max OAuth tokens from third-party tools in Jan-Feb 2026, so "use your Claude plan with pi/OpenCode/etc." is no longer the cheap path it appears to be.

Pi's docs still advertise Claude subscription auth, but pi clarifies it's billed per-token from the "extra usage" pool on `claude.ai/settings/usage`, not against your $20/$100 monthly plan limits — effectively API rates wearing a subscription's hat. ChatGPT Plus + Codex CLI does still draw from plan limits, but committing $20/mo for a second daily-driver agent duplicates Claude Code rather than complementing it. OpenRouter PAYG with a 1Password-backed key wins for "experiment with pi and other models" since it composes with the existing Claude Code subscription instead of replacing it. DeepSeek V3.2 / Qwen3-Coder via OpenRouter cost roughly 100x less than Opus for comparable code tasks, making throwaway pi sessions effectively free.

Refs: [WinBuzzer (2026-02-19)](https://winbuzzer.com/2026/02/19/anthropic-bans-claude-subscription-oauth-in-third-party-apps-xcxwbn/), [pi-mono providers docs](https://github.com/badlogic/pi-mono/blob/main/packages/coding-agent/docs/providers.md).

## 2026-05-04: Pi Custom Providers in models.json Are Broken

**Key Insight:** Defining a custom OpenAI-compatible provider in `~/.pi/agent/models.json` makes the model selectable but every request hangs silently — known unfixed bug as of v0.73.0.

I scaffolded a `models.json` with a custom `openrouter` provider so the OpenRouter API key could be resolved via `!op read` at runtime. Models appeared in `/model`, were selectable, and `pi --list-models` showed them — but every prompt produced no response, no error, zero token consumption. Bug filed as [pi-mono #3168](https://github.com/badlogic/pi-mono/issues/3168) (April 2026) and dupe [#3095](https://github.com/badlogic/pi-mono/issues/3095): "Custom providers aren't registered with pi-ai's provider streaming system. Only extensions with explicit streamSimple get registered." Both auto-closed by an OSS-weekend bot, not by a fix; no relevant changelog entry through v0.73.0.

Workaround: use pi's built-in OpenRouter provider (which does register) and supply the API key via the `OPENROUTER_API_KEY` env var. Tried auth.json first with `{"openrouter": {"type": "api_key", "key": "!op read 'op://Personal/OpenRouter/credential'"}}` since pi's docs claim `!command` resolution; pi v0.73.0 ignores it and reports "No API key for provider: openrouter". Tried env var sourced from `op read` in zsh init second; that fails on a fresh shell because `op` requires per-session `op signin` on a Mac mini (no Touch ID, so 1Password's desktop integration can't biometrically auto-unlock). Settled on macOS Keychain: seeded with `security add-generic-password -a "$USER" -s openrouter -w "$(op read ...)"` once, then zsh init exports the env var via `security find-generic-password -ws openrouter`. Keychain auto-unlocks at login, every shell inherits, no prompts. 1Password remains the offline backup for syncing the same key to other hosts.

---

## Entry Guidelines

Keep entries brief. Structure each as:

- Date and descriptive title
- **Key Insight:** One sentence capturing the core learning
- 2-4 sentences of essential context
- Optional: Relevant command or code snippet
- Optional: Link to docs for deeper dive

Focus on "what" and "why", not detailed "how". Reader can consult docs for implementation details.

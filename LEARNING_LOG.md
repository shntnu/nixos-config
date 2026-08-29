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

Ubuntu gets CLI tools and dotfiles but not GUI apps or system services.
Those need `apt install`.

## 2025-01-21: Home Manager's Two Modes

**Key Insight:** Home Manager runs in integrated mode on NixOS/macOS (inside system rebuild) but standalone mode on Ubuntu.

Home Manager isn't just for Ubuntu - it's used everywhere, differently:

- NixOS/macOS: Loaded as a module in system configurations, runs during `nixos-rebuild`/`darwin-rebuild`
- Ubuntu: Runs standalone via `home-manager switch` since no system rebuild exists

Same Home Manager, different delivery mechanism.
System rebuild carries it on NixOS/macOS; Ubuntu runs it directly.

## 2025-01-26: Nix Overlays for Package Version Updates

**Key Insight:** Overlays let you override package versions when nixpkgs is behind upstream releases.

Encountered Nextflow 24.08.0-edge in nixpkgs but needed 25.08.0-edge for plugin compatibility.
Solution: create an overlay that fetches the latest version directly from GitHub releases.
Overlays modify the package set before it's used, allowing version updates without waiting for nixpkgs.

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

Hit hash mismatch building `awscli2` because nixpkgs had a stale hash for `prompt-toolkit` dependency.
Adding `home-manager.inputs.nixpkgs.follows = "nixpkgs"` is good practice (prevents multiple nixpkgs versions, reduces disk usage) but didn't fix this upstream package issue.
Solution: moved `awscli` to Homebrew brews instead of nixpkgs.

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

For packages that update frequently (like `claude-code` with hourly releases), imperative installation is simpler than declarative flake-based management.
Adding a package as a flake input requires passing it through multiple configuration layers, while `nix profile install github:owner/repo` installs directly to your user profile.
Update independently with `nix profile upgrade` without rebuilding your entire system configuration.

```bash
# Simple imperative install
nix profile install github:sadjow/claude-code-nix

# Update when needed (use profile name, not URL; --refresh bypasses cache)
nix profile upgrade claude-code-nix --refresh
```

Use declarative (flake-based) for system packages that change with your config; use imperative for tools you want to update independently.

## 2026-02-14: Why Nix Flake Wrappers Over npm/Homebrew for CLI Tools

**Key Insight:** Third-party nix flake wrappers (like `sadjow/claude-code-nix`, `sadjow/gemini-cli-nix`, and `sadjow/codex-cli-nix`) solve problems that `npm install -g` and Homebrew cannot.

When adding `gemini-cli`, considered Homebrew (macOS-only, won't work on NixOS), npm global install, and nixpkgs (version 0.17.0 vs latest 0.28.2 — same lag problem as claude-code).
The `sadjow` flake wrappers provide: disabled auto-update (respects Nix store immutability), rollback via `nix profile rollback`, and hourly CI-driven version updates with hash verification.
For Node.js tools (claude-code, gemini-cli), they also provide Node.js version isolation.
Codex CLI is a native Rust binary so the wrapper just fetches the prebuilt release — no Node.js needed.

```bash
# All three tools follow the same pattern
nix profile install github:sadjow/codex-cli-nix
nix profile upgrade codex-cli-nix --refresh
```

## 2026-02-19: nix-darwin's `brew bundle --no-upgrade` Default

**Key Insight:** `build-switch` won't upgrade already-installed Homebrew formulae because nix-darwin runs `brew bundle install --no-upgrade` by default.

Tried updating specstory from 1.0.0 to 1.7.0.
Two separate systems are involved: nix-homebrew (zhaofengli) manages Homebrew itself and tap availability only ("does not manage any package installed by it"), while nix-darwin's `homebrew.*` module manages installed formulae via `brew bundle`.
The `--no-upgrade` flag means missing formulae get installed but existing ones are never upgraded.
Required a manual `brew upgrade specstoryai/tap/specstory`.

```bash
# Full update flow for custom tap brews (with default settings)
nix flake update specstoryai-tap
nix run .#build-switch
brew upgrade specstoryai/tap/specstory

# Or set in modules/darwin/home-manager.nix to auto-upgrade on rebuild:
# homebrew.onActivation.upgrade = true;
```

Key distinction: nix-homebrew = tap sources; nix-darwin `homebrew.*` = installed packages.
The `onActivation.upgrade` default of `false` is intentional for idempotent rebuilds.

## 2026-03-21: Homebrew Cask Reinstall vs Upgrade for Auto-Updating Apps

**Key Insight:** Apps that auto-update internally (like Obsidian) can outgrow their Homebrew cask installer, requiring `brew reinstall --cask` rather than a version upgrade.

Obsidian's app bundle auto-updates its asar package (1.10.3 → 1.12.4) independently of Homebrew.
The cask version stayed at 1.10.3, leaving the old installer wrapper in place — missing the new CLI (`obsidian.wrapper.sh`).
`homebrew.onActivation.upgrade = true` only triggers upgrades when a new cask *version* exists; it doesn't detect that the installed app has self-updated past its cask.
`brew reinstall --cask` replaces the entire app bundle and links the current CLI entry point.

```bash
# When cask version lags behind the app's self-update
brew reinstall --cask obsidian
# Not: brew upgrade --cask obsidian (no new cask version to upgrade to)
```

## 2026-06-28: Stale Homebrew Casks Need a Flake Bump, Not `brew update`

**Key Insight:** With `nix-homebrew` and `mutableTaps = false`, the cask catalog is pinned to the `homebrew-cask` flake input — `brew update` is a no-op by design, so a sunset/stale cask is fixed by bumping that one input and rebuilding.

ChatGPT's app showed "This version has been sunset"; its in-app updater just bounced to the download page, and the installed cask version was itself already sunset (the catalog lagged OpenAI's release).
`brew update` failed with `/nix/store/...-source/.git: Permission denied` because the taps are read-only Nix store paths.
The fix is targeted, not a full `nix flake update` (that bumps nixpkgs/msgvault/private/all taps — a world rebuild for a one-app problem).
Two related-but-distinct failure modes now in this log: app self-updates *past* its cask → `brew reinstall --cask` (Obsidian); cask catalog *lags behind* the app → bump the flake input (below).

```bash
nix flake update homebrew-cask   # pulls latest cask catalog revision
nix run .#build-switch           # onActivation.upgrade=true reinstalls at new version
```

Separately, if a cask's app bundle goes missing from `/Applications` but brew's receipt still says installed, `build-switch` won't notice — `brew reinstall --cask <name>` re-syncs disk to receipt.

## 2026-07-05: Refactoring Out Starter-Template Residue

**Key Insight:** Two starter-template patterns were the whole reason this repo felt unmaintainable - a `fetchTarball` of a *moving* branch, and a "shared config" that was a raw attrset instead of a real module.

The `dustinlyons/emacs-overlay` was pulled via `builtins.fetchTarball` of `refs/heads/master` pinned by `sha256`.
Pinning a branch (not a tag/commit) by hash is a time bomb: the moment upstream pushes, every build on every machine fails with a hash mismatch for a package I don't even customize.
Worse, it was a no-op - `nix store diff-closures` before/after removing it showed zero change, because nixpkgs' `emacs` already resolves to `emacs30`.
Lesson: never `fetchTarball` a branch; if you need a pinned dep it belongs in `flake.nix` inputs (which lock to a commit), and check whether an overlay actually changes the closure before trusting it.

The bigger wart: `modules/shared/home-manager.nix` was a plain attrset `import`ed and stitched into consumers with `lib.recursiveUpdate` plus a hand-written `lib.mkMerge` of `zsh.initContent`.
That defeats the module system - you can't see what wins, and every consumer re-implements the merge.
Rewriting it as a normal HM module (`programs = { ... }`, pulled in via `imports`) let darwin and headless just declare their deltas and let the module system merge them (`lib.mkAfter` for shell init, plain attrs for git).
The headless file lost ~40 lines of `sharedPrograms`/`recursiveUpdate`/`mkMerge` plumbing.

Also consolidated two overlay mechanisms into one (`modules/shared/overlays.nix`, applied everywhere via `modules/shared/nixpkgs.nix`) so servers get the same `nextflow` pin and `msgvault` as the Macs - the point of the repo is that all machines match.

Verification that made the refactor safe: snapshot `nix eval ...drvPath` for all five configs before touching anything, then `nix build` + `nix store diff-closures /run/current-system ./result` after.
A refactor that's meant to be behavior-preserving should show an *empty or explainable* closure diff; anything else is an unintended change.

Postscript - a pin you no longer need is just debt.
The nextflow overlay (pinned Sep 2025 to jump 24.08 -> 25.08) was still carrying a hardcoded version and hash long after nixpkgs caught up and passed it.
The overlay wasn't buying anything anymore - nixpkgs already had a version that met the original need - so it was pure maintenance surface: a custom derivation to keep bumping for a tool I barely run.
Deleting it made the config strictly simpler and let nixpkgs own the version like every other package.
The point isn't which nextflow version anyone ends up on; it's that an override outlives its reason, and the maintainable move once upstream can provide the thing is to drop the pin, not to keep tending it.

Second lesson, mechanical: build on the real target, not a proxy.
I'd reasoned on the Mac that unifying the overlays "just adds the pin on the servers too," a no-op.
Actually building the profile on oppy (`rsync` the tree over, `nix build .#homeConfigurations."shsingh@oppy".activationPackage`) and diffing against oppy's *live* profile is what surfaced that the pin was even in play there.
An eval on the build host is not a build on the target host; the closure diff that told the real story only appeared on oppy.

## 2026-07-14: Wrap Native Python Tools at the VS Code Process Boundary

**Key Insight:** VS Code Remote can strip `LD_LIBRARY_PATH` from its extension host, so a shell-level export is insufficient; restore native library paths in a wrapper around the affected extension process.

The marimo extension launches its bundled uv environment outside project `direnv` shells.
Process inspection after a full VS Code restart showed that the extension host and `marimo-lsp` retained `NIX_LD_LIBRARY_PATH` but not `LD_LIBRARY_PATH`, so the manylinux `pyzmq` wheel still could not load `libstdc++.so.6`; testing a clean login shell had exercised the wrong boundary.
Home Manager now configures `marimo.lsp.path` to a narrow wrapper that discovers the installed extension and restores the Nix runtime only for `marimo-lsp` and its child kernels.

## 2026-07-29: Claude Desktop on a Lab Server - Packaged, Then Scrapped

**Key Insight:** A package that installs cleanly can still be the wrong thing to install; over SSH the CLI already covers it, and the app adds a third-party repackaging to maintain forever.

Claude Desktop for Linux ships only as a `.deb` from Anthropic's apt repo, and nixpkgs has no `claude-desktop` (request #366213 closed unpackaged).
The route that worked was `github:aaddrick/claude-desktop-debian` (repackages that official `.deb`): flake input, overlay entry beside `msgvault`, one line in `modules/headless/packages.nix`.
Built and ran on karkinos, then reverted - updates ride `nix flake update` instead of the nixpkgs bump, and it lands in the shared headless profile so oppy and spirit inherit it too.
Before adding a flake input for a GUI app: what does it do that the CLI can't, and who bumps it in six months?

## 2026-08-06: GNOME 49 Screenshots Are Shortcut-Only

**Key Insight:** On GNOME 49 Wayland there is no scriptable screenshot path, so a keybinding is the fix and a CLI tool is not a substitute.

`org.gnome.Shell.Screenshot.Screenshot` over D-Bus returns `AccessDenied` - GNOME 49 allowlists that interface to the media-keys daemon and the desktop portal, so a plain shell caller is refused.
`gnome-screenshot` 41.0 builds fine but Shell 49 rejects it too ("resorting to fallback X11") and writes no file, and `grim`/`slurp` are wlroots tools that Mutter does not serve.
The portal works but pops a confirmation dialog, which rules out unattended capture.
That leaves the shell keybindings, rebound in `modules/headless/home-manager.nix` because the Air75 V2 has no PrtSc key; `gsettings set org.gnome.shell.keybindings ...` takes effect immediately, no restart.

## 2026-08-20: Signed Release Assets Can Change Without a Version Bump

**Key Insight:** A versioned GitHub release asset can still be replaced after publication, so validate a new digest before updating a Nix fixed-output hash.

Kata's `v0.14.3` macOS ARM archive was replaced when its binary received a Developer ID signature, changing the archive hash while its reported version, commit, platform, and build timestamp remained the same.
GitHub's release API digest and the binary's version and code-signing metadata provided independent checks before the package and documentation hashes were updated.

## 2026-08-22: Backup Jobs Must Not Follow a Daemon Restart Loop

**Key Insight:** A backup oneshot should weakly depend on its daemon, and failed off-host transfers should reuse a deterministic staging path.

`Requires=kata.service` coupled the active backup job to every daemon failure, while the persistent timer retried it as the daemon restarted.
Each retry created another local export, and a timestamped remote partial name leaked a new file whenever the destination ran out of space.
Using `Wants=kata.service` lets an in-progress export finish independently, and one staging name per immutable backup bounds an interrupted transfer to one partial file.

## 2026-08-22: Verify Listener Ownership Before Accepting a Managed Kata Service

**Key Insight:** A healthy endpoint does not prove that the managed Kata unit has always owned its configured listener.

During a non-destructive audit, systemd repeatedly restarted the managed unit because another Kata process already held the listener.
After the competing process released it, the unit became healthy and the listener belonged to the service cgroup.
Check the listener PID and cgroup, not only `systemctl is-active` or `kata health`, when qualifying a deployment or diagnosing restart loops.

## 2026-08-23: tmux Session Restore Replays a Snapshot That Can Never Update

**Key Insight:** tmux-continuum restores on every server start but can only save while a client is attached, so a server whose sessions are never attached replays one frozen snapshot forever.

Caladan kept reopening shells in the admin and career folders long after the work in them had ended.
The sessions came from a Remote Control experiment: a launchd agent (May 2026) and later the `launch-remote-control` skill started `claude --remote-control` inside tmux sessions named `rc-<slug>`.
The agent was dropped on 2026-07-02 precisely because it "produced ghost sessions via tmux-resurrect", yet twelve days later a new `tmux-server` login agent reintroduced restore and its commit treated the returning sessions as a benefit.

Two mechanics made it permanent.
First, `@continuum-restore 'on'` fires whenever a fresh server starts, so simply typing `tmux` replays the file, and resurrect records only a pane's directory and command name, never the `claude` process that was running, which is why every restored pane was a bare shell.
Second, continuum's save hook lives in `status-right`, which redraws only for an attached client, so the detached ghosts could never write a newer save and `last` stayed pinned to a snapshot from six days earlier.

The login agent was not even the trigger: `launchctl print` showed `runs = 1` and `last exit reason = OS_REASON_CODESIGNING` with empty logs, so it had never once succeeded.
Diagnose the plugin that reacts to server startup, not the unit that appears to start it.
Both plugins were removed repo-wide and the agent deleted; the deliberate trade is that servers no longer restore sessions after a reboot, which was preferred over surprise resumption.

```bash
launchctl print gui/$(id -u)/org.nixos.<agent>   # "runs" and "last exit reason" reveal a unit that never worked
tmux show-options -g | grep -E 'continuum|resurrect'
```

## 2026-08-28: Codex's desktop launcher needs its own open-file limit

**Key Insight:** Raising zsh's open-file limit does not affect the desktop app, because the app starts its shared Codex server through `/bin/sh`.

Codex CLI 0.150.1 exhausted macOS's default soft limit of 256 while loading skills and starting MCP servers.
The shared app server had more than 230 descriptors open, so some skills and MCP servers failed nondeterministically during startup.
Home Manager now installs a `~/.local/bin/codex` launcher, which raises the soft limit to 4096 before executing the Nix profile's Codex binary.
The desktop bootstrap and interactive macOS shells both put that directory first on `PATH`.

---

## Entry Guidelines

Keep entries brief.
Structure each as:

- Date and descriptive title
- **Key Insight:** One sentence capturing the core learning
- 2-4 sentences of essential context
- Optional: Relevant command or code snippet
- Optional: Link to docs for deeper dive

Focus on "what" and "why", not detailed "how".
Reader can consult docs for implementation details.

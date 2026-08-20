# nixos-config

Personal Nix configuration for macOS, NixOS, and Ubuntu/WSL, based on [dustinlyons/nixos-config](https://github.com/dustinlyons/nixos-config).

Thanks to [@leoank](https://github.com/leoank) for bringing Nix to the Carpenter-Singh lab.

See also: [leoank/neusis](https://github.com/leoank/neusis), [HugoHakem/nix-os.config](https://github.com/HugoHakem/nix-os.config), [afermg/nix-configs](https://github.com/afermg/nix-configs)

## Quick Reference

Pick the workflow that matches where you are:

### macOS (caladan / laptop)

This flake owns the full system.
One command rebuilds everything (system + Home Manager):

```bash
nix run .#build-switch
```

### Lab servers (oppy / spirit / karkinos) — neusis-managed NixOS

On these machines, [neusis](https://github.com/shntnu/neusis) owns the **system configuration** (NixOS, user accounts, SSH keys).
This flake only manages **your Home Manager profile** (dotfiles, shell, programs).

```bash
# 1. Make your changes and stage them (flake only sees tracked files)
git add .

# 2. Apply your Home Manager profile
home-manager switch --flake '.#shsingh@oppy'      # on oppy
home-manager switch --flake '.#shsingh@spirit'    # on spirit
home-manager switch --flake '.#shsingh@karkinos'   # on karkinos
```

> **Do not** run `nix run .#build-switch` on these machines — that would attempt a full NixOS system rebuild from this flake, which is not what you want.
System changes go through neusis, which has a separate configuration per machine (`sudo nixos-rebuild switch --flake /path/to/neusis#<host>`).

To test-build without activating:

```bash
nix build '.#homeConfigurations."shsingh@oppy".activationPackage'
```

## Repo Map

```
flake.nix                       inputs + outputs (darwinConfigurations, homeConfigurations)
apps/aarch64-darwin/            build / build-switch / rollback (dispatch on hostname)
hosts/darwin/
  default.nix                   shared macOS base: nix settings, launchd agents, system.defaults
  caladan.nix, laptop.nix       per-host: private module + host-only casks/agents
modules/
  shared/
    nixpkgs.nix                 nixpkgs.config + overlays (used at darwin AND HM level)
    overlays.nix                msgvault (from the flake input)
    home-manager.nix            cross-platform HM module: zsh, git, vim, ssh, tmux
    packages.nix                cross-platform package list
  darwin/
    home-manager.nix            macOS user block: imports shared, adds mac-only shell + emacs
    casks.nix                   Homebrew casks (all Macs)
    dock/                        declarative dock module
    emacs/                       init.el + config.org
  headless/
    home-manager.nix            lab-server HM: imports shared, adds server deltas
    kata.nix                    reusable Kata config, user service, and backup timer
    packages.nix                server-only package list
```

`modules/shared/*` is the single source of truth; `darwin/` and `headless/` import it and layer platform-specific config.

## How It All Fits Together

```
  oppy / spirit / karkinos (NixOS)
  =================================

┌─────────────────────────────┐
│  neusis (shntnu/neusis)     │
│  Owns: NixOS system, users, │
│        SSH keys              │
│  Cmd:  sudo nixos-rebuild   │
│    switch --flake .#<host>   │
│  Note: shsingh homeModules  │
│        = null (opted out)    │
└──────────────┬──────────────┘
               │ account + SSH keys
               ▼
┌─────────────────────────────┐
│  nixos-config (this repo)   │
│  Owns: Home Manager profile │
│  Cmd:  home-manager switch  │
│    --flake .#shsingh@<host> │
└─────────────────────────────┘
```

On the NixOS machines, the two repos are independent - run either in any order, and one never triggers the other.

## Headless Home Manager

`modules/headless/home-manager.nix` is the personal, non-GUI Home Manager module for lab servers and other SSH-first Linux machines.
It imports the shared shell/git/tmux/SSH setup, adds server-oriented packages from `modules/headless/packages.nix`, and is exported as `homeModules.shsingh-headless` for external flakes.

The standalone `homeConfigurations.shsingh@oppy`, `homeConfigurations.shsingh@spirit`, and `homeConfigurations.shsingh@karkinos` targets let this repo build the same profile directly for lab servers, while a shared repo such as `neusis` can skip only the `shsingh` Home Manager profile without changing other users' home-manager workflows.
Each standalone target also imports a matching `private.homeModules.<host>` when that output exists, following the same public-behavior/private-facts split used by the Darwin host modules.

## Msgvault archive replication

Caladan is the only Gmail, IMAP, Slack, and iMessage archive writer.
Its private host module creates a transactionally consistent `msgvault backup` snapshot every day at 04:10, restores it with analytics into alternating publication slots on the attached backup volume, and exposes only the credential-free restored archive over SSH.

The laptop and all three lab-server Home Manager profiles pull the published archive hourly at minute 40.
Each client updates its inactive slot, checks SQLite integrity and the message, attachment, and source counts, confirms that credential paths are absent, and only then atomically switches `~/.local/share/msgvault-mirror/current`.
Interrupted or invalid transfers leave the previous local mirror active.

Use the local mirror without Caladan:

```bash
msgvault-mirror stats
msgvault-mirror search "incident review"
msgvault-mirror show-message MESSAGE_ID
```

The wrapper permits read and export commands only.
Run `msgvault-mirror-status` to report the active snapshot and freshness; it exits nonzero when a client has not completed in three hours or the publisher has not completed in 36 hours.
Client failures are also visible in the user service journal on Linux and `/tmp/msgvault-pull-mirror.err.log` on macOS.
Publisher failures are logged to `/tmp/msgvault-publish-snapshot.err.log` on Caladan.

The backup repository is append-only because the current msgvault backup format does not yet support pruning.
Do not add `--include-config`, `--include-tokens`, or `--allow-plaintext-secrets` to the publisher.

## Development Commands

```bash
nix flake update          # Update flake dependencies
nix flake check           # Check flake configuration
nix develop               # Enter development shell
nix shell nixpkgs#<pkg>   # Try a package without installing
```

## Further Documentation

- [`CLAUDE.md`](./CLAUDE.md) — architecture details and module organization (for Claude Code)
- [`LEARNING_LOG.md`](./LEARNING_LOG.md) — Nix/Homebrew/system learnings and gotchas
- [Shared repository memory with Hindsight](./docs/hindsight.md) - public setup specification for Claude Code, Codex, and Pi over REST, with no Hindsight MCP
- [Text a local Codex agent through Telegram](./docs/codex-telegram.md) - tested single-user gateway specification using outbound long polling
- [Share one Kata work ledger across coding agents and private machines](./docs/kata.md) - tested single-user remote-ledger specification with named-daemon and per-workspace client patterns

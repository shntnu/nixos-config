# nixos-config

Personal Nix configuration for macOS, NixOS, and Ubuntu/WSL, based on [dustinlyons/nixos-config](https://github.com/dustinlyons/nixos-config).

Thanks to [@leoank](https://github.com/leoank) for bringing Nix to the Carpenter-Singh lab.

See also: [leoank/neusis](https://github.com/leoank/neusis), [HugoHakem/nix-os.config](https://github.com/HugoHakem/nix-os.config), [afermg/nix-configs](https://github.com/afermg/nix-configs)

## Quick Reference

Pick the workflow that matches where you are:

### macOS (caladan / laptop)

This flake owns the full system. One command rebuilds everything (system + Home Manager):

```bash
nix run .#build-switch
```

### Lab servers (oppy / karkinos) — neusis-managed NixOS

On these machines, [neusis](https://github.com/shntnu/neusis) owns the **system configuration** (NixOS, user accounts, SSH keys). This flake only manages **your Home Manager profile** (dotfiles, shell, programs).

```bash
# 1. Make your changes and stage them (flake only sees tracked files)
git add .

# 2. Apply your Home Manager profile
home-manager switch --flake '.#shsingh@oppy'      # on oppy
home-manager switch --flake '.#shsingh@karkinos'   # on karkinos
```

> **Do not** run `nix run .#build-switch` on these machines — that would attempt a full NixOS system rebuild from this flake, which is not what you want. System changes go through neusis (`sudo nixos-rebuild switch --flake /path/to/neusis#oppy`).

To test-build without activating:

```bash
nix build '.#homeConfigurations."shsingh@oppy".activationPackage'
```

### spirit — Ubuntu 22.04 (standalone Home Manager)

spirit is not managed by neusis (NixOS migration planned but not yet done). Home Manager runs standalone:

```bash
git add .
home-manager switch --flake '.#shsingh@spirit'
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
    packages.nix                server-only package list
```

`modules/shared/*` is the single source of truth; `darwin/` and `headless/` import it and layer platform-specific config.

## How It All Fits Together

```
  oppy / karkinos (NixOS)               spirit (Ubuntu)
  ========================               ================

┌─────────────────────────────┐
│  neusis (shntnu/neusis)     │
│  Owns: NixOS system, users, │         (no neusis - Ubuntu
│        SSH keys              │          manages its own OS)
│  Cmd:  sudo nixos-rebuild   │
│        switch --flake .#oppy │
│  Note: shsingh homeModules  │
│        = null (opted out)    │
└──────────────┬──────────────┘
               │ account + SSH keys
               ▼
┌─────────────────────────────┐   ┌──────────────────────────┐
│  nixos-config (this repo)   │   │  nixos-config (this repo)│
│  Owns: Home Manager profile │   │  Owns: Home Manager      │
│  Cmd:  home-manager switch  │   │  Cmd:  home-manager switch│
│    --flake .#shsingh@oppy   │   │    --flake .#shsingh@spirit│
└─────────────────────────────┘   └──────────────────────────┘
```

On the NixOS machines, the two repos are independent - run either in any order, and one never triggers the other.
On spirit, there is only one command to run (no neusis involvement).

## Headless Home Manager

`modules/headless/home-manager.nix` is the personal, non-GUI Home Manager
module for lab servers and other SSH-first Linux machines. It imports the
shared shell/git/tmux/SSH setup, adds server-oriented packages from
`modules/headless/packages.nix`, and is exported as
`homeModules.shsingh-headless` for external flakes.

The standalone `homeConfigurations.shsingh@oppy`,
`homeConfigurations.shsingh@spirit`, and
`homeConfigurations.shsingh@karkinos` targets let this repo build the same
profile directly for lab servers, while a shared repo such as `neusis` can skip
only the `shsingh` Home Manager profile without changing other users'
home-manager workflows.

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

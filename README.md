# nixos-config

Personal Nix configuration for macOS, NixOS, and Ubuntu/WSL, based on [dustinlyons/nixos-config](https://github.com/dustinlyons/nixos-config).

Thanks to [@leoank](https://github.com/leoank) for bringing Nix to the Carpenter-Singh lab.

See also: [leoank/neusis](https://github.com/leoank/neusis), [HugoHakem/nix-os.config](https://github.com/HugoHakem/nix-os.config), [afermg/nix-configs](https://github.com/afermg/nix-configs)

```bash
# Apply changes - macOS/NixOS (includes Home Manager in system rebuild)
nix run .#build-switch

# Apply changes - Ubuntu/WSL (Home Manager standalone, no GUI apps)
nix run 'home-manager/master' -- switch --flake '.#shsingh'

# Build a headless lab-server Home Manager profile
nix build '.#homeConfigurations."shsingh@oppy".activationPackage'

# Apply a headless lab-server Home Manager profile
home-manager switch --flake '.#shsingh@oppy'
```

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

See [`CLAUDE.md`](./CLAUDE.md) for documentation and [`LEARNING_LOG.md`](./LEARNING_LOG.md) for Nix insights.

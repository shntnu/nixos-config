# nixos-config

Personal Nix configuration for macOS, NixOS, and Ubuntu/WSL, based on [dustinlyons/nixos-config](https://github.com/dustinlyons/nixos-config).

See also: [leoank/neusis](https://github.com/leoank/neusis), [HugoHakem/nix-os.config](https://github.com/HugoHakem/nix-os.config), [afermg/nix-configs](https://github.com/afermg/nix-configs)

```bash
# Apply changes - macOS/NixOS (system-level)
nix run .#build-switch

# Apply changes - Ubuntu/WSL (user-level only, no GUI apps)
nix run 'home-manager/master' -- switch --flake '.#shsingh'
```

See [`CLAUDE.md`](./CLAUDE.md) for documentation and [`LEARNING_LOG.md`](./LEARNING_LOG.md) for Nix insights.

# Development and updates

## Ownership and layout

The public flake manages macOS systems through nix-darwin and standalone Linux user profiles through Home Manager.
Linux system administration belongs to the separate system-configuration repository.
Access to the `private` input is required for the configured Darwin and headless builds.

[`flake.nix`](../flake.nix) defines the available host keys and passes inputs through `specialArgs` or `extraSpecialArgs`.
Darwin host modules import their private counterpart; headless profiles import `private.homeModules.default` and an optional matching `private.homeModules.<host>`.
The exported `homeModules.shsingh-headless` lets downstream flakes consume the public headless module independently.

| Change | Source |
| --- | --- |
| Shared shell, Git, SSH, tmux, or packages | `modules/shared/home-manager.nix`, `modules/shared/packages.nix` |
| Nixpkgs configuration and overlays | `modules/shared/nixpkgs.nix`, `modules/shared/overlays.nix` |
| macOS user settings or shared casks | `modules/darwin/home-manager.nix`, `modules/darwin/casks.nix` |
| Shared macOS system settings | `hosts/darwin/default.nix` |
| Linux user settings or packages | `modules/headless/home-manager.nix`, `modules/headless/packages.nix` |
| Host-specific services, paths, or credentials wiring | Matching module in the private input |

Both platform modules import `modules/shared/` through the Nix module system.
Nixpkgs configuration is imported at the Darwin system level and the headless Home Manager level.
Edit managed sources rather than generated dotfiles.

## Build and apply

Inspect the working tree before staging changes with `git add .`; Git-backed flakes omit untracked files.
Documentation-only changes need diff and link checks, with no build or activation.
For configuration changes, build the affected target before applying it.
Replace `<user>` and `<host>` with an existing key from `flake.nix`.

On Apple Silicon macOS:

```bash
nix run .#build           # Build without activation
nix run .#build-switch    # Apply system and Home Manager changes
nix run .#rollback        # Roll back the system generation
```

The build scripts map `scutil --get LocalHostName` to a Darwin configuration key.
Renaming a Mac requires updating the hostname mappings in `apps/aarch64-darwin/{build,build-switch,rollback}`, plus the flake key if it changes.
Activation can require a sudo password.

On Linux, run these commands on the target host:

```bash
nix build '.#homeConfigurations."<user>@<host>".activationPackage'
home-manager switch --flake '.#<user>@<host>'
```

The Darwin apps are not Linux rebuild commands.
Do not run `nixos-rebuild` from this flake; it does not own the Linux system configuration.
An SSH command does not automatically load the interactive Home Manager shell environment.
Check tools with `ssh <host> 'zsh -ic "command -v home-manager"'` or use an explicit executable path.

## Dependency updates

```bash
nix flake update <input>   # Update one dependency
nix flake check           # Check the flake
nix develop               # Enter the development shell
nix shell nixpkgs#<pkg>   # Try a package
```

Homebrew taps are pinned flake inputs, and `homebrew.onActivation.upgrade = true` upgrades formulae and casks during Darwin activation.
Update the relevant tap input and then build and apply the Darwin configuration.
If an app's self-updater has outgrown its cask installer or its application bundle is missing, `brew reinstall --cask <app>` can repair the installation.
See [LEARNING_LOG.md](../LEARNING_LOG.md) for the underlying gotchas.

The public lock pins the private input by revision.
Configuration changes there need a committed, available private revision followed by `nix flake update private` here before an ordinary build can consume them.
A temporary build can instead use the adjacent working tree:

```bash
nix run .#build -- --override-input private path:../nixos-config-private
```

The first `--` forwards arguments to the app's inner Nix command.
An override is temporary validation; documentation-only private edits do not require a lock update or activation.

## Codex CLI

All machines use OpenAI's standalone installer for Codex.
The same install and update command applies to macOS and Linux.
Home Manager owns the launcher at `~/.local/bin/codex`; the installer owns the binary under `~/.local/libexec/codex`.
The macOS launcher also raises the open-file limit to 4096.

The desktop app's automatic updater is separate from these standalone CLI installations.
This configuration does not enable unattended CLI updates, and startup update checks do not establish a scheduled updater.
See OpenAI's [app update documentation](https://learn.chatgpt.com/docs/enterprise/manage-app-updates) and [startup update setting](https://learn.chatgpt.com/docs/config-file/config-reference#check_for_update_on_startup).

Run this command on each machine when updating its CLI.
On a fresh machine, install the binary before activating Home Manager:

```bash
curl -fsSL https://chatgpt.com/codex/install.sh | \
  env PATH="$HOME/.local/libexec/codex:$PATH" \
    CODEX_INSTALL_DIR="$HOME/.local/libexec/codex" sh
```

For unattended deployment, add `CODEX_NON_INTERACTIVE=1` to `env`.
That variable skips installer prompts for this invocation; it does not schedule future updates.
After activation, verify `~/.local/bin/codex --version`, then remove the old `codex-cli-nix` entry if it appears in `nix profile list`.
Restart existing Codex sessions or reconnect the desktop SSH connection to use the new binary.
No machine reboot is needed.

## Reference documents

Public specifications describe reusable behavior and acceptance checks.
Deployment locations, service inventory, secret wiring, and current operational state belong in the private repository.

- [Hindsight memory](hindsight.md).
- [Codex Telegram gateway](codex-telegram.md).
- [Kata shared work ledger](kata.md).
- [Headlong provider configuration](headlong.md).
- [Zvec-Grep evaluation](zvec-grep-evaluation.md).
- [Nix and application lessons](../LEARNING_LOG.md).

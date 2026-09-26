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

## Remote deployment

The `deploy` app uses [deploy-rs](https://github.com/serokell/deploy-rs) to build and transfer configurations, then activate them over SSH.
Use the same locked inputs for every selected target.
Targets need Nix and SSH access but do not need configuration checkouts or Git access to the private input.
The authoring machine fetches that input before sending sources to the Linux builder.

Each Darwin configuration has a `<host>.system` deployment profile.
Each standalone Home Manager configuration has a `<host>.home` deployment profile, using its existing host key without the username prefix.
Linux system configuration remains owned by the separate system flake.
Its Home Manager integration must continue to exclude users whose profiles are managed here.

First, stage new source files and build the affected configurations.
Use an Apple Silicon controller for Mac builds.
Use `deploy-linux` to build and deploy Linux profiles on an `x86_64-linux` SSH builder.
The app copies its own immutable flake and locked inputs with `nix flake archive`, then runs deploy-rs against the archived source on the builder.
No Git checkout, daemon reconfiguration, or sudo bootstrap is needed on the builder.
It needs Nix on its noninteractive SSH PATH and permission to accept the archived store paths.
The builder also needs SSH access to the deployment targets as the configured user.
Use a trusted builder because the archived sources include the private configuration.

Linux outputs stay on the builder and selected targets, avoiding a second copy on the Mac.
Ordinary Nix distributed builds copy outputs back to the controller, which can be expensive for large profiles.
Nix reuses shared dependencies while building a separate generation for each host.
Keep the builder hostname and operational examples in the private operations documentation.

Next, build and transfer a selected profile without activating it:

```bash
nix run .#deploy -- --dry-activate '.#<mac>.system'
nix run .#deploy-linux -- <builder> --dry-activate '.#<host>.home'
```

The dry run prints the activation command and leaves the active generation unchanged.
It checks building, transfer, and remote execution, but does not test actual dotfile linking, service restarts, or Homebrew actions.
The flake's deployment checks validate schemas and activation wrappers separately for Darwin and Linux.
They also check SSH argument forwarding; that check can be run directly with `bash tests/deploy-linux.sh`.

Finally, activate the selected profiles:

```bash
nix run .#deploy -- '.#<mac>.system'
nix run .#deploy-linux -- <builder> --targets '.#<host-a>.home' '.#<host-b>.home'
```

Select `.system` profiles with the Mac command and `.home` profiles with the Linux command.
Passing `.` to deploy-rs selects every configured machine, including incompatible platforms.
Darwin deployment, including a normal dry run, prompts for sudo authentication.
Standalone Home Manager deployment runs as the account owner.
The `deploy` app also accepts a revision-qualified remote flake as its target.
For example, `github:<owner>/<repo>/<revision>#<host>.home` deploys a published revision without using a target checkout.
For `deploy-linux`, use `.#<host>.home` targets; the app expands them to the archived source path.
Publish a revision before using its remote URL; a local staged checkout can be tested without pushing it.

Deploy-rs keeps its Linux `home` profile separate from Home Manager's `home-manager` profile.
Automatic rollback requires a previous generation managed by deploy-rs, so retain the native generation history during the first deployment.
After a failed first Home Manager deployment, select the previous path from `home-manager generations` and run its `activate` script.
Macs retain the existing `rollback` app.
Nix rollback does not undo changes to application data or Homebrew installations.

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

## msgvault source package

The `msgvault` input pins a source commit, and `modules/shared/msgvault-package.nix` builds the executable.
The installed CLI, service commands, and remote client use the same `pkgs.msgvault` package.
Development builds inside a source checkout do not change that package.

The package owns its Go and Bun versions because upstream no longer provides Nix packaging.
Go modules and frontend dependencies have separate fixed-output hashes.
The frontend dependency fetch includes optional packages for all supported platforms, and the application builds without network access.
The build validates the frontend assets before embedding them and checks the installed executable's embedded assets.

When updating msgvault, change the source revision in `flake.nix` and update the package version.
Check the source's `go.mod` and `web/package.json` for toolchain changes.
If dependencies changed, replace the relevant hash with `lib.fakeHash`, build that dependency output, and record the reported hash.

```bash
nix build --option eval-cache false .#msgvault.goModules .#msgvault.webDependencies
nix build --option eval-cache false .#msgvault
```

Run the affected platform builds described above, including a headless profile when changing the shared package.
Test upgrades against a consistent archive copy before activation, and check imports, cache rebuilds, search, and remote clients.
Record machine-specific evidence and the deployment decision in the private input's documentation.
After activation, restart an idle daemon and verify its executable because replacing the installed CLI does not replace an already running process.
Keep an archive backup for rollback because a Nix generation rollback does not undo database migrations.

## Codex CLI

All machines use OpenAI's standalone installer for Codex.
On macOS, the installer owns `~/.local/bin/codex`, including replacements made by Codex's updater.
Nix sets a minimum inherited launchd soft file limit of 4096, so Codex does not need a wrapper at that path.
The limit applies to newly launched GUI and SSH processes across the Mac; existing processes keep their inherited limits.
The launch job preserves the kernel file ceilings and uses the kernel per-process ceiling as the numeric hard limit when raising the soft limit.
On Linux, the installer also owns `~/.local/bin/codex`, which the desktop SSH bootstrap needs because it does not load zsh's `PATH`.
Home Manager only creates the installer's symlink there when the path is missing, so an updater replacement never blocks activation.

The desktop app's automatic updater is separate from these standalone CLI installations.
This configuration does not enable unattended CLI updates, and startup update checks do not establish a scheduled updater.
See OpenAI's [app update documentation](https://learn.chatgpt.com/docs/enterprise/manage-app-updates) and [startup update setting](https://learn.chatgpt.com/docs/config-file/config-reference#check_for_update_on_startup).

Install or update with:

```bash
curl -fsSL https://chatgpt.com/codex/install.sh | \
  env PATH="$HOME/.local/bin:$PATH" sh
```

Older Linux installations also have a `~/.local/libexec/codex/codex` symlink into the same standalone release; it is unused and harmless.

For unattended deployment, add `CODEX_NON_INTERACTIVE=1` to `env`.
That variable skips installer prompts for this invocation; it does not schedule future updates.
After activation, verify `~/.local/bin/codex --version`, then remove the old `codex-cli-nix` entry if it appears in `nix profile list`.
Restart existing Codex sessions or reconnect the desktop SSH connection to use the new binary.
For the macOS file-limit migration, activate Nix and inspect `sudo launchctl print system/org.nixos.file-limits` and `/var/log/org.nixos.file-limits.log` for a successful exit and a soft limit of at least 4096.
Check `launchctl limit maxfiles` and the unchanged `sysctl kern.maxfiles kern.maxfilesperproc` values.
Verify `ulimit -Sn` in a new GUI terminal and a new SSH session before relying on the setting.
A logout or reboot may be needed for existing parent processes to inherit it; do not restart active sessions automatically.

## imsg on macOS

`imsg` is packaged from the upstream macOS release in `modules/darwin/imsg-package.nix` and installed for Darwin hosts through Home Manager.
It sends through Messages.app with Apple events and verifies delivery by reading `~/Library/Messages/chat.db`, so the process context that launches it needs both Automation for Messages and Full Disk Access.
macOS attributes the grant to the parent context, not to `imsg`: a terminal app, `claude`, the ChatGPT app, or `/usr/libexec/sshd-keygen-wrapper` for SSH sessions.

Grant each context once by running a real send from it while sitting at the unlocked Mac and clicking Allow on the dialog:

```bash
imsg send --to +1XXXXXXXXXX --service imessage --text "permission test" --json
```

For the SSH context, run the same command through `ssh caladan 'zsh -ic "..."'`.
A dialog that times out is recorded as a denial with reason 9, and on macOS 26.6 the System Settings toggle for `sshd-keygen-wrapper` cannot undo it.
Clear it with `tccutil reset AppleEvents`, which resets every Automation decision for the user, then repeat the send and click Allow.
Verify the grant with the privacy database (`auth_value` 2 under `kTCCServiceAppleEvents` for `com.apple.MobileSMS`) and delivery with `is_sent` and `is_delivered` on the newest `message` row.

`imsg` 0.15.6 confirms a send only when the conversation is labeled iMessage; a send to a chat that Messages labels RCS, such as an owner's self-conversation, delivers but exits with `may_have_completed`.
Treat that as an upstream verifier limitation and check `chat.db` rather than retrying.

## Reference documents

Public specifications describe reusable behavior and acceptance checks.
Deployment locations, service inventory, secret wiring, and current operational state belong in the private repository.

- [Hindsight memory](hindsight.md).
- [Codex Telegram gateway](codex-telegram.md).
- [OpenClaw deployment pilot specification](openclaw.md).
- [Kata shared work ledger](kata.md).
- [Headlong provider configuration](headlong.md).
- [Zvec-Grep evaluation](zvec-grep-evaluation.md).
- [Nix and application lessons](../LEARNING_LOG.md).

# Share one Kata work ledger across coding agents and private machines

[Kata](https://www.katatracker.com/) is a lightweight issue tracker designed for coding-agent work.
This specification builds one durable Linux Kata server, same-host and remote CLI clients, stable repository project bindings, scheduled off-host backups, and the built-in browser UI over a trusted private network.
It is written as a portable handoff for a coding agent and can be implemented with Nix or translated into another managed configuration system.

The tested baseline is Kata `v0.14.3`, commit `410ee88`.
In August 2026, coding agents used this document to set up a fresh server/client deployment successfully and independently reproduced the core server, client, authentication, lifecycle, and restore contract.
A later production deployment used the reference Nix implementation for an in-place conversion and passed managed activation, restart, crash recovery, Home Manager reapplication, SSH-session independence, and off-host restore qualification.
Those are separate claims: the specification has worked for a fresh setup, while the recorded production conversion was not itself a clean-room installation.

Version-sensitive upstream references are the Kata [`v0.14.3` release](https://github.com/kenn-io/kata/releases/tag/v0.14.3), [remote-daemon guide](https://www.katatracker.com/operations/remote-daemon/), [configuration reference](https://www.katatracker.com/reference/configuration/), [agent workflow](https://www.katatracker.com/workflows/agents/), and [backup and restore guide](https://www.katatracker.com/operations/backup-restore/).

## Give this specification to a coding agent

For a new server and client, identify the machines and say:

> Implement and test the Kata deployment in this document on these machines. > Preserve their existing managed configuration and ask before any production cutover, reboot, credential-bearing browser action, destructive restore, network-policy change, or repository push.

To connect only a new client, say:

> Connect this machine and repository to my existing shared Kata server using the client contract in this document, and run the client acceptance checks.

The agent must read this document completely, determine whether each machine is a server, client, or both, and inspect the existing package, configuration, service, firewall, private-network, Kata, and workspace state before changing anything.
It must update the owning Nix, Home Manager, chezmoi, system package, or service source rather than editing generated files.
Before acting, it must name the files, services, listener, secret boundary, backup locations, test records, and external copies it intends to create or change.

The ordinary setup instruction does not authorize changing private-network ACLs or device identity, publishing a listener, exposing a token, rebooting a shared host, deleting ledger data, replacing a live database, committing unrelated changes, or pushing a repository.

## Required outcome

One always-on unprivileged Linux account owns one SQLite database and the only Kata daemon for the deployment.
Every CLI, including CLIs on the server, resolves its workspace to that daemon instead of starting an independent local ledger.
The daemon listens on one literal stable private address, never `0.0.0.0`, `::`, or a public interface.

```text
same-host CLI --------------------+
                                  |
remote CLI -> private overlay ----+-> literal private IP:7777
                                  |        -> one managed Kata daemon
browser -> exact private hostname +        -> one SQLite database
```

The baseline is a trusted single-operator deployment protected by one high-entropy static bearer token.
The private network supplies encrypted transport and membership control, while Kata uses private plaintext HTTP inside that boundary.
Both token-bearing CLI clients and the server explicitly opt in with `KATA_TRUST_PRIVATE_NETWORK=1`.
Use HTTPS and a separately designed authentication boundary if the private network is insufficient or the deployment becomes multi-user.

The CLI target uses the literal private IP.
The browser uses one exact private hostname configured as both the public origin and an allowed host.
Do not weaken either path to make an initial health check pass.

## Resolve these values first

- `<server-user>`: the unprivileged account that owns the service and database.
- `<private-ip>`: a stable literal private address routed by the existing private network.
- `<browser-hostname>`: the exact private name users enter in a browser.
- `<kata-port>`: normally `7777`.
- `<kata-binary>`: the absolute path installed by the managed package source.
- `<daemon-name>`: a stable non-secret client catalog name.
- `<token-env>`: the environment-variable name referenced by the catalog, normally `KATA_AUTH_TOKEN`.
- `<project-name>`: the stable non-secret project name shared by its checkouts.
- `<workspace>`: the repository root on each client.
- `<actor>`: one stable identity for the same human across machines.
- `<backup-directory>`: an owner-only local collection.
- `<off-host-destination>`: a distinct authenticated machine and owner-only collection.

Confirm that the browser hostname resolves to the private IP, the clients can route to the server, and the selected port is unused.
Preserve the host's existing private-network identity and ACL policy unless the user separately authorizes a change.

## Choose an implementation path

### Reference Nix implementation

This repository contains the tested implementation:

- [`modules/shared/kata.nix`](../modules/shared/kata.nix) packages the pinned release.
- [`modules/headless/kata.nix`](../modules/headless/kata.nix) defines the reusable Home Manager client, server, backup service, and timer options.
- [`modules/shared/packages.nix`](../modules/shared/packages.nix) installs the CLI in the shared profile.

On a Nix-managed machine, read those modules and use them instead of recreating their generated TOML, systemd units, or backup wrapper by hand.
A deployment-specific module should supply only the endpoint, browser origin, listener, daemon name, external secret path, backup schedule, off-host target, and role enablement.
Keep personal deployment values in the private configuration source that already owns similar services.

The Home Manager module deliberately leaves the bearer token, SSH identity, known-host file, linger, and deletion policy outside the Nix store.
Linger is privileged host state and may require a system-level declaration or administrator action.

### Implementation without Nix

Install the same pinned release through the host's managed package or configuration system.
Do not rely on `kata update` or an unpinned mutable download.

| Platform | Release asset | SHA-256 |
| --- | --- | --- |
| Linux amd64 | `kata_0.14.3_linux_amd64.tar.gz` | `d569eeff70fb6fa9f67db3c51c43bb3a7adaaa0cd310274a4bd0a42ca2ff3ec0` |
| macOS arm64 | `kata_0.14.3_darwin_arm64.tar.gz` | `6f7b775a86401c0c7ddd780523d515f40de87e4e00fb2ad52943fcad7582344c` |

Verify the archive before installing it.
Other platforms are unqualified until they pass the complete acceptance suite.

Run this on every server and client:

```bash
kata version --json
```

The result must report `v0.14.3`, commit `410ee88`, and the expected operating system and architecture.

## Configure the server

### Data and non-secret configuration

Use the service account's default `KATA_HOME`, normally `~/.kata`, unless the host already owns a different durable location.
Protect the state as follows:

```text
~/.kata/                 0700
~/.kata/config.toml      0600
~/.kata/kata.db          0600
~/.kata/kata.db-wal      0600 when present
~/.kata/kata.db-shm      0600 when present
```

The non-secret server configuration is:

```toml
listen = "<private-ip>:<kata-port>"

[web]
public_origin = "http://<browser-hostname>:<kata-port>"
allowed_hosts = ["<browser-hostname>:<kata-port>"]
```

`public_origin` controls the browser session exchange, while `allowed_hosts` controls the accepted HTTP `Host` authority.
Keep both exact and do not add a wildcard.

### Secret boundary

Create at least 256 random bits of token entropy without printing the value.
Deliver the same token to clients through an authenticated out-of-band channel.

The recommended server secret file is a mode-`0600` regular file inside a mode-`0700` directory and contains only:

```text
KATA_AUTH_TOKEN=<high-entropy-token>
```

Keep the token out of Git, Nix store paths, TOML, process arguments, logs, chat, command output, general project environment files, and unrelated child processes.
Declare the non-secret `KATA_TRUST_PRIVATE_NETWORK=1` and `KATA_TELEMETRY_ENABLED=0` in the managed service.
Do not replace authentication with `allow_unauthenticated_private_network_writes` or `--insecure-readonly`.

### Managed user service

Run the daemon in the foreground under a managed user systemd unit equivalent to:

```ini
[Unit]
Description=Kata shared work-ledger daemon
After=network-online.target

[Service]
Type=simple
Environment=HOME=%h
Environment=KATA_HOME=%h/.kata
Environment=KATA_TRUST_PRIVATE_NETWORK=1
Environment=KATA_TELEMETRY_ENABLED=0
EnvironmentFile=%h/.config/kata/server.env
WorkingDirectory=%h
ExecStart=<kata-binary> daemon start --foreground --listen <private-ip>:<kata-port>
Restart=on-failure
RestartSec=5s
TimeoutStopSec=30s
UMask=0077
NoNewPrivileges=true
PrivateTmp=true

[Install]
WantedBy=default.target
```

Use the absolute managed binary path.
Enable the unit and enable linger for the service account so the user manager starts without an interactive login:

```bash
loginctl enable-linger <server-user>
loginctl show-user <server-user> -p Linger
```

Ask before enabling linger if the user did not identify this account as an always-on server.
A foreground process orphaned from an SSH session or running in `session-*.scope` is not a managed service.
The accepted daemon PID must belong to the loaded Kata unit and its service cgroup.

## Configure clients and workspaces

Every participating repository commits only its stable project binding:

```toml
# <workspace>/.kata.toml - tracked
version = 1

[project]
name = "<project-name>"
```

Use the same project name in every checkout and worktree that should share a ledger.
Inspect the changes from `kata init --project <project-name>` before asking to commit them.

### Recommended shared named daemon

Use one user-level named daemon when one account connects several workspaces to the same server.
Create an owner-only Kata client environment:

```text
~/.config/kata/                         0700
~/.config/kata/<daemon-name>.env        0600
```

```text
<token-env>=<same-static-token>
KATA_TRUST_PRIVATE_NETWORK=1
KATA_AUTHOR=<actor>
```

Do not set `KATA_SERVER` in this file because it takes precedence over the named catalog.
Do not combine Kata values with unrelated cloud, database, or application credentials.

Configure the owner-only client catalog without storing the token in TOML:

```toml
# ~/.kata/config.toml - mode 0600
active_daemon = "<daemon-name>"

[[daemon]]
name = "<daemon-name>"
url = "http://<private-ip>:<kata-port>"
token_env = "<token-env>"
```

On a machine that is both server and client, merge these catalog values with the server's `listen` and `[web]` values in the same owner-only `config.toml` instead of replacing either role's fields.
Use the literal private IP and do not enable `allow_insecure` for this target.
Load the Kata-only environment through the machine's secret launcher or add it exactly once to the existing workspace direnv configuration:

```bash
kata_env_file="${XDG_CONFIG_HOME:-$HOME/.config}/kata/<daemon-name>.env"
dotenv_if_exists "$kata_env_file"
```

The tracked workspace then needs no local token or routing file.

### Per-workspace alternative

Use a per-workspace target only when workspaces on the same account intentionally use different servers or a user-level catalog is unavailable.
Keep `.kata.local.toml` and `.env.kata` ignored and owner-only, route with the literal private IP, and keep the token only in `.env.kata`.

```toml
# <workspace>/.kata.local.toml - ignored
version = 1

[server]
url = "http://<private-ip>:<kata-port>"
```

```text
# <workspace>/.env.kata - ignored, mode 0600
KATA_AUTH_TOKEN=<same-static-token>
KATA_TRUST_PRIVATE_NETWORK=1
KATA_AUTHOR=<actor>
```

Preserve the rest of the workspace's `.envrc` and `.gitignore`, add `dotenv_if_exists .env.kata` to `.envrc`, and ignore both `.kata.local.toml` and `.env.kata`.
Verify both files remain ignored and untracked before asking to commit the tracked workspace binding or environment loader.

Kata resolves a target in this order: explicit `--daemon`, `KATA_SERVER`, `.kata.local.toml`, user-level `active_daemon`, then local discovery or auto-start.
Audit higher-priority sources before diagnosing the named catalog.
A configured remote must fail closed when unavailable rather than silently starting or using a local daemon.

## Browser UI

The same daemon serves the UI at:

```text
http://<browser-hostname>:<kata-port>/kata
```

The login exchanges the bearer token for a tab-scoped in-memory session.
Never place the token in the URL or persistent browser storage.
If an agent controls the browser, obtain action-time confirmation before entering the token and prevent it from appearing in screenshots, logs, or tool output.
The user may perform login manually instead.

## Back up and qualify recovery

Do not copy `kata.db` alone while the daemon runs because committed writes may still live in the SQLite WAL.
Run an online JSONL export from a scheduled user service.

The backup implementation must:

1. set `umask 077` and create an owner-only timestamped local destination;
2. run outside every Kata workspace;
3. unset `KATA_AUTH_TOKEN` and `KATA_SERVER`;
4. use an empty temporary `KATA_HOME` and set `KATA_DSN` directly to the live database;
5. run `kata export --allow-running-daemon --output <snapshot>`;
6. verify that the snapshot is nonempty and mode `0600`; and
7. copy it to a distinct authenticated off-host location with an atomic final name and matching cryptographic checksum.

The backup service does not need the daemon token.
If using SSH, use batch mode, strict host-key checking, explicit runtime identity and known-host paths, and no inherited SSH agent or unrelated user SSH configuration.
Retry unpublished local snapshots after temporary off-host failures.

Enable a persistent timer at a recovery interval chosen by the owner.
Retention and remote deletion are consequential choices, so keep snapshots append-only until the user explicitly chooses and qualifies a pruning policy.

### Restore qualification

Exercise a backup before calling it recoverable:

1. Round-trip the off-host snapshot into disposable storage and compare checksums.
2. Set `umask 077` and an isolated `KATA_HOME`.
3. Run `kata import --input <snapshot> --target <fresh-db> --new-instance` without `--force`.
4. Confirm the restored database is mode `0600` and `PRAGMA quick_check` returns `ok`.
5. Compare project, issue, comment, relationship, distinct-label, and event counts exactly without printing ledger content.
6. Start the restored database on a unique loopback port, verify health and a known project, restart it, and repeat the checks.
7. Stop the isolated daemon and move only disposable qualification state to trash.

In `v0.14.3`, JSONL record classes use `.kind`, labels use `.data.label`, and restored logical labels are `count(distinct label)` from `issue_labels`.
Import creates a target database and is not an incremental merge.
A live database replacement is a separate destructive recovery action that requires exact authorization while every daemon using the target is stopped.

## Convert an existing deployment safely

Before replacing any live process:

1. Record the package version, process command, PID, cgroup, exact listener, health schemas, logical counts, current managed generation, and rollback command.
2. Take an online export and complete the isolated restore qualification.
3. Verify only the ownership and mode of the external secret file without printing its content.
4. Build or evaluate the ordinary managed configuration without activating it.
5. Obtain explicit action-time production-cutover authorization.

During cutover, reverify the exact old process, stop only that PID, wait for its listener to be released, and run the ordinary managed activation.
Do not replace the database.

If activation fails, stop the new unit, reactivate the recorded previous configuration, and restart the pinned foreground command against the unchanged database.
Restoring a backup over production requires separate authorization.

## Acceptance suite

Do not accept a successful package build, `kata daemon status`, a visible login page, or one successful client list as sufficient evidence.
Test installed artifacts and the active managed service.

### Structure and lifecycle

1. Confirm `kata version --json` reports `v0.14.3`, commit `410ee88`, and the expected platform on every machine.
2. Confirm `kata health --json` reports healthy status, database schema `25`, and API schema `0.10.0`.
3. Confirm the service is loaded, enabled, active, and owns the daemon PID and service cgroup.
4. Confirm linger is enabled and the daemon is the only process listening on the exact private address and port.
5. Confirm all state, configuration, token, and backup paths have their intended owner-only modes.
6. Inspect sanitized service logs and prove no token, unrelated credential, issue body, or comment content was logged.
7. Apply the managed setup twice and prove the second application creates no duplicates or drift.
8. Explicitly restart the service and verify a new managed PID, health, listener, integrity, and counts.
9. Kill only the verified service PID, wait for automatic recovery, and repeat the checks.
10. End the launching login or SSH session, reconnect, and prove the service remains available through linger.

Host reboot is the strongest boot-durability test and requires separate action-time authorization.
If it is not performed, report reboot durability as untested.

### Authentication and routing

1. From same-host and remote clients, verify protected commands succeed with the correct token and `KATA_TRUST_PRIVATE_NETWORK=1`.
2. Use a protected command such as `kata projects list --agent` to prove absent and deliberately wrong non-secret tokens fail.
3. Keep the correct token but remove the client trust opt-in and prove the client refuses to send it over private plaintext HTTP.
4. Verify each workspace's `.kata.toml` selects the intended project through the same daemon.
5. Verify the named daemon works once with `--daemon <daemon-name>` and then through `active_daemon` without the flag.
6. Configure a disposable unreachable remote and prove the client fails closed without local fallback.

`kata health` is public in `v0.14.3` and cannot prove authentication rejection.
Never print the real token while performing negative tests.

### Cross-client ledger behavior

Tell the user before this check because it creates a small durable closed qualification graph and comments.
From client A, create idempotent qualification issues that exercise parent, blocking, and related links.
From client B, observe the same records, append a non-sensitive comment, and verify client A sees it.
Inspect `.links` in structured output, verify the intended graph and readiness behavior, then close the qualification records in a valid order with substantive evidence.
Restart the managed service and verify the same records and counts remain.

For this pinned version, parent containment alone does not gate readiness, an explicit blocking edge does, and an open child prevents its parent from closing.

### Browser and recovery

Confirm a browser-style request with `Accept: text/html` loads the login page at the exact origin without host errors.
Token login, browser mutation, and fresh-tab session checks require action-time credential confirmation.

Run the installed backup service manually and complete the full off-host restore qualification against that new snapshot.
Verify the scheduled timer is enabled and active, and distinguish a manual service run from a naturally triggered timer execution.

## Minimal agent workflow after installation

At the start of work, run from the repository:

```bash
kata quickstart
kata whoami --agent
kata list --agent
```

Search before creating, claim one issue before working, keep the issue body as the current contract, and use comments for discoveries, decisions, evidence, and handoffs.
Use explicit blocking links for execution order and inspect `.links` after graph edits.
Close work only after fresh verification with an issue-specific message and test command.
The upstream [agent workflow](https://www.katatracker.com/workflows/agents/) contains the full command guidance.

## Important limits and common failures

- The pinned static token grants daemon-wide read/write access and does not make client-supplied actor strings authoritative.
- Remote-daemon mode has no project ACL or high availability.
- Private HTTP is acceptable only inside the trusted encrypted private network described here.
- The browser session is tab-scoped and in memory.
- `KATA_SERVER` and `.kata.local.toml` override `active_daemon` and commonly explain routing surprises.
- Token-bearing private HTTP requires `KATA_TRUST_PRIVATE_NETWORK=1` on the client as well as the server.
- A plaintext DNS hostname needs an insecure override in `v0.14.3`; the accepted CLI baseline avoids that by using the literal private IP.
- `allowed_hosts` can make the page visible while a wrong `public_origin` still breaks token exchange.
- A raw database copy can omit WAL state; use online export and qualified restore.
- Export must bypass workspace and named-daemon routing through an empty temporary `KATA_HOME` and explicit `KATA_DSN`.
- Import is replacement into a fresh target, not merge, and must use an isolated `KATA_HOME` during qualification.
- `umask 077` is required because import can otherwise create a mode-`0644` database.
- A timer definition does not prove that a scheduled run or off-host recovery has succeeded.
- A foreground process, transient unit, or successful build does not prove enabled service, login independence, declarative reapplication, or reboot durability.

Upgrading Kata, changing the authentication model, adding another human, exposing the service beyond the trusted private network, or replacing systemd requires a new design review and the complete acceptance suite.

## Evidence and remaining boundaries

The fresh setup exercise used this specification on an empty server/client deployment and completed the pinned artifact, private listener, authentication, routing, cross-client ledger, browser-page, managed-service, and backup/restore checks.
Independent reruns exposed and then validated fixes for import umask, protected authentication negatives, JSONL label counting, browser content negotiation, routing-neutral host-local export, and SSH configuration isolation.

The later production conversion used the repository's Nix implementation and qualified managed activation, explicit restart, forced-failure recovery, Home Manager reapplication, launching-session independence, an installed backup service, checksummed off-host storage, and isolated restored-daemon restart.
That production exercise was an in-place conversion, not the fresh-install test described above.

The production record did not establish host reboot, credential-bearing browser login, browser mutation, a naturally triggered timer run, automated pruning, or recurring restore execution.
Do not infer those results from the declarative configuration.

This public document intentionally contains no real hostname, private IP, user, token, project, repository, database path outside the service account, or private-network policy.
Deployment-specific values, external secret ownership, current status, and rollback evidence belong in a private overlay or operations record.

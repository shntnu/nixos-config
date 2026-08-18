# Share one Kata work ledger across coding agents and private machines

[Kata](https://www.katatracker.com/) is a lightweight issue tracker designed for coding-agent work.
This specification defines one durable Linux Kata server with a SQLite database, CLI clients on the same or other machines, and the built-in web UI over a trusted private network.
Repositories carry only a stable project binding and machine-local routing.
Issue state remains on the server, so agents on several machines see and update one work ledger.

This specification records a tested design for Kata `v0.14.3`, commit `410ee88`.
The reference investigation verified an existing Linux server from a macOS client, authentication failures, private-HTTP guardrails, workspace routing, the web login page, and a full cross-machine export/import/restart exercise in August 2026.
An isolated restored ledger then passed a Linux user-systemd qualification, including automatic failure recovery and survival of the launching SSH session.
The existing production daemon remained an unmanaged session process, and no host reboot was authorized.
The browser token exchange was deliberately not performed.
Two fresh agents independently reproduced the isolated server/client, service-lifecycle, cross-client ledger, and backup/restore contract after the first run's failures were incorporated.
Durable managed activation, reboot, and browser credential use remain explicit untested boundaries.

Primary version-sensitive references are the Kata [`v0.14.3` release](https://github.com/kenn-io/kata/releases/tag/v0.14.3), [remote-daemon guide](https://www.katatracker.com/operations/remote-daemon/), [configuration reference](https://www.katatracker.com/reference/configuration/), [agent workflow](https://www.katatracker.com/workflows/agents/), and [backup and restore guide](https://www.katatracker.com/operations/backup-restore/).

## Use this specification

Give a coding agent this document with an explicit role instruction.

To create the first shared server and connect a workspace on it, say:

> Set up the first shared Kata server and a same-machine client from this specification, preserve this host's managed configuration, and run the full acceptance test.

To connect another machine, say:

> Connect this machine and this repository as a client of my existing shared Kata server from this specification, and run the client acceptance test.

To set up both a new server and a separate client, identify the two machines and say:

> Set up these machines as the Kata server and client described by this specification, preserve each machine's managed configuration, and run the full acceptance test.

That instruction authorizes the ordinary installation and configuration changes described for the named role.
It does not authorize changing private-network ACLs or device identity, committing unrelated repository changes, entering a bearer token into a browser, rebooting a shared host, deleting ledger data, or publishing test results.
The agent must state the exact files, services, listener, workspace files, durable test records, and external copies it will create before it changes them.

## Architecture and invariants

The flow is:

```text
same-host CLI --------------------+
                                  |
remote CLI -> private overlay ----+-> literal private IP:7777
                                  |        -> one managed Kata daemon
browser -> exact private hostname +        -> one SQLite database
```

One always-on Linux host owns the database and runs the only daemon for this deployment.
Every CLI, including a CLI on the server, resolves its workspace to that daemon rather than starting an independent local ledger.
The final connection uses a literal stable private IP and does not depend on an interactive SSH tunnel.
The daemon binds that exact address, never `0.0.0.0`, `::`, or a public interface.

The baseline is a trusted single-operator deployment with one high-entropy static bearer token.
Both server and CLI clients explicitly opt in to bearer authentication over private plaintext HTTP with `KATA_TRUST_PRIVATE_NETWORK=1`.
Private-network encryption and access control are part of the security boundary.
Kata does not require or assign an overlay-network device tag; preserve the host's existing network identity and ACL policy unless the user separately authorizes a change.

The CLI uses the literal private IP so it does not need `KATA_ALLOW_INSECURE`.
The browser uses one exact private hostname configured as both the public origin and an allowed host.
Do not weaken either path merely to get a first health check.

Kata data is a live work ledger.
Git remains the durable record for code, reviewed documents, scientific outputs, and other repository artifacts.
An issue body describes the current contract or desired state, while comments preserve decisions, attempts, evidence, and handoffs in chronological order.

## Parameters to resolve before changing anything

Resolve and record these values without printing a secret:

- `<server-user>`: the unprivileged account that owns the daemon and database;
- `<private-ip>`: a stable literal RFC1918, CGNAT, link-local, or ULA address on the private network;
- `<browser-hostname>`: the exact private DNS name users will enter in the browser;
- `<kata-port>`: normally `7777`;
- `<kata-binary>`: the absolute path installed by the host's managed package system;
- `<project-name>`: a stable, non-secret project name shared by every checkout;
- `<workspace>`: the repository root on each client;
- `<actor>`: the stable actor identity used on that client, with the same handle for the same human across machines; and
- `<backup-destination>`: an owner-only location plus a distinct off-host destination.

Confirm that `<browser-hostname>` resolves to `<private-ip>` from each intended browser client.
Confirm that the private network routes between the clients and server and that `<private-ip>:<kata-port>` is unused.
Do not infer a device tag from a hostname, role, or prior configuration.

## Execution rules for the coding agent

- Read the whole specification before acting and determine whether this host is the server, a client, or both.
- Inspect the operating system, architecture, shell, service manager, existing configuration management, package source, private-network client, firewall, Kata installation, workspace files, and any running Kata process before changing them.
- Preserve the machine's configuration model.
  Update Nix, Home Manager, chezmoi, or another managed source instead of hand-editing its generated unit, package profile, shell file, or environment.
- Pin Kata `v0.14.3` at commit `410ee88` for this tested contract.
  A newer version requires the full acceptance suite and a review of its release notes and versioned CLI help.
- Verify the installed artifact with `kata version --json` on every server and client.
  `kata --version` is not the version command in `v0.14.3`.
- Keep the bearer token out of Git, Nix store paths, process arguments, logs, chat, command output, general project `.env` files, and unrelated child processes.
- Use a separate owner-only server environment file and a separate Kata-only client environment file or an operating-system secret mechanism.
  Never source a project environment containing unrelated cloud or application credentials into the Kata service.
- Preserve an existing live database and ledger.
  Before changing a live service, take an online JSONL export and qualify its restore in an isolated path.
- Do not call an installation durable until a managed service owns the running PID, user linger is enabled, the ordinary managed activation has succeeded, and restart and login-independence checks pass.
- Apply the managed setup twice and verify that the second application creates no duplicate service, environment, ignore, or agent-instruction entries.
- Treat workspace files intended for Git as pending until the user authorizes their commit and push.
  Report uncommitted managed or workspace changes rather than describing them as durable publication.
- Never run `kata delete`, `kata purge`, `kata projects purge`, `kata import --force`, or a destructive restore without explicit authorization for the exact target.
- Report every changed path, service name, package version and revision, secret-delivery method, listener, test result, retained test record, backup location, and untested boundary.

## Install the pinned artifact

Install the same Kata release on the Linux server and each CLI client through the machine's managed package source.
For Nix-managed machines, package Kata in the owning flake or Home Manager source and activate that source through its normal command.
For another package system, pin the release or immutable artifact in that system rather than relying on `kata update`.

The two exercised release assets and SHA-256 digests are:

| Platform | Asset | SHA-256 |
| --- | --- | --- |
| Linux amd64 | `kata_0.14.3_linux_amd64.tar.gz` | `d569eeff70fb6fa9f67db3c51c43bb3a7adaaa0cd310274a4bd0a42ca2ff3ec0` |
| macOS arm64 | `kata_0.14.3_darwin_arm64.tar.gz` | `6ae968301b696c905ad631cff20b544567815a27532ec2eb271d91cf24c12906` |

Verify the archive digest before packaging or installing it.
Treat every other operating-system and architecture artifact as unqualified until it passes this specification.

Verify all installed binaries:

```bash
kata version --json
```

The accepted reference reports `v0.14.3` and commit `410ee88`.
Confirm the operating-system and architecture fields as well.
A temporary profile install or local flake override can qualify the binary, but it is not the final deployment.

## Server configuration

### Data and non-secret configuration

Use the service account's default `KATA_HOME`, normally `~/.kata`, unless the host already declares a different durable path.
Make the directory owner-only and preserve the database in it:

```text
~/.kata/                 0700
~/.kata/config.toml      0600
~/.kata/kata.db          0600 preferred, and never reachable through a traversable public directory
```

Kata uses SQLite WAL mode, so `kata.db-wal` and `kata.db-shm` can exist while the daemon runs.
They belong to the same protected directory.

Set the server's non-secret configuration to the resolved values:

```toml
listen = "<private-ip>:<kata-port>"

[web]
public_origin = "http://<browser-hostname>:<kata-port>"
allowed_hosts = ["<browser-hostname>:<kata-port>"]
```

`public_origin` and `allowed_hosts` solve different checks.
The first declares the exact browser origin used during session exchange.
The second admits the exact HTTP `Host` authority.
Keep both narrow and do not add a wildcard.

### Static token and private-HTTP opt-in

Create a high-entropy token with at least 256 random bits without printing it.
Deliver the same token to clients through an existing secret manager or another authenticated out-of-band channel.

The service environment file contains only Kata service values:

```text
KATA_AUTH_TOKEN=<high-entropy-token>
KATA_TRUST_PRIVATE_NETWORK=1
KATA_TELEMETRY_ENABLED=0
```

Place it at an owner-only managed path such as `~/.config/kata/server.env` with mode `0600` and its parent directory mode `0700`.
Use a token alphabet that does not need shell quoting in an `EnvironmentFile`, such as lowercase hexadecimal.
Do not put the token directly in `config.toml` when the managed deployment has a proper runtime secret mechanism.

Do not enable `allow_unauthenticated_private_network_writes` or `--insecure-readonly` as a substitute for authentication.
Any device that reaches an unauthenticated writable listener can write and assert any actor.

### Managed user systemd service

Run the daemon in the foreground under a managed user systemd service.
The configuration source should generate the equivalent of:

```ini
[Unit]
Description=Kata shared work-ledger daemon
After=network-online.target

[Service]
Type=simple
Environment=HOME=%h
Environment=KATA_HOME=%h/.kata
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

Use the absolute managed binary path, not a mutable shell `PATH` lookup or a hard-coded transient package-store path copied from a temporary build.
The explicit listener and the matching config value make the intended bind unambiguous.
The retry policy lets the unit recover when the private overlay address appears after the user manager starts.

Enable linger for `<server-user>` so the user manager and service start without an interactive login:

```bash
loginctl enable-linger <server-user>
loginctl show-user <server-user> -p Linger
```

Enabling linger may require an administrator and changes system state outside the user's Home Manager profile.
Ask before doing it if the original setup instruction did not name this host as the always-on server.

Activate the ordinary managed configuration, enable and start the generated unit, and verify that the managed unit owns the live PID.
An orphaned process with parent PID 1 or a cgroup named `session-*.scope` is not proof of a service.
`systemctl --user status <pid>` must resolve to the intended loaded Kata unit rather than merely showing a process.

Do not leave a second ad hoc daemon running.
Before switching an existing unmanaged daemon, export and qualify the live database, stop only the old process, start the managed unit against the same database, and recheck health and record counts.

## Client and workspace configuration

Install the pinned CLI and the private-network client on every client machine.
Use the literal private IP for CLI routing:

```toml
# <workspace>/.kata.local.toml - ignored
version = 1

[server]
url = "http://<private-ip>:<kata-port>"
```

Do not set `allow_insecure` for this literal private-IP URL.
Do not use the browser hostname for a plaintext token-bearing CLI target.
Kata `v0.14.3` rejects bearer authentication to a non-loopback HTTP hostname unless the client separately weakens the target with `KATA_ALLOW_INSECURE=1` or `allow_insecure = true`.

Commit only the stable project binding:

```toml
# <workspace>/.kata.toml - tracked
version = 1

[project]
name = "<project-name>"
```

The project name must be identical in every checkout and worktree intended to share the ledger.
Run `kata init --project <project-name>` when creating it, then inspect its changes before committing.

For the reference direnv workflow, preserve every existing `.envrc` entry and add this line exactly once:

```bash
# <workspace>/.envrc - tracked
dotenv_if_exists .env.kata
```

Preserve the rest of `.gitignore`, then add these entries exactly once and protect the files:

```text
# <workspace>/.gitignore - tracked entries
.kata.local.toml
.env.kata
```

```text
# <workspace>/.env.kata - ignored, mode 0600
KATA_AUTH_TOKEN=<same-static-token>
KATA_TRUST_PRIVATE_NETWORK=1
KATA_AUTHOR=<actor>
```

This file must contain only Kata client values.
Do not combine it with AWS, cloud-provider, application, database, or other project credentials.
If the repository runs untrusted project processes, prefer a small managed wrapper or operating-system secret launcher that gives these variables only to the Kata process instead of exporting the token to the whole direnv environment.

Approve the `.envrc` through the client's normal direnv trust flow, then prove both local files are ignored and inspect the intended tracked files:

```bash
git check-ignore .kata.local.toml .env.kata
git status --short -- .kata.toml .envrc .gitignore .kata.local.toml .env.kata
```

After the user authorizes the repository commit, `git ls-files --error-unmatch .kata.toml .envrc .gitignore` must succeed, while the two local files remain untracked and ignored.

`KATA_SERVER` overrides `.kata.local.toml`.
Remove an accidental global `KATA_SERVER` before concluding that workspace routing is wrong.
A configured remote is authoritative: if it is unavailable, the command must fail instead of silently starting or using a local daemon.

## Browser UI

The same daemon serves the UI at its canonical route.
Open it with `kata ui` from a configured workspace or visit:

```text
http://<browser-hostname>:<kata-port>/kata
```

The exact hostname must match `[web].public_origin` and `[web].allowed_hosts`.
The login form exchanges the bearer token for a tab-scoped in-memory browser session; the token must never be placed in the URL or persistent browser storage.
Opening a fresh tab can require a new login.

Entering the bearer token is a credential transmission.
If a coding agent controls the browser, it must obtain action-time confirmation immediately before entering and submitting the token, avoid exposing the value in tool output or logs, and clear any temporary clipboard afterward.
The user can instead perform the login manually.

This HTTP design assumes an encrypted private overlay and trusted members.
Use a same-origin HTTPS reverse proxy and set `public_origin` to its exact HTTPS origin when the private network is not a sufficient bearer-token transport boundary.

## Agent work-ledger contract

At the beginning of every coding-agent session, run from the workspace:

```bash
kata quickstart
kata whoami --agent
kata list --agent
```

Use `--agent` for ordinary human-readable agent operations and `--json` for scripts that require structured fields.
`kata list --agent` is flat output and does not prove a parent-child hierarchy.

Search before creating:

```bash
kata search "<terms>" --agent
```

Search in `v0.14.3` can be lexical and can miss a relevant issue whose wording differs.
Fall back to `kata list --status all --agent` and inspect likely matches with `kata show <ref> --agent` before creating a new issue.
Use an idempotency key for a retryable create.

Claim one existing issue before starting work:

```bash
kata claim <ref> --agent
```

A repeated claim by the same owner is an idempotent no-change result.
A claim already held by another actor is a coordination signal, not a reason to force ownership.

Keep the body as the current problem statement, desired state, constraints, and acceptance contract.
Append discoveries, failed attempts, decisions, evidence, and remaining work as comments, especially before compaction, a long pause, or a handoff.

Use relationships deliberately:

- `parent` and child structure express containment or work breakdown;
- `blocks` and `blocked_by` express execution order; and
- `related` expresses useful context without ordering.

In `v0.14.3`, a parent link alone does not remove either record from `kata ready`, so use an explicit blocking edge for execution order.
Kata does refuse to close a parent while one of its children remains open; close or rescope the children first.

Create or change those relationships explicitly:

```bash
kata edit <child> --parent <parent> --agent
kata edit <predecessor> --blocks <successor> --agent
kata edit <issue-a> --related <issue-b> --agent
```

After relationship edits, inspect every affected issue and audit the complete graph.
A successful single link mutation does not prove that directions, stale edges, or duplicates are correct.
For JSON automation, treat the `.links` collection as authoritative and handle convenience relationship fields as nullable.

`kata list --all` means all non-archived projects.
`kata list --status all` means open and closed statuses in the selected project.
Do not confuse those scopes.

Close only after fresh verification and attach issue-specific evidence:

```bash
kata close <ref> --done \
  --message "<what was completed and freshly verified>" \
  --test "<verification command>" \
  --agent
```

If work remains, leave the issue open, label it `needs-review`, and add a substantive comment stating what was attempted and what remains.
Never close merely because an agent attempted the task or a command returned success.

## Backup, off-host copy, and restore

### Scheduled online export

Do not copy `kata.db` alone while the daemon is running.
Recent committed writes may exist only in the SQLite WAL file.

Create a managed backup script or equivalent service that:

1. sets `umask 077`;
2. runs outside any Kata workspace so `.kata.local.toml` cannot select a remote;
3. loads only the Kata server environment file;
4. writes a timestamped full JSONL export with `kata export --allow-running-daemon --output <path>`;
5. verifies that the new file is nonempty and owner-only; and
6. transfers it to a distinct authenticated off-host destination without logging the token or export contents.

Run it from a user systemd timer at an interval appropriate to the ledger's recovery-point objective.
The backup unit should use the same managed Kata binary and `KATA_HOME` as the daemon.
Do not set `KATA_SERVER` in it.
`kata export` is host-local and refuses a configured remote target.

Retention and off-host deletion policy are consequential choices.
Agree them with the user rather than silently removing old snapshots.

### Isolated restore qualification

Exercise every backup before calling it recoverable:

1. Copy one export to a disposable directory on another machine and compare cryptographic checksums.
2. Set `umask 077` and `KATA_HOME=<isolated-home>`, then run `kata import --input <export> --target <fresh-db> --new-instance`.
3. Run SQLite `PRAGMA quick_check` against the restored database.
4. Confirm that the restored database is owner-only, correcting its mode before serving if the platform ignored the requested umask.
5. Compare project, issue, comment, relationship, label, and event counts between the export and restored database without printing private content.
   JSONL record classes are in the `kind` field in `v0.14.3`.
   JSONL label records store the value at `.data.label`.
   Count restored logical labels as distinct values of `issue_labels.label`; there is no separate `labels` table.
6. Start the restored database under an isolated Kata daemon on a unique loopback port with a temporary `KATA_HOME`.
7. Verify `kata health --json`, list a known project, restart that isolated daemon, and verify health and the same records again.
8. Stop the isolated daemon before moving the disposable directory to trash.

`kata import` creates a database and is not a merge operation.
The target must not exist unless `--force` is passed, and this specification never authorizes `--force` against live data.
Use `--new-instance` for an isolated qualification copy.
For an actual disaster-recovery replacement, preserve the source instance identity and follow the pinned version's restore procedure while every daemon using the target is stopped.

## Acceptance tests

Do not accept a successful package build, `kata daemon status`, a visible login page, or one client list as sufficient proof.
Run the checks against installed artifacts and the active managed service.

### Structural and lifecycle checks

1. Record `kata version --json` on the server and every client and confirm `v0.14.3`, commit `410ee88`, and the expected platform.
2. Run `kata health --json` through the configured server and confirm healthy status, database schema `25`, and API schema `0.10.0`.
3. Confirm the service is loaded, enabled, active, and owns the daemon PID and cgroup.
4. Confirm `loginctl show-user <server-user> -p Linger` reports `yes`.
5. Confirm the daemon listens only on `<private-ip>:<kata-port>`, not a wildcard, loopback-only address, public address, or second stale listener.
6. Confirm `~/.kata`, the token environment files, config, database, and backup files have the intended ownership and restrictive modes.
7. Inspect sanitized service logs and prove that no bearer token, unrelated environment credential, issue body, or comment content was logged.
8. Apply the managed setup a second time and prove that it creates no duplicate unit, hook, environment, ignore, or instruction entry.

`kata daemon status` can report a stopped state with a successful process exit, so parse its structured result and use `kata health --json` for reachability.
A transient unit can qualify foreground execution, restart policy, and survival of its launching session, but it cannot prove enabled state, ordinary managed activation, declarative reapplication, or boot durability.

### Authentication and routing checks

From both a same-host workspace and a separate client:

1. With the correct token and client-side `KATA_TRUST_PRIVATE_NETWORK=1`, run `kata health --json` and `kata projects list --agent`.
2. With the token removed, prove the protected `kata projects list --agent` request fails.
3. With a deliberately wrong non-secret token, prove the protected `kata projects list --agent` request fails.
4. With the correct token still present but `KATA_TRUST_PRIVATE_NETWORK` removed, prove the client refuses to send the bearer token over private plaintext HTTP before the request succeeds.
5. In a disposable workspace, configure an unreachable remote private address and prove the command fails with daemon-unavailable behavior rather than using or starting a local daemon.
6. Confirm no client config uses a plaintext hostname plus `allow_insecure` in the accepted baseline.

Do not print the real token while constructing the negative tests.
`kata health` is intentionally public in `v0.14.3`, so it can stay healthy without a token and cannot prove authentication rejection.

### Cross-client ledger check

Tell the user that this check will add a small durable closed qualification graph and comments to the selected project before running it.
From client A, create a qualification parent and the minimum child records needed to exercise parent, ordering, and related edges, using idempotency keys, then claim the active record.
From client B, show the same records, append a distinctive non-sensitive comment, and verify client A sees that comment.
Inspect every affected issue and verify the complete graph through `.links` in JSON.
Verify that parent containment alone leaves the records ready, an explicit blocking edge gates its target, and an open child prevents its parent from closing.
Close every qualification record in a valid order only after the checks pass, with substantive messages and explicit test evidence.
Verify both clients see the same final state.

Restart the managed server with `systemctl --user restart`, wait for health, and verify that the qualification records and project counts survived and that the new daemon PID still belongs to the managed unit.
End the interactive SSH or login session, reconnect from a client, and prove health and ledger access continue because linger is enabled.

A reboot is the strongest boot-durability test, but it is a disruptive host action.
Obtain explicit action-time authorization, reboot the server, and then repeat health, service-ownership, listener, and sentinel checks.
If reboot is not authorized, report boot durability as untested rather than inferring it from `WantedBy` and linger.

### Browser check

1. Open `http://<browser-hostname>:<kata-port>/kata` in a browser and confirm the Kata login page loads without host or origin errors.
   A command-line probe must send `Accept: text/html`; a raw request without browser-style content negotiation can return 404 even when the UI works.
2. After explicit action-time credential confirmation, authenticate with the correct token or ask the user to do so manually.
3. Verify the selected project, issue list, issue detail, comments, and relationships agree with the CLI.
4. Make one harmless browser mutation authorized by the user and confirm it from a CLI client.
5. Open a fresh tab and confirm the session behavior matches the documented tab-scoped in-memory design.

If the login page appears but token exchange fails with `origin_forbidden`, do not call the token wrong until `[web].public_origin` is checked.
If the request fails with `host_invalid`, check the exact authority in `[web].allowed_hosts`.

### Backup and restore check

Run the scheduled backup unit manually, copy the resulting export off-host, compare checksums, import it as a new isolated instance, run `PRAGMA quick_check`, compare all logical record-type counts, start and restart the isolated daemon, and verify the same project from its loopback client.
Do not point any qualification daemon at the live database or listener.
Move only disposable qualification artifacts to trash after the checks pass, and report every retained path.

## Failure modes this specification guards against

- A package in a profile and a foreground daemon in an SSH session can work for days without being boot-durable.
  Require a loaded managed unit, an owned cgroup, linger, restart, logout, and an authorized reboot check.
- A client configured for a remote daemon does not fall back locally when the tunnel or daemon disappears.
  Use the stable direct private path and treat daemon-unavailable as a real failure.
- `KATA_TRUST_PRIVATE_NETWORK=1` is required on clients that attach a bearer token to private plaintext HTTP as well as on the server.
- A plaintext DNS hostname is rejected for bearer authentication unless `allow_insecure` weakens that client target.
  Keep CLI routing on the literal private IP.
- `[web].allowed_hosts` alone can make the login page visible while the token exchange fails with `origin_forbidden`.
  Configure the exact `public_origin` too.
- An unexpected browser hostname can fail as `host_invalid` before token authentication.
- Sourcing a general project `.env` into the daemon can leak unrelated cloud credentials into a long-lived service.
  Use separate Kata-only environment files.
- A live `kata.db` file is not a complete backup when WAL data exists.
  Use host-local JSONL export and qualify restore.
- A remote workspace target makes `kata export` fail because export is intentionally host-local.
  Run the backup service from outside a workspace with no `KATA_SERVER`.
- Import is replacement into a fresh target, not incremental merge.
- On a host with another active Kata daemon, `v0.14.3` can reject an otherwise fresh explicit import target unless the qualification also sets an isolated `KATA_HOME`.
- On macOS, import can create a mode-0644 database under the caller's default umask.
  Set `umask 077`, verify the resulting mode, and harden the file before starting the restored daemon.
- Static-token authentication controls access but does not make actor strings authoritative.
- Lexical search can miss an issue, flat list output can hide hierarchy, and one successful relationship edit can conceal a wrong graph.
  Fall back to list/show and audit `.links` after graph changes.
- The `v0.14.3` `--parent` help text says the parent must finish before the child starts, but two disposable tests showed that parent containment alone does not gate `ready`.
  Treat the tested behavior as authoritative for this pinned version, use explicit blocking edges for execution order, and retain the open-child parent-close check.
- `--all` selects projects while `--status all` selects statuses.
- Convenience relationship fields in JSON can be null.
  Null-safe scripts should use `.links` as the authoritative edge collection.

## Known limits

This specification is pinned to Kata `v0.14.3` and a Linux systemd user service.
Other Kata versions, operating systems, and service managers require the full acceptance suite.

The baseline static token is daemon-wide read/write access.
Kata remote-daemon mode has no project ACL or role model, and a static-token client can supply an actor string.
For a second human, independent revocation, or trusted attribution, create DB-backed identity tokens and enable `require_token_identity = true` using the pinned remote-daemon procedure, then rerun every authentication, CLI, browser, backup, and restore test.

Plain HTTP is acceptable here only because the private overlay encrypts transport and its membership is trusted.
It is not a public or multi-tenant deployment.
Use HTTPS or a separately designed authenticated proxy when that boundary is insufficient.

SQLite gives one authoritative server, not high availability.
Clients cannot work against this ledger while the host, private network, or daemon is unavailable.
The JSONL export and off-host copy provide recovery, not live failover.

The built-in browser session is tab-scoped and in memory.
This specification does not claim that a previously authenticated tab survives a daemon restart or browser restart.

## Scope and boundaries

This document does not publish a real hostname, private IP, token, user, repository, project, issue identifier, database path outside the service account, or private-network policy.
It does not authorize changing a network ACL, assigning a device tag, publishing a port, sharing a token in chat, deleting ledger data, or pushing repository changes.
It defines the behavior and acceptance contract while requiring each implementation to preserve the host's existing managed configuration.

## Test evidence

The investigation and two independent fresh-agent runs took place on August 17-18, 2026.
The test environment was one NixOS Linux amd64 user-systemd server and one Nix-managed macOS arm64 client on an encrypted private overlay, both running Kata `v0.14.3` commit `410ee88`.
Each fresh agent received only this specification, a server/client role instruction, disposable roots, a unique private port and project name, and the production safety boundary.
The tests used newly generated dummy credentials, isolated databases, transient units, and disposable workspaces.

The reference investigation established the current deployment and the failures that shaped the first draft:

- one shared server database was reachable from both machines;
- correct, absent, wrong, and missing-client-trust authentication paths behaved as described;
- a configured unavailable remote failed closed instead of creating a local ledger;
- the browser login page rendered through the exact hostname, while credential-bearing login was deliberately skipped;
- an online JSONL export copied off-host with an identical checksum, restored with exact logical counts and `PRAGMA quick_check=ok`, served from an isolated loopback daemon, and survived restart;
- an isolated user-systemd service automatically recovered from process failure and survived the SSH session that launched it; and
- disposable graph tests proved the parent, blocking, related, readiness, and parent-close behavior recorded above.

The first fresh-agent run reproduced both release-asset hashes, server and client health, literal-address binding, permissions, protected authentication, client trust refusal, fail-closed routing, idempotent workspace initialization, cross-client comments and graph state, crash recovery, explicit service restart, SSH-session independence, browser-style HTML and host rejection, online backup, off-host checksum, exact restore counts, database integrity, and restored-daemon restart.
It exposed four missing instructions: import inherited a permissive macOS umask, authentication negatives did not name a protected command, JSONL and logical-label counting were underspecified, and a raw HTTP request did not negotiate HTML.

After those instructions were revised, a second fresh agent reran the contract from a new empty server and client state.
It completed without an acceptance failure.
In particular, import with `umask 077` produced a mode-0600 database without manual repair; every JSONL record had a string `kind`; `.data.label` matched `count(distinct label)` from `issue_labels`; protected absent and wrong token requests failed; the browser-style request returned HTML; all graph, restart, restore, and cleanup checks passed; and the production daemon's PID, start time, listener, database path, and unmanaged service state stayed unchanged.

The fresh tests did not exercise a previously unconfigured host's managed package installation, an enabled persistent unit, ordinary Nix or Home Manager activation and reapplication, a zero-login-session state, host reboot, durable backup scheduling or retention, durable off-host storage, firewall or overlay ACL changes, production service conversion, browser token exchange, browser mutation, or tab-session behavior.
Those boundaries remain untested and must not be inferred from the transient-service and HTML-probe results.

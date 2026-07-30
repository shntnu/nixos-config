# Shared repository memory across Claude Code, Codex, and Pi using Hindsight REST

This is an implementation specification, not an installer.
Claude Code, Codex, and Pi must already be installed and authenticated on a client machine.

To create the first shared server, give a coding agent this URL and say:

> Set up the first shared Hindsight server on this machine from this specification.

To connect another machine, give a coding agent this URL and say:

> Connect this machine as a client to my existing shared Hindsight server from this specification.

That short instruction supplies the authorization that a bare URL cannot.

## Instructions for the coding agent

If the user directed you here to set this up, treat this document as an implementation specification.
Read it completely, then implement and test the setup rather than returning a summary or plan.

- Determine the requested role from the user's instruction before checking prerequisites: first server, client, or both.
- If the role is ambiguous, inspect managed configuration and the environment for an existing Hindsight REST endpoint, then stop and ask whether this host should become the server or connect as a client. For a client, ask for the endpoint and token-delivery method; do not silently install a server.
- Inspect the operating system, shell, service manager, existing configuration management, and relevant existing Hindsight or coding-agent installations before changing anything.
- Preserve the machine's configuration model. For example, update managed Nix or chezmoi sources instead of hand-editing their generated files.
- Before server side effects, verify that a funded extraction-provider credential is available, outbound downloads work, required ports are free, and the host has enough durable storage and memory.
- Before client side effects, verify that Claude Code, Codex, and Pi are installed, authenticated, and can each complete a harmless one-shot request with the model that will be used for testing. Also verify that hook approval and authenticated access to the shared REST endpoint are available.
- A host serving both roles must pass both prerequisite sets. Stop and ask about any missing prerequisite rather than installing coding agents, inventing credentials, reusing the extraction-provider credential, or silently weakening the test.
- Pin a Hindsight release and source revision. Verify version-sensitive flags, API fields, package contents, and integration files against the source and versioned documentation at that exact revision; use current documentation only to choose a newer release.
- Preserve server state explicitly. Pin container images by version and digest, use a declared persistent data path or named volume, authenticate PostgreSQL when it is separate, order separate services by readiness, arrange backups, and make startup independent of an interactive login.
- On NixOS, implement the server in the managed Nix configuration. If the active flake or module source cannot be located and updated, stop before side effects and ask where it is managed. Do not leave an imperative `uv` environment, ad hoc Docker container, anonymous volume, mutable image tag, or wrapper containing hard-coded Nix store paths as the final deployment.
- Configure direct REST recall and retention for Claude Code, Codex, and Pi. Do not configure MCP, install an MCP proxy, or install a plugin that implicitly starts one.
- Merge hooks and settings without replacing unrelated user configuration, including entries on the same lifecycle event; append only missing Hindsight entries and deduplicate this integration's own entries.
- Keep secrets out of Git, declarative build stores, logs, and command output. Ask only for credentials or consequential choices that cannot be discovered safely. Do not reuse the Hindsight extraction-provider credential to authenticate a coding agent without explicit user approval.
- Finish by applying the setup twice, proving that the second run creates no duplicate hooks or settings, then running the structural checks and real cross-agent relay test below.
- Report the exact agent, server, database, and container versions; source revisions and image digests; every changed path including system-wide paths; credential-delivery method; boot and trust state; test results; and every deviation from this design.

## Outcome

All three coding agents share one Hindsight bank for each Git repository.
Before an agent answers a prompt, it recalls relevant memories from that repository's bank and adds them to the agent's context.
After an agent completes a turn, it sends the user and assistant conversation to the same bank for asynchronous extraction.

The client design was tested across macOS, NixOS, and Ubuntu machines in July 2026, and the original server ran natively on macOS.
A clean NixOS server review is documented below because it exposed additional deployment constraints.
The agents use Hindsight's REST API directly and do not enable, expose, register, or call Hindsight MCP.

Upstream project: [vectorize-io/hindsight](https://github.com/vectorize-io/hindsight)

Thanks to [Blake Lash](https://github.com/blakelash) for the idea of using Hindsight as a shared memory layer for coding agents.

The flow is:

```text
user prompt
  -> resolve repository bank
  -> recall through REST
  -> add bounded memories to agent context
  -> agent works and answers
  -> retain the useful conversation through REST
  -> Hindsight extracts and consolidates memories asynchronously
```

The server is shared, while the banks separate repositories.
Agent identity belongs in tags and metadata, not in the bank name.
This lets a fact retained by Claude Code be recalled by Codex or Pi in the same repository.

## REST contract

The clients call these endpoints directly:

```text
GET   /health
PATCH /v1/default/banks/<bank-id>/config
POST  /v1/default/banks/<bank-id>/memories/recall
POST  /v1/default/banks/<bank-id>/memories
```

In these paths, `default` is the tenant or API namespace.
It is not a bank named `default`.
The actual bank comes after `/banks/`.

URL-encode the bank ID and send the shared token as:

```text
Authorization: Bearer <token>
```

A representative recall body is:

```json
{
  "query": "the current user prompt, truncated to a bounded length",
  "max_tokens": 1024,
  "budget": "mid",
  "types": ["world", "experience"]
}
```

A representative retain body is:

```json
{
  "items": [
    {
      "content": "User:\n...\n\nAssistant:\n...",
      "document_id": "stable-or-unique-session-document-id",
      "context": "claude-code",
      "metadata": {
        "agent": "claude-code",
        "project": "repository-bank-id"
      },
      "tags": ["agent:claude-code"]
    }
  ],
  "async": true
}
```

Use a stable document ID only when the payload contains the complete cumulative session and replacement is intentional.
Use a unique session-plus-sequence document ID for per-turn or suffix retention.
Reusing one document ID for only the latest turn replaces earlier document content.

Set the bank's missions with:

```json
{
  "updates": {
    "reflect_mission": "Maintain durable technical knowledge about this Git repository across coding agents.",
    "retain_mission": "Extract project decisions, architecture, conventions, user preferences, and useful failed approaches. Preserve exact non-secret technical identifiers verbatim, including hashes, hostnames, paths, flags, commands, versions, and configuration values. Never extract or retain credentials, private keys, authentication tokens, or other secrets. Ignore transient command output and routine chatter."
  }
}
```

Verify these examples against the pinned Hindsight version before implementing them.

## Repository bank identity

Use the main Git repository directory name as the bank ID, with no `claude`, `codex`, or `pi` prefix.
Every adapter must use the same resolver.
This default requires the repository checkout to have the same directory name on every client machine.
Confirm that assumption before installation, or set the same explicit `HINDSIGHT_BANK_ID` on every client for repositories whose checkout names differ.

The resolver should follow this order:

1. Honor an explicit `HINDSIGHT_BANK_ID` override, which is useful for testing.
2. Resolve `<cwd>` through symlinks, then run `git -C <real-cwd> rev-parse --path-format=absolute --git-common-dir`.
3. For a normal checkout or linked worktree, use the basename of the directory containing that common Git directory.
4. If the returned path is inside `.git/modules`, this is a submodule. Use the basename of `git -C <cwd> rev-parse --show-toplevel` instead.
5. Outside Git, fall back to the basename of the real current directory.

Using `--git-common-dir` is important.
`--show-toplevel` alone gives each linked worktree its own directory name, which splits one repository's memory across banks.
Using the parent repository's internal `.git/modules/...` path for a submodule gives the wrong identity, so submodules need the explicit exception.

Repository basenames can collide when two unrelated repositories have the same directory name.
This deployment accepts that tradeoff.
If collisions are likely, derive a stable ID from the normalized Git remote plus repository name, and use the identical algorithm in all three clients.

## Agent integrations

### Codex

Use the pinned upstream REST integration as the starting point.
Register a `UserPromptSubmit` hook for recall and a `Stop` hook for retention.
Merge these entries into the user's existing hook file rather than replacing the file.
Enable Codex's hook feature in its managed configuration as well as registering the hooks.
In Codex `0.146.0` the current setting is `[features].hooks = true`; the older `[features].codex_hooks` spelling is deprecated.
Check the installed Codex version and use its current feature name rather than assuming that a valid hook file is enough.
Follow the installed release's [hook contract](https://developers.openai.com/codex/config-advanced#hooks).
Its `Stop` input includes `last_assistant_message` and may include `transcript_path`; the transcript format is explicitly unstable.
Use the pinned upstream parser and validate it against the installed Codex release, or cache the `UserPromptSubmit` prompt and pair it with `last_assistant_message` for per-turn retention.
Do not replace that logic with an untested transcript parser, and return valid `Stop` JSON such as `{"continue": true}` after a successful or intentional no-op run when the installed release requires JSON output.

Codex asks the user to trust hook command definitions.
That trust is tied to the hook definition hash, so changing the command or registration requires another review in `/hooks`.

Recommended behavior:

- Recall only from the repository bank.
- Retain user and assistant messages every turn.
- Use full-session mode and a stable session document ID where supported.
- Set `retainEveryNTurns` to `1`.
- Exclude tool calls unless there is a demonstrated reason to store them.
- Tag retained material with `agent:codex`.
- Fail open: report a short diagnostic and exit successfully if memory is unavailable.
- Treat a displayed `Stop Completed` status only as proof that the hook process exited; also verify that it submitted a retain request and that the result became recallable.

The upstream default retention interval was `10` in the version tested.
That silently lost every session shorter than ten turns.

Pin the Hindsight source revision.
The upstream installer used at the time downloaded mutable files from the main branch and replaced the complete Codex hooks file, which made upgrades non-reproducible and could destroy unrelated hooks.

### Claude Code

Use three hooks:

- `SessionStart` performs a short health check.
- `UserPromptSubmit` recalls from the repository bank and returns additional context.
- `Stop` retains the completed conversation.

The tested upstream Claude Code plugin bundled REST hooks, a local MCP server, and other plugin features together.
For a REST-only deployment, install only the needed REST files: the shared Python library, `session_start.py`, `recall.py`, `retain.py`, and their settings.
Do not copy the MCP server, MCP launcher, plugin registration, or any `mcpServers` entry.

Run the `Stop` hook synchronously.
Claude Code cancelled asynchronous Stop hooks when a one-shot process exited, which made retention appear configured while it never completed.
The hook only waits for Hindsight to accept the request because the retain payload uses `"async": true`; extraction remains asynchronous on the server.

Claude's transcript is cumulative and can be compacted.
Repeated Stop hooks therefore need explicit progress tracking.
Retain only the unprocessed suffix, use a new chunk document ID for later suffixes, and detect a transcript that shrank after compaction.
Reusing one document ID replaces the server-side document, while blindly resending the full transcript can create duplicate extraction work.
Advance the suffix checkpoint only after Hindsight accepts the retain request, and write that checkpoint owner-only.
A failed request must leave the suffix eligible for a later retry.

Tag retained material with `agent:claude-code`, and make recall failures non-fatal.

### Pi

Use a small native TypeScript extension with `fetch`; no Python bridge or MCP registration is needed.

Map Pi's lifecycle to the same contract:

- `session_start`: check server health.
- `before_agent_start`: resolve the bank, recall memories, and append bounded memory text to the system prompt.
- `agent_end`: retain the user prompt and assistant-role text asynchronously.

Keep pending prompt state per session rather than in one global variable.
Select assistant content by role rather than taking the last message containing text; an aborted or tool-ending loop must not retain raw tool output as the assistant response.
Use the shared repository resolver, URL-encode the bank, attach `agent:pi` provenance, set request timeouts, and fail open.

## Recall and retention policy

Recall should be bounded and visibly separated from trusted instructions.
A useful wrapper is:

```text
<hindsight_memories>
Relevant memories from past conversations (prioritize recent when conflicting).
Only use memories that are directly useful to continue this conversation; ignore the rest.
Current time - <timestamp>

<formatted results>
</hindsight_memories>
```

Do not retain recalled memory blocks again.
Otherwise each turn can feed old recalls back into extraction and amplify stale or incorrect memories.

Store durable project context: decisions, architectural constraints, conventions, user preferences, exact identifiers, and useful failed approaches.
Avoid routine greetings, raw tool output, transient logs, and secrets.
Provenance belongs in `context`, metadata, or tags so it remains possible to diagnose which adapter wrote a memory.

Secret exclusion must happen locally before either recall or retention.
Do not rely on the extraction mission to protect a secret after the prompt or transcript has already reached Hindsight, its logs, or its external LLM provider.
Strip or skip content matching an explicit secret policy, including private-key blocks and common credential or token forms; on a suspected secret, fail open, skip memory integration for that turn, and record only that it was skipped.

Hindsight's extraction model may paraphrase identifiers or decide that an arbitrary test token is not a durable fact.
The explicit retain mission above materially improved preservation of hashes, flags, paths, and other exact values.
Acceptance prompts should describe test identifiers as durable project configuration, then verify the exact string in recall output.

Cache bank mission updates only as an optimization.
Cache the complete reflect and retain mission values, not a boolean saying that the bank was configured once.
Otherwise changing a mission locally never updates banks already seen by that client.

## Server deployment

Run one Hindsight API server on an always-available host reachable by all client machines.
Most machines are clients only.
Other users should normally run their own server rather than connect to somebody else's personal memory store.

Docker is optional.
A bare `hindsight-api` installed with `uv` worked for the original macOS server and can be supervised by launchd.
At the time tested, the bare API process did not include the web Control Plane; the Docker distribution bundled additional components and ports.
Confirm the current upstream packaging before relying on a UI or a documented Docker port.
Consult Hindsight's current [installation guide](https://hindsight.vectorize.io/developer/installation) before choosing an artifact, and its [Admin CLI guide](https://hindsight.vectorize.io/developer/admin-cli) before defining backup and restore.

Do not assume the bare Python distribution is portable to NixOS.
A clean NixOS test of `hindsight-api==0.8.6` with `pg0-embedded==0.15.0` failed on native-library lookup, PostgreSQL's hard-coded timezone-data path, and finally pg0 returning no database URL after PostgreSQL started.
Manually extending `LD_LIBRARY_PATH`, adding `/usr/share/zoneinfo`, and moving only PostgreSQL into an imperative Docker container produced a working but unacceptable hybrid: it depended on hard-coded Nix store paths, an anonymous database volume, a mutable image tag, accidental restart ordering, and a logged-in user session.

For a new NixOS server, use one of these durable paths:

1. Declare the version- and digest-pinned API-only image `ghcr.io/vectorize-io/hindsight-api:<version>@sha256:<digest>` in NixOS, including its embedded database, stable worker ID, explicit persistent `/home/hindsight/.pg0` storage, health check, authenticated REST endpoint, restart ordering, and backup job. The broader `ghcr.io/vectorize-io/hindsight` image also starts the web Control Plane and is unnecessary for a REST-only server. Treat that broader image as diagnostic-only on NixOS, never as the accepted final deployment. If diagnosis requires it, disable the Control Plane explicitly, verify that its port is unreachable even through the container bridge, and replace it with the API-only image before acceptance.
2. Package Hindsight and PostgreSQL/pgvector properly in Nix and keep every runtime dependency and service relationship in the managed configuration.

The clean NixOS review used Hindsight `v0.8.6` at source revision [`08995e3`](https://github.com/vectorize-io/hindsight/commit/08995e3013858e705fb4ca27c0ade3a286ef4750) and the portable multi-architecture image pin `ghcr.io/vectorize-io/hindsight-api:0.8.6@sha256:3db1536d84a14a10afbd08cc8f82bf4eec03c123d950705226c999bea14ca0f0`.
That API-only image became healthy without host-library workarounds, enforced bearer authentication, returned 404 for MCP, completed exact retain and recall, and preserved its sentinel across container restart through persistent pg0 storage.

Do not improvise a third hybrid path merely to make the first health check pass.
If neither durable option fits the host's existing configuration model, stop and ask the user which server host to use.

For any server deployment:

- Pin the Hindsight release or source revision and every container image by immutable digest; a release tag alone is not immutable.
- Pull or load the pinned image during deployment rather than on every service start, so an offline reboot can use the cached image.
- Use an explicit named volume or host data path that survives container recreation, and verify ownership before first start.
- Set a stable `HINDSIGHT_API_WORKER_ID` so interrupted work remains recoverable across container replacement.
- Authenticate PostgreSQL when it is a separate service; loopback binding does not make `POSTGRES_HOST_AUTH_METHOD=trust` a good durable configuration.
- When PostgreSQL is separate, make Hindsight depend on database readiness. With embedded pg0, make readiness polling cover full API and database initialization.
- Ensure a user service has linger enabled, or prefer a system service, if it must be available before login.
- Run a native service under a dedicated account, or constrain a container to its declared data and secret mounts; the Hindsight process does not need an interactive user's home, `wheel`, or the Docker socket.
- Define and test a backup and restore path with `hindsight-admin` or the corresponding pinned-version mechanism. Exercise restore against a fresh isolated temporary data path and verify the restored sentinel there; never overwrite or destructively restore the active data path without explicit user approval. Order the backup job after the service, make archives owner-only, and keep a copy outside the primary data path when the memories matter.
- Test service restart and container recreation without losing a retained sentinel. Reboot as well when the user authorizes it.

The service needs an LLM provider for extraction and consolidation in addition to its local embedding and reranking models.
Use a low-cost model unless measured extraction quality requires a larger one.
Provider credentials and billing failures can break retention while `/health` continues to return success, so a health check is necessary but insufficient.
In Hindsight `v0.8.6`, fact extraction defaults to a `64000`-token completion allowance.
Some OpenAI-compatible gateways reserve or affordability-check that full allowance before generation, so a tiny retain can fail with a billing error even though it would produce a short answer.
Retention extraction and consolidation use separate completion limits, so cap both deliberately for the chosen model and budget.
The clean review used:

```text
HINDSIGHT_API_RETAIN_MAX_COMPLETION_TOKENS=8192
HINDSIGHT_API_CONSOLIDATION_MAX_COMPLETION_TOKENS=8192
```

Then prove extraction and consolidation quality with actual retain-and-recall tests and a clean server-error window.

Protect the REST service with Hindsight's API-key tenant extension and a strong tenant API key.
For the version tested, the relevant settings were:

```text
HINDSIGHT_API_MCP_ENABLED=false
HINDSIGHT_API_TENANT_EXTENSION=hindsight_api.extensions.builtin.tenant:ApiKeyTenantExtension
HINDSIGHT_API_TENANT_API_KEY=<strong-random-secret>
HINDSIGHT_API_LLM_PROVIDER=<provider>
HINDSIGHT_API_LLM_MODEL=<model>
HINDSIGHT_API_LLM_API_KEY=<provider-secret>
```

These names are version-sensitive; verify them against the pinned server version.

On Apple Silicon, local embedding and reranker models worked interactively but crashed under a long-running launchd process through MPS/XPC.
Forcing both local components to CPU stabilized the daemon:

```text
HINDSIGHT_API_EMBEDDINGS_LOCAL_FORCE_CPU=true
HINDSIGHT_API_RERANKER_LOCAL_FORCE_CPU=true
```

Limiting all worker concurrency to one slot also made behavior easier to reason about during validation:

```text
HINDSIGHT_API_WORKER_MAX_SLOTS=1
HINDSIGHT_API_WORKER_CONSOLIDATION_RESERVED_SLOTS=0
HINDSIGHT_API_CONSOLIDATION_LLM_PARALLELISM=1
```

In `v0.8.6`, `HINDSIGHT_API_WORKER_CONSOLIDATION_RESERVED_SLOTS` is a reservation floor, not a concurrency ceiling, and its deprecated `...MAX_SLOTS` predecessor had the same counterintuitive behavior.
With a one-slot global pool, leave that slot shared by setting the consolidation reservation to zero; reserving the only slot would prevent ordinary retain work from claiming it.
Do not use the reservation setting alone to claim that consolidation is limited to a single worker.

Cold starts can take more than a minute because of migrations and model loading.
Use readiness polling and service retries rather than treating the first failed health check as a broken installation.

Binding only to a transient overlay-network address creates a service start-order dependency and can take local clients down when that network restarts.
A stable bind such as `0.0.0.0` avoids that dependency, but it also exposes the port to every reachable interface.
Use bearer authentication, host firewall rules, and a private network; use TLS or a trusted reverse proxy whenever traffic leaves that private network.

On macOS, a background service cannot prompt to unlock the login Keychain.
If secrets are unavailable at boot, exit cleanly and let launchd retry after a delay.

## Secret delivery

Keep the bearer token and LLM provider key outside Git and outside immutable build stores such as the Nix store.
Use a system secret store when available, with an owner-only runtime file as a practical bridge for CLI hooks.
The coding-agent user needs the Hindsight bearer token, but does not need the server's LLM provider key.
Keep the provider key readable only by the server service account or root, and deliver any generated environment file inside the service's private runtime directory so systemd removes it when the service stops.
A database-only backup is not a complete machine-loss recovery plan.
Back up these secrets through the system secret store, or document how to rotate the tenant token and redeploy it to every client after restore.

Recommended permissions are:

```text
~/.config/hindsight                  0700
~/.config/hindsight/api-token        0600
```

The clients need the same bearer token that the server accepts.
Generating an independent token on each machine does not create additional valid clients; it creates authentication failures.

Test every way an agent can start:

- Interactive shell
- Non-interactive login shell
- Non-interactive non-login shell used by SSH and remote executors
- GUI-launched process on macOS
- launchd or systemd service

Putting the token only in an interactive shell file caused remote Codex executors and some hooks to receive no authentication.
For zsh, environment setup that must reach non-interactive shells belongs in `.zshenv`, or the adapter should read the owner-only token file directly.
On macOS, GUI processes may also need `launchctl setenv` or direct token-file access because they do not inherit a terminal's environment.

Never print the token while copying or testing it.
Redact request headers and environment dumps from diagnostics.
Keep adapter state directories and files owner-only as well (`0700` and `0600`) because recall checkpoints can contain private repository context.
Verify ownership and writability of every parent directory, not only the final leaf; a root-owned `~/.local` can make a hook fail even when `~/.local/lib/hindsight` itself was installed for the user.
Use each coding agent's own existing authentication for relay tests unless the user explicitly authorizes another credential source.

## MCP exclusion contract

This design uses no Hindsight MCP at runtime.
Some official Hindsight distributions may contain dormant MCP modules or a console entry point in the same artifact as the REST API; do not configure or start them, and prefer a narrower artifact when it satisfies the required embedding, reranking, and database providers.
Verify all of the following:

- The server has `HINDSIGHT_API_MCP_ENABLED=false`.
- The server's `/mcp/default/` route returns HTTP 404.
- `codex mcp list` contains no Hindsight registration.
- `claude mcp list` contains no Hindsight registration.
- Claude settings contain no Hindsight `mcpServers` entry.
- No Hindsight Claude plugin is installed if that plugin bundles an MCP proxy.
- No `mcp_server.py`, `run_mcp.sh`, or equivalent launcher was copied into an active adapter or service path.
- The Pi extension calls REST directly and registers no MCP server.

Do not infer MCP usage from the `/v1/default/...` URL.
Again, `default` is the tenant namespace in the REST API.

## Verification

Run a quick structural test on every machine after installation, upgrades, hook changes, or token rotation.
It should verify:

- Each of the three adapters independently passes the same bank resolver cases and resolves identical repository and worktree bank IDs.
- Normal repositories, linked worktrees, submodules, directories outside Git, symlinked working directories, spaces, and non-ASCII paths are covered by resolver tests.
- Hook and extension files exist and their registrations were merged successfully; seed unrelated hooks on the same events in a fixture and prove they survive unchanged.
- A second setup run produces an empty configuration diff and exactly one registration for each Hindsight hook.
- On NixOS, the server, container, storage, startup, and backup declarations exist in managed Nix source; no imperative environment, hand-written user unit, or ad hoc wrapper owns the deployment.
- The server starts independently of login, the image reference contains an immutable digest, backup and isolated restore have both been exercised without replacing active data, and a retained sentinel survives restart and container recreation.
- The URL and bank policy match across clients.
- Changing either mission value updates a bank already seen by each client; a boolean `mission set` cache is insufficient.
- The token directory and file permissions are `0700` and `0600`.
- Authenticated REST can list or access banks.
- Both login and non-login non-interactive shells can authenticate.
- Hindsight MCP is absent from the server and all three clients, and no unnecessary Control Plane port is reachable.
- Adapters time out and fail open when the server is unavailable.
- Resolver, timeout, fail-open, retain, and recall checks run separately for Claude Code, Codex, and Pi rather than treating one adapter as representative of the others.
- `SessionStart` performs the promised bounded health check instead of silently skipping it when an explicit API URL is configured.
- A Pi session ending in a tool result does not retain that raw tool result as assistant text.
- Held-out synthetic fake-secret fixtures cover at least a PEM private-key block, bearer token, common API-token prefix, shell assignment, and JSON credential field. Keep those fixtures outside the filter implementation, verify that each causes both recall and retention to be skipped before any request reaches Hindsight, and verify that its unique marker appears in neither outbound requests nor adapter, setup, or server logs.
- Adapter state files that contain recall or retention checkpoints are mode `0600` inside mode `0700` directories.

Then run a real cross-agent relay in one unique temporary bank:

```text
Codex retains exact value A
  -> wait until REST recall returns A
Claude Code recalls A and retains exact value B
  -> wait until REST recall returns B
Pi recalls B and retains exact value C
  -> wait until REST recall returns C
Codex recalls C
```

Use fresh agent sessions at every boundary.
Give each identifier a short random value and describe it as durable project configuration.
Do not include the value being recalled in the receiving agent's prompt or in the REST query used to poll for it; keep the expected value only in the out-of-band verifier.
Use ordinary persisted Codex sessions for retention tests because an ephemeral session deliberately leaves no transcript for a Stop hook to retain.
Poll recall for up to five minutes because retention only acknowledges the asynchronous job; it does not mean extraction has finished.
Inspect the agent's recorded recall context as well as its natural-language answer so the test distinguishes hook failure from model behavior.
Directly invoking an adapter or hook is a structural test, not a cross-agent relay.
If any agent is missing or unauthenticated, report the relay as blocked; do not substitute direct hook invocation or claim that the relay passed.
Each named CLI must run as a fresh authenticated process and exercise its installed hook or extension at that boundary.
Use persisted hook trust, or an automation bypass only after explicit user approval; a silently chosen trust bypass cannot establish acceptance.

Create a unique temporary bank for each run.
Delete only that bank after success.
Preserve the bank, transcripts, server logs, and test work directory on failure.

Watch the server logs during the relay.
The following can coexist with a successful `/health` response:

- LLM authentication or credit failures
- Fact-extraction JSON parsing errors
- Background worker crashes
- A retain request accepted but never made recallable

Count new extraction errors during the test and fail if the count increases.

## Lessons from the working deployment

1. A shared server does not create shared memory by itself. Identical bank identity across agents is the essential contract.
2. Agent-prefixed banks defeat cross-agent recall. Put agent identity in provenance fields.
3. The `default` URL component is a tenant namespace, not a catch-all memory bank.
4. Worktrees and submodules break naive directory-name bank resolution in different ways.
5. Hook installers that replace configuration are unsafe. Pin source and merge settings.
6. An upstream integration can bundle REST and MCP together. Copying the whole plugin can silently violate a REST-only design.
7. Claude Code Stop hooks must finish synchronously even when server-side extraction is asynchronous.
8. A retention interval greater than one loses short sessions unless a reliable final-session hook exists.
9. Cumulative and compacted transcripts require deliberate progress and document-ID handling.
10. A boolean mission cache makes configuration changes look deployed when old banks still use old instructions.
11. Extraction models need explicit instructions to preserve exact technical identifiers.
12. Health checks prove process availability, not successful extraction, provider authentication, or recallability.
13. Secrets present in an interactive terminal may be absent from SSH, GUI, and hook processes.
14. GPU acceleration that works in a terminal may be unstable in a macOS background daemon.
15. Asynchronous retention requires polling and an end-to-end relay test. A successful HTTP response is only the start of the test.
16. Every adapter should fail open so a memory outage never prevents the coding agent from working.
17. A receiving prompt that contains the expected identifier does not test recall; it tests copying from the prompt.
18. Ephemeral Codex sessions do not provide the transcript that Stop retention needs.
19. Symlinked working directories expose resolver differences that normal worktree tests miss.
20. Setup must be idempotent; blindly appending hooks makes every rerun execute recall and retention more than once.
21. A currently healthy NixOS process is not a durable NixOS deployment when it depends on imperative files and hard-coded store paths.
22. Anonymous volumes, mutable image tags, and login-bound user services can all pass an immediate smoke test and still lose memory or fail after reboot.
23. Docker is optional at the architecture level, but a container is the safer NixOS route when the tested bare binary distribution is not actually Nix-portable.
24. Pi retention must select assistant-role content explicitly; the last text-bearing event can be a tool result or the user prompt.
25. A retain mission cannot protect a secret that was already sent to the extraction provider; filtering has to happen locally first.
26. A valid Codex hook file does nothing when hooks are disabled, and a displayed hook-completion status does not prove that retention occurred.
27. Hook state paths need writable parent directories as well as correct leaf permissions.
28. An oversized provider completion allowance can make a tiny retain fail an affordability check before generation.
29. Merging a hooks object can still replace unrelated hooks on the same event; merge and deduplicate the event arrays themselves.
30. The extraction-provider key belongs to the server service, not to the coding-agent user.
31. Pulling an image during every service start turns an offline reboot into an avoidable outage.
32. A retention checkpoint written before REST acceptance converts a temporary failure into permanent data loss.
33. Retention extraction and consolidation have separate completion limits; capping only one can leave background errors behind a successful recall.
34. A restore drill belongs in an isolated data path; a setup test does not authorize replacing active memory storage.

## Deliberate boundaries

This blueprint does not publish somebody else's endpoint, credentials, private repository names, hostnames, network topology, or configuration repository.
It does not make one personal Hindsight service a public multi-user offering.
It does not prescribe one service manager across platforms; use the host's existing configuration system and preserve the architecture and tests above.
It does require a declarative NixOS end state when NixOS is the host.

The source of truth is the behavior: one repository bank shared by Claude Code, Codex, and Pi over authenticated REST, with no MCP, deterministic bank resolution, safe secret delivery, and a passing real-agent relay.

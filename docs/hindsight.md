# Shared repository memory across Claude Code, Codex, and Pi using Hindsight REST

[Hindsight](https://github.com/vectorize-io/hindsight) is an open-source long-term memory system for AI agents.
It extracts durable information from conversations into memory banks, then recalls relevant memories during future work so agents can learn across sessions.
This specification defines a deployment in which Claude Code, Codex, and Pi share one Hindsight memory bank per Git repository.
Before an agent answers a prompt, it recalls relevant memories from that repository's bank and adds them to its context.
After an agent completes a turn, it sends the useful conversation to the same bank for asynchronous extraction and consolidation.
The clients use authenticated REST directly; Hindsight MCP is disabled and absent from every agent.

This specification records a tested design.
It grew from a working native macOS server, client deployments on macOS, NixOS, and Ubuntu, real cross-agent relay tests, and a clean NixOS server exercise completed in July 2026.
The deployment failures found during that work are expressed below as requirements and acceptance tests.
These are tested reference configurations; every other platform, package, or service-manager combination still requires the full acceptance process.

Thanks to [Blake Lash](https://github.com/blakelash) for the idea of using Hindsight as a shared memory layer for coding agents.

## Use this specification

Give a coding agent this document with an explicit role instruction.

To create the first shared server, give a coding agent this URL and say:

> Set up the first shared Hindsight server on this machine from this specification.

To connect another machine, give a coding agent this URL and say:

> Connect this machine as a client to my existing shared Hindsight server from this specification.

That short instruction supplies the authorization that a bare URL cannot.
After reading the whole specification, a server-only host implements the server and secret sections; a client implements the shared contract, secret, and adapter sections; a host serving both roles implements both paths.

## Architecture and invariants

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

One server is shared, while one bank per Git repository separates project memory.
Agent identity belongs in tags and metadata, not in the bank name.
This lets a fact retained by Claude Code be recalled by Codex or Pi in the same repository.

Every client must use the same repository resolver, authenticated REST contract, recall and retention policy, local secret filtering, and fail-open behavior.
A successful retain response means that the server accepted asynchronous work; it does not prove that extraction completed or that the memory is recallable.

## Execution rules for the coding agent

If the user directed you here to set this up, treat this document as an implementation specification.
Read it completely, then implement and test the setup rather than returning a summary or plan.

- Determine the requested role from the user's instruction before checking prerequisites: first server, client, or both.
- If the role is ambiguous, inspect managed configuration and the environment for an existing Hindsight REST endpoint, then stop and ask whether this host should become the server or connect as a client.
  For a client, ask for the endpoint and token-delivery method; do not silently install a server.
- Inspect the operating system, shell, service manager, existing configuration management, and relevant existing Hindsight or coding-agent installations before changing anything.
- Preserve the machine's configuration model.
  For example, update managed Nix or chezmoi sources instead of hand-editing their generated files.
- Resolve the exact managed-source revisions and flake inputs that the activation command will evaluate.
  A successful switch can still activate an older locked input when the desired changes exist only in another working tree.
- Treat a local input override as temporary validation rather than a durable deployment.
  Prove that the override reaches the inner build and activation commands; wrapper applications that do not forward `"$@"` can silently drop it.
- Before server side effects, verify that a funded extraction-provider credential is available, outbound downloads work, required ports are free, and the host has enough durable storage and memory.
- Before client side effects, verify that Claude Code, Codex, and Pi are installed, authenticated, and can each complete a harmless one-shot request with the model that will be used for testing.
  Also verify that hook approval and authenticated access to the shared REST endpoint are available.
- A host serving both roles must pass both prerequisite sets.
  Stop and ask about any missing prerequisite rather than installing coding agents, inventing credentials, reusing the extraction-provider credential, or silently weakening the test.
- Pin a Hindsight release and source revision.
  Verify version-sensitive flags, API fields, package contents, and integration files against the source and versioned documentation at that exact revision; use current documentation only to choose a newer release.
- Preserve server state explicitly.
  Pin container images by version and digest, use a declared persistent data path or named volume, authenticate PostgreSQL when it is separate, order separate services by readiness, arrange backups, and make startup independent of an interactive login.
- On NixOS, implement the server in the managed Nix configuration.
  If the active flake or module source cannot be located and updated, stop before side effects and ask where it is managed.
  Do not leave an imperative `uv` environment, ad hoc Docker container, anonymous volume, mutable image tag, or wrapper containing hard-coded Nix store paths as the final deployment.
- Configure direct REST recall and retention for Claude Code, Codex, and Pi.
  Do not configure MCP, install an MCP proxy, or install a plugin that implicitly starts one.
- Merge hooks and settings without replacing unrelated user configuration, including entries on the same lifecycle event; append only missing Hindsight entries and deduplicate this integration's own entries.
- Keep secrets out of Git, declarative build stores, logs, and command output.
  Ask only for credentials or consequential choices that cannot be discovered safely.
  Do not reuse the Hindsight extraction-provider credential to authenticate a coding agent without explicit user approval.
- Do not describe the deployment as durable while required changes exist only in uncommitted managed-source working trees or temporary input overrides.
  Report that state explicitly; when authorized, commit and push the managed sources, refresh dependent locks, repeat the ordinary activation without overrides, and rerun verification.
- Finish by applying the setup twice, proving that the second run creates no duplicate hooks or settings, then running the structural checks and real cross-agent relay test below.
- Report the exact agent, server, database, and container versions; source revisions and image digests; every changed path including system-wide paths; credential-delivery method; boot and trust state; test results; and every deviation from this design.

## Shared memory contract

### REST API

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
      "document_id": "deterministic-session-plus-turn-document-id",
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

The adapters in this design use one deterministic session-plus-turn document ID for each paired prompt and final assistant message.
Replaying the same turn is therefore idempotent, while a later turn cannot replace earlier content.
Use a stable session-level document ID only when the payload contains the complete cumulative session and replacement is intentional.

Set the bank's missions with:

```json
{
  "updates": {
    "reflect_mission": "Maintain durable technical knowledge about this Git repository across coding agents.",
    "retain_mission": "Extract project decisions, architecture, conventions, user preferences, and useful failed approaches. Preserve exact non-secret technical identifiers verbatim, including hashes, hostnames, paths, flags, commands, versions, and configuration values. Every explicit non-secret identifier and configuration value must appear verbatim in the extracted memory text, not only as an entity. Never extract or retain credentials, private keys, authentication tokens, or other secrets. Ignore transient command output and routine chatter."
  }
}
```

Cache bank mission updates only as an optimization.
Cache the complete reflect and retain mission values, not a boolean saying that the bank was configured once.
Otherwise changing a mission locally never updates banks already seen by that client.

Verify these examples against the pinned Hindsight version before implementing them.

### Repository bank identity

Use the main Git repository directory name as the bank ID, with no `claude`, `codex`, or `pi` prefix.
Every adapter must use the same resolver.
This default requires the repository checkout to have the same directory name on every client machine.
Confirm that assumption before installation, or set the same explicit `HINDSIGHT_BANK_ID` on every client for repositories whose checkout names differ.

The resolver should follow this order:

1. Honor an explicit `HINDSIGHT_BANK_ID` override, which is useful for testing.
2. Resolve `<cwd>` through symlinks, then run `git -C <real-cwd> rev-parse --path-format=absolute --git-common-dir`.
3. For a normal checkout or linked worktree, use the basename of the directory containing that common Git directory.
4. If the returned path is inside `.git/modules`, this is a submodule.
   Use the basename of `git -C <cwd> rev-parse --show-toplevel` instead.
5. Outside Git, fall back to the basename of the real current directory.

Using `--git-common-dir` is important.
`--show-toplevel` alone gives each linked worktree its own directory name, which splits one repository's memory across banks.
Using the parent repository's internal `.git/modules/...` path for a submodule gives the wrong identity, so submodules need the explicit exception.

Repository basenames can collide when two unrelated repositories have the same directory name.
This deployment accepts that tradeoff.
If collisions are likely, derive a stable ID from the normalized Git remote plus repository name, and use the identical algorithm in all three clients.

### Recall and retention policy

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
Entity metadata alone cannot satisfy this contract because normal recall can return memory text without the entity's exact value.

## REST-only boundary

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

The `/v1/default/...` paths described above are REST endpoints.
Their `default` component is the tenant namespace, not evidence of MCP or a catch-all bank.

## Server deployment

Run one Hindsight API server on an always-available host reachable by all client machines.
Most machines are clients only.
Other users should normally run their own server rather than connect to somebody else's personal memory store.

### Artifact and platform choice

Docker is optional.
A bare `hindsight-api` installed with `uv` worked for the original macOS server and can be supervised by launchd.
At the time tested, the bare API process did not include the web Control Plane; the Docker distribution bundled additional components and ports.
Confirm the current upstream packaging before relying on a UI or a documented Docker port.
Consult Hindsight's current [installation guide](https://hindsight.vectorize.io/developer/installation) before choosing an artifact, and its [Admin CLI guide](https://hindsight.vectorize.io/developer/admin-cli) before defining backup and restore.

Do not assume the bare Python distribution is portable to NixOS.
A clean NixOS test of `hindsight-api==0.8.6` with `pg0-embedded==0.15.0` failed on native-library lookup, PostgreSQL's hard-coded timezone-data path, and finally pg0 returning no database URL after PostgreSQL started.
Manually extending `LD_LIBRARY_PATH`, adding `/usr/share/zoneinfo`, and moving only PostgreSQL into an imperative Docker container produced a working but unacceptable hybrid: it depended on hard-coded Nix store paths, an anonymous database volume, a mutable image tag, accidental restart ordering, and a logged-in user session.

For a new NixOS server, use one of these durable paths:

1. Declare the version- and digest-pinned API-only image `ghcr.io/vectorize-io/hindsight-api:<version>@sha256:<digest>` in NixOS, including its embedded database, stable worker ID, explicit persistent `/home/hindsight/.pg0` storage, health check, authenticated REST endpoint, restart ordering, and backup job.
   The broader `ghcr.io/vectorize-io/hindsight` image also starts the web Control Plane and is unnecessary for a REST-only server.
   Treat that broader image as diagnostic-only on NixOS, never as the accepted final deployment.
   If diagnosis requires it, disable the Control Plane explicitly, verify that its port is unreachable even through the container bridge, and replace it with the API-only image before acceptance.
2. Package Hindsight and PostgreSQL/pgvector properly in Nix and keep every runtime dependency and service relationship in the managed configuration.

The clean NixOS review used Hindsight `v0.8.6` at source revision [`08995e3`](https://github.com/vectorize-io/hindsight/commit/08995e3013858e705fb4ca27c0ade3a286ef4750) and the portable multi-architecture image pin `ghcr.io/vectorize-io/hindsight-api:0.8.6@sha256:3db1536d84a14a10afbd08cc8f82bf4eec03c123d950705226c999bea14ca0f0`.
That API-only image became healthy without host-library workarounds, enforced bearer authentication, returned 404 for MCP, completed exact retain and recall, and preserved its sentinel across container restart through persistent pg0 storage.

Do not improvise a third hybrid path merely to make the first health check pass.
If neither durable option fits the host's existing configuration model, stop and ask the user which server host to use.

### Persistence and service lifecycle

For any server deployment:

- Pin the Hindsight release or source revision and every container image by immutable digest; a release tag alone is not immutable.
- Pull or load the pinned image during deployment rather than on every service start, so an offline reboot can use the cached image.
- Use an explicit named volume or host data path that survives container recreation, and verify ownership before first start.
- Set a stable `HINDSIGHT_API_WORKER_ID` so interrupted work remains recoverable across container replacement.
- Authenticate PostgreSQL when it is a separate service; loopback binding does not make `POSTGRES_HOST_AUTH_METHOD=trust` a good durable configuration.
- When PostgreSQL is separate, make Hindsight depend on database readiness.
  With embedded pg0, make readiness polling cover full API and database initialization.
- Ensure a user service has linger enabled, or prefer a system service, if it must be available before login.
- Run a native service under a dedicated account, or constrain a container to its declared data and secret mounts; the Hindsight process does not need an interactive user's home, `wheel`, or the Docker socket.
- Define and test a backup and restore path with `hindsight-admin` or the corresponding pinned-version mechanism.
  Exercise restore against a fresh isolated temporary data path and verify the restored sentinel there; never overwrite or destructively restore the active data path without explicit user approval.
  Order the backup job after the service, make archives owner-only, and keep a copy outside the primary data path when the memories matter.
- Test service restart and container recreation without losing a retained sentinel.
  Reboot as well when the user authorizes it.
- Package-manager output identifies installed files only.
  After an in-place native-package upgrade, acceptance also requires a new managed daemon process started after the executable changed; after a container upgrade, require a replacement container using the pinned digest.

### Extraction provider and API authentication

The service needs an LLM provider for extraction and consolidation in addition to its local embedding and reranking models.
Start with a low-cost model that reliably follows Hindsight's structured extraction contract unless measured quality requires a larger one.
The macOS deployment tested Hindsight `v0.8.5` with OpenRouter's `openai/gpt-oss-20b`, a Hindsight-recommended model for structured retention and consolidation.
The exact settings were:

```text
HINDSIGHT_API_LLM_PROVIDER=openrouter
HINDSIGHT_API_LLM_MODEL=openai/gpt-oss-20b
```

It completed both successfully while leaving Hindsight's completion-limit overrides unset.
Provider credentials and billing failures can break retention while `/health` continues to return success, so a health check is necessary but insufficient.
In the tested Hindsight `v0.8.5` and `v0.8.6` releases, fact extraction defaults to a `64000`-token completion allowance.
That allowance is an output ceiling, not the number of tokens a normal retain consumes.
Some OpenAI-compatible gateways reserve or affordability-check the full allowance before generation, so a tiny retain can fail with a billing error even though it would produce a short answer.
Choose retention and consolidation limits explicitly for the selected model, provider, and budget; the two operations have separate settings.
Do not lower the `64000` retain ceiling automatically when an inexpensive model supports it.
If provider affordability or quota requires a lower ceiling, reduce it and then repeat exact retain, recall, and consolidation tests against realistic transcripts.
The clean NixOS review used these lower limits successfully:

```text
HINDSIGHT_API_RETAIN_MAX_COMPLETION_TOKENS=8192
HINDSIGHT_API_CONSOLIDATION_MAX_COMPLETION_TOKENS=8192
```

Treat those values as one tested deployment choice, not a universal default.
Prove extraction and consolidation quality with actual retain-and-recall tests and a clean server-error window.

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

### Runtime and network behavior

On Apple Silicon, local embedding and reranker models worked interactively but crashed under a long-running launchd process through MPS/XPC.
Forcing both local components to CPU stabilized the daemon:

```text
HINDSIGHT_API_EMBEDDINGS_LOCAL_FORCE_CPU=true
HINDSIGHT_API_RERANKER_LOCAL_FORCE_CPU=true
```

Use one slot reserved for ordinary retention plus one shared slot for consolidation and other background work:

```text
HINDSIGHT_API_WORKER_MAX_SLOTS=2
HINDSIGHT_API_WORKER_RETAIN_RESERVED_SLOTS=1
HINDSIGHT_API_WORKER_CONSOLIDATION_RESERVED_SLOTS=0
HINDSIGHT_API_CONSOLIDATION_LLM_PARALLELISM=1
```

In `v0.8.6`, per-operation `...RESERVED_SLOTS` settings are reservation floors, not concurrency ceilings, and deprecated `...MAX_SLOTS` aliases had the same counterintuitive behavior.
A one-slot shared pool allowed a slow recovered consolidation job to block ordinary retention beyond the five-minute relay window.
Reserving one of two slots for `retain` prevents that starvation; the remaining shared slot lets consolidation and other operation types run, while `HINDSIGHT_API_CONSOLIDATION_LLM_PARALLELISM=1` bounds work inside consolidation.
Do not use a reservation setting alone to claim that an operation type is capped at that value.

Cold starts can take more than a minute because of migrations and model loading.
Use readiness polling and service retries rather than treating the first failed health check as a broken installation.

Binding only to a transient overlay-network address creates a service start-order dependency and can take local clients down when that network restarts.
A stable bind such as `0.0.0.0` avoids that dependency, but it also exposes the port to every reachable interface.
Use bearer authentication, host firewall rules, and a private network; use TLS or a trusted reverse proxy whenever traffic leaves that private network.

## Secrets and process authentication

Keep the bearer token and LLM provider key outside Git and outside immutable build stores such as the Nix store.
Use a system secret store when available, with an owner-only runtime file as a practical bridge for CLI hooks.
On macOS, a background service cannot prompt to unlock the login Keychain.
If secrets are unavailable at boot, exit cleanly and let launchd retry after a delay.
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

## Client adapters

Claude Code, Codex, and Pi must already be installed and authenticated on a client machine.

### Codex

Use the pinned upstream REST integration as the starting point.
Register a `UserPromptSubmit` hook for recall and a `Stop` hook for retention.
Merge these entries into the user's existing hook file rather than replacing the file.
Enable Codex's hook feature in its managed configuration as well as registering the hooks.
In Codex `0.146.0` the current setting is `[features].hooks = true`; the older `[features].codex_hooks` spelling is deprecated.
Check the installed Codex version and use its current feature name rather than assuming that a valid hook file is enough.
Follow the installed release's [hook contract](https://developers.openai.com/codex/config-advanced#hooks). Its `UserPromptSubmit` input includes `session_id`, `turn_id`, and `prompt`; its `Stop` input includes the same identifiers and `last_assistant_message`.
Cache the prompt by session and turn, then pair it with `last_assistant_message` for per-turn retention.
Use one deterministic document ID per turn so repeated Stop delivery is idempotent.
Do not read `transcript_path`; Codex explicitly documents that transcript format as unstable.
Return valid `Stop` JSON such as `{"continue": true}` after a successful or intentional no-op run when the installed release requires JSON output.

Codex asks the user to trust hook command definitions.
That trust is tied to the hook definition hash, so changing the command or registration requires another review in `/hooks`.

Recommended behavior:

- Recall only from the repository bank.
- Retain user and assistant messages every turn.
- Use one stable document ID per turn.
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

Claude's `UserPromptSubmit` event supplies `session_id` and `prompt`, and `Stop` supplies the same session plus `last_assistant_message`.
Claude does not document a turn ID, so assign an owner-only per-session sequence when staging each prompt.
Pair the staged prompt with the final assistant message and use one deterministic document ID per sequence.
Repeated Stop delivery then becomes an idempotent no-op after the successful retain is marked complete.
Do not parse Claude's cumulative transcript or track compaction offsets.
A failed request must leave the staged turn eligible for a later retry.

Tag retained material with `agent:claude-code`, and make recall failures non-fatal.
Disable Claude native auto memory when Hindsight is canonical.
Audit existing `MEMORY.md` files before disabling it, preserve any unique legacy content as an archive or migrate it through the same local secret policy, and do not synchronize either product's private native memory directory.

### Pi

Use a small native TypeScript extension with `fetch`; no Python bridge or MCP registration is needed.

Map Pi's lifecycle to the same contract:

- `session_start`: check server health.
- `before_agent_start`: resolve the bank, recall memories, and append bounded memory text to the system prompt.
- `agent_end`: retain the user prompt and assistant-role text asynchronously.

Keep pending prompt state per session rather than in one global variable.
Select assistant content by role rather than taking the last message containing text; an aborted or tool-ending loop must not retain raw tool output as the assistant response.
Use the shared repository resolver, URL-encode the bank, attach `agent:pi` provenance, set request timeouts, and fail open.

## Verification

Use three verification levels.

### One-time implementation acceptance

Run one-time implementation acceptance after the first setup and after material changes to repository resolution, persistence, service architecture, or secret filtering.
It should verify:

- Each of the three adapters independently passes the same bank resolver cases and resolves identical repository and worktree bank IDs.
- Normal repositories, linked worktrees, submodules, directories outside Git, symlinked working directories, spaces, and non-ASCII paths are covered by resolver tests.
- Hook and extension files exist and their registrations were merged successfully; seed unrelated hooks on the same events in a fixture and prove they survive unchanged.
- A second setup run produces an empty configuration diff and exactly one registration for each Hindsight hook.
- The installed hook and extension symlinks resolve to the immutable artifacts produced by the intended configuration.
  Assertions inspect those installed artifacts rather than only the source checkout or an earlier build result.
- When activation uses a local flake input override, the override reaches the actual inner build and switch commands.
  A successful wrapper exit is insufficient evidence because a launcher can consume or drop arguments.
- The final ordinary activation uses committed managed sources and refreshed input locks and produces the same verified behavior without a temporary override.
  If the user has not authorized those persistence operations, report durability as outstanding instead of claiming completion.
- On NixOS, the server, container, storage, startup, and backup declarations exist in managed Nix source; no imperative environment, hand-written user unit, or ad hoc wrapper owns the deployment.
- The server starts independently of login, the image reference contains an immutable digest, backup and isolated restore have both been exercised without replacing active data, and a retained sentinel survives restart and container recreation.
- Changing either mission value updates a bank already seen by each client; a boolean `mission set` cache is insufficient.
- Exact identifiers appear verbatim in recalled memory text; an identifier present only in entity metadata does not pass.
- Adapters time out and fail open when the server is unavailable.
- Resolver, timeout, fail-open, retain, and recall checks run separately for Claude Code, Codex, and Pi rather than treating one adapter as representative of the others.
- `SessionStart` performs the promised bounded health check instead of silently skipping it when an explicit API URL is configured.
- A Pi session ending in a tool result does not retain that raw tool result as assistant text.
- Held-out synthetic fake-secret fixtures cover at least a PEM private-key block, bearer token, common API-token prefix, shell assignment, and JSON credential field.
  Keep those fixtures outside the filter implementation, verify that each causes both recall and retention to be skipped before any request reaches Hindsight, and verify that its unique marker appears in neither outbound requests nor adapter, setup, or server logs.

### Per-machine quick check

Run a quick structural and connectivity test on every machine after installation, upgrades, hook changes, or token rotation.
It should verify:

- Hook and extension files exist and the expected registrations are active.
- Installed client files resolve to the intended active generation, and the assertions below run against those installed files rather than the source checkout.
- The URL and bank policy match across clients.
- The token directory and file permissions are `0700` and `0600`.
- Authenticated REST can list or access banks.
- The active server process or container was created from the pinned artifact; checking only the installed package version is insufficient after an upgrade.
- The health check polls through the documented cold-start window instead of failing after one immediate request.
- Both login and non-login non-interactive shells can authenticate.
- Hindsight MCP is absent from the server and all three clients, and no unnecessary Control Plane port is reachable.
- Codex and Claude pair staged prompts with `last_assistant_message`, create one deterministic document per turn, and never read `transcript_path`.
- Adapter state files that contain recall or retention checkpoints are mode `0600` inside mode `0700` directories.
- Claude native auto memory is disabled when Hindsight is canonical, and pre-existing native memory files remain available as an audited archive until explicitly migrated or removed.

### Full cross-agent relay

Run a real cross-agent relay in one unique temporary bank:

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
Require that exact value in recalled memory text; entity metadata or a vague memory that merely mentions an identifier does not pass.
Do not include the value being recalled in the receiving agent's prompt or in the REST query used to poll for it; keep the expected value only in the out-of-band verifier.
Use fresh Codex sessions for retention tests; per-turn event pairing does not require a persisted transcript.
Poll recall for up to five minutes because retention only acknowledges the asynchronous job; it does not mean extraction has finished.
Inspect the agent's recorded recall context as well as its natural-language answer so the test distinguishes hook failure from model behavior.
Directly invoking an adapter or hook is a structural test, not a cross-agent relay.
If any agent is missing or unauthenticated, report the relay as blocked; do not substitute direct hook invocation or claim that the relay passed.
Each named CLI must run as a fresh authenticated process and exercise its installed hook or extension at that boundary.
Use each coding agent's own existing authentication unless the user explicitly authorizes another credential source.
Use persisted hook trust, or an automation bypass only after explicit user approval; a silently chosen trust bypass cannot establish acceptance.

Delete only the temporary bank after success.
Preserve the bank, transcripts, server logs, and test work directory on failure.

Watch the server logs during the relay.
Record a timestamp or error-count baseline immediately before the run, preserve older entries as history, and judge the run only by new errors in its window.
The following can coexist with a successful `/health` response:

- LLM authentication or credit failures
- Fact-extraction JSON parsing errors
- Background worker crashes
- A retain request accepted but never made recallable

Count new extraction errors during the test and fail if the count increases.

## Failure modes found in deployment

The requirements above came from observed failures and clean-room testing.
The recurring patterns were:

- Shared memory depends on identical bank identity, not merely a shared server; agent prefixes, worktrees, submodules, symlinks, and confusion over the `default` tenant namespace all split or obscure memory.
- Retention missions need explicit exact-identifier instructions and caches keyed by the complete mission values; otherwise models can keep a value only as entity metadata, paraphrase the recalled memory text, or leave existing banks on stale policy.
- Adapter setup is release-sensitive; installers can replace unrelated hooks, plugins can bundle MCP, disabled hooks can look configured, repeated setup can duplicate registrations, and startup metadata can move into new standalone envelopes such as `environment_context`.
- Agent lifecycles require product-specific handling; Claude Code needs synchronous `Stop` completion, Codex and Claude must pair stable prompt and final-message events without parsing transcripts, and Pi must select assistant-role content when a session ends in a tool result.
- Declarative activation can report success while deploying an older input; uncommitted sibling repositories, stale flake locks, wrapper applications that drop arguments, and checks against a source checkout instead of the installed artifact all create false confidence.
  A local override validates behavior but is not durable until the managed sources and locks are persisted and an ordinary activation passes the same checks.
- A healthy process is not a durable or current server; imperative NixOS hybrids, anonymous storage, mutable images, login-bound services, startup image pulls, stale daemons after in-place upgrades, and untested restores can all pass an immediate health check and still fail or lose memory later.
- Credentials and state must work outside an interactive terminal; SSH, GUI, hooks, and services expose missing environment propagation, locked Keychains, unsafe provider-key sharing, late secret filtering, and unwritable parent directories.
- Provider and runtime behavior must be tested directly; health can stay green during extraction failures, macOS background GPU paths can crash, oversized completion allowances can fail affordability checks, and a long consolidation can starve retention when worker reservations are wrong.
- Acceptance requires fail-open adapters, polling asynchronous retention until recall succeeds, prompts that do not reveal the expected value, fresh real-agent sessions, server-log inspection, idempotence checks, and isolated persistence and restore tests.

## Scope and boundaries

This blueprint does not publish somebody else's endpoint, credentials, private repository names, hostnames, network topology, or configuration repository.
It does not make one personal Hindsight service a public multi-user offering.
It does not prescribe one service manager across platforms; use the host's existing configuration system and preserve the architecture and tests above.
It does require a declarative NixOS end state when NixOS is the host.

The tested behavior and acceptance criteria above are the source of truth across implementations.

# Text a local Codex agent through Telegram

[Telegram bots](https://core.telegram.org/bots) can receive messages through outbound HTTPS long polling.
This specification uses that interface to give one Telegram user a private text conversation with an existing Codex CLI on an always-on host.
The host polls Telegram, runs `codex exec --json` in a chosen working directory, and returns the final Codex answer to the same chat.
It needs no webhook, public port, DNS name, TLS certificate, tunnel, or multi-channel agent framework.

This specification records a tested design.
The reference deployment passed a real phone-to-Telegram-to-local-Codex-to-Google-Calendar relay on macOS on August 17, 2026, using Codex CLI 0.147.0.
The setup and runtime failures found during that work are expressed below as requirements and acceptance checks.
Other operating systems, service managers, Codex versions, and connector sets still require the full acceptance process.

## Use this specification

Give a coding agent this document with an explicit instruction:

> Set up a private single-user Telegram gateway to my existing local Codex CLI from this specification, preserve this machine's configuration model, and run the full acceptance test.

That instruction supplies authorization that a bare URL cannot.
The host must already have an authenticated Codex CLI that works non-interactively, an always-on user session with outbound HTTPS, a Telegram account, a durable working directory, and an operating-system secret store.
After reading the whole specification, the coding agent should inspect those prerequisites, implement the gateway, activate it, and test the installed result rather than only summarizing this document.

## Transport choice

| Option | Result |
| --- | --- |
| Telegram Bot API | The smallest supported chat transport with outbound long polling and one ordinary phone conversation. |
| Built-in Codex Slack app | Runs through Codex cloud environments and does not by itself bridge to local-only files on a private host. |
| Custom Slack app | Socket Mode avoids a public endpoint, but it adds a workspace, two credentials, scopes, and more lifecycle machinery. |
| iMessage bridge | Has a convenient private phone surface, but consumer Messages has no supported inbound bot API; a bridge depends on Full Disk Access and undocumented local data. |
| WhatsApp Cloud API | Requires business infrastructure and a public webhook, and its business terms are a poor fit for a personal general-purpose AI bot. |
| iOS Shortcut over Tailscale SSH | Is private and small, but behaves like a request form rather than a durable conversation. |
| Multi-channel agent framework | Adds dependencies and a wider security surface before a second channel exists. |

Primary references are the [Telegram Bot API](https://core.telegram.org/bots/api), [Telegram privacy policy](https://telegram.org/privacy), [Slack Socket Mode](https://docs.slack.dev/apis/events-api/using-socket-mode/), [Codex in Slack](https://learn.chatgpt.com/docs/third-party/slack), [Apple platform security](https://support.apple.com/guide/security/secd9764312f/web), [WhatsApp Business Terms](https://www.whatsapp.com/legal/business-terms), and [WhatsApp Business Solution Terms](https://www.whatsapp.com/legal/business-solution-terms).

The Codex adapter follows the documented [non-interactive mode](https://learn.chatgpt.com/docs/non-interactive-mode).

## Architecture and invariants

The flow is:

```text
phone direct message
  -> Telegram cloud
  -> outbound getUpdates long poll
  -> single-user gateway on the private host
  -> codex exec or codex exec resume
  -> outbound sendMessage
  -> phone direct message
```

Only one gateway process polls a bot token.
It accepts private text messages only from one exact numeric Telegram user ID established through local pairing.
It processes messages serially and resumes one explicitly saved Codex thread, so turns cannot race and unrelated Codex sessions cannot be selected accidentally.

The gateway acknowledges each Telegram update in durable state before invoking Codex.
This provides at-most-once execution across crashes: a user may have to resend an interrupted request, but the service must not automatically repeat a consequential action.
State updates are atomic and owner-only.

The default permission label is `local-files read-only`.
It describes the Codex filesystem sandbox, not the complete capability boundary: connected apps can still read or modify their services when the user's prompt and connector policy authorize that action.

## Execution rules for the coding agent

- Inspect the host, shell, service manager, configuration management, Codex installation, authentication mode, active plugins, and intended working directory before changing anything.
- Preserve the machine's configuration model.
  Update managed Nix, Home Manager, chezmoi, or equivalent source instead of hand-editing generated files or leaving an ad hoc background process.
- Use the official Bot API through long polling.
  Do not add a webhook, public listener, tunnel, reverse proxy, browser automation, or general agent framework.
- Keep the bot token and paired user ID out of Git, declarative build stores, logs, shell history, Codex prompts, and Codex's child environment.
- Treat a local source or flake override as temporary validation.
  If a wrapper invokes an inner build or switch, prove that it forwards its arguments; with `nix run`, arguments for the app begin after `--`.
- Do not describe the deployment as durable while managed changes are uncommitted, a dependent input lock is stale, or only an overridden build was activated.
  When authorized, commit and push the managed sources, refresh dependent locks, run the ordinary activation without overrides, and verify the installed artifact.
- Finish with unit checks, idempotent setup, the live phone relay, and a service restart test below.

## Gateway contract

### Telegram transport and state

Use `getMe` as a token preflight before pairing or replacing a working credential.
Treat HTTP 401 and 404 as an invalid token and HTTP 409 as a webhook or competing poller; these are fatal configuration errors, not transient network failures.
Retry ordinary polling failures with a bounded delay and log only a fixed, sanitized message.

Request only `message` updates and ignore groups, channels, non-text messages, malformed updates, and senders other than the paired numeric user ID.
Sort valid updates by `update_id` before processing them.
Persist `update_offset`, the time of its last advance, and the active Codex thread ID.
The state directory must be mode `0700`, the state file mode `0600`, and writes must use an atomic replacement.

Telegram can choose a random update ID after at least one week without updates, while it retains pending updates for no more than 24 hours.
Reset a saved polling offset after six idle days, before randomization can occur and after every old update has expired, then resume strictly monotonic acknowledgement from the next received update.

Split replies below Telegram's message limit, preferring whitespace boundaries.
The tested implementation uses 4,000-character chunks, waits one second between chunks, honors one server-provided `retry_after` bounded to 30 seconds, and stops rather than retrying indefinitely.

### Codex process

Use persisted Codex sessions and save the exact thread ID emitted by the gateway's own process.
Do not use `--ephemeral`, `--last`, or a shared notion of the most recent thread.
For Codex CLI 0.147.0, all global flags precede `exec`:

```bash
codex -C <workdir> -a never -s <sandbox> \
  -c 'web_search="live"' \
  -c 'model_reasoning_effort="low"' \
  exec --json -

codex -C <workdir> -a never -s <sandbox> \
  -c 'web_search="live"' \
  -c 'model_reasoning_effort="low"' \
  exec resume <thread-id> --json -
```

Pass the prompt on standard input rather than interpolating it into a shell command.
Override approval policy, sandbox, web search, and reasoning effort on every new and resumed turn so an unsafe or slow user default cannot leak into the gateway.
Use `never` approvals because the stable non-interactive process cannot relay approval prompts to Telegram.

Parse standard output as bounded JSON Lines and keep standard error separate.
Persist `thread.started` as soon as it arrives, then return the last completed agent message after the turn exits.
If a resumed invocation exits nonzero before emitting any JSON event, clear only the saved pointer and retry the prompt once as a new thread.
Do not retry after execution has begun or after any event has arrived.

Remove every Telegram-named environment variable before spawning Codex.
Start Codex in its own process group, impose a 30-minute turn timeout, and on timeout or service shutdown send the whole group `SIGTERM`, wait a bounded grace period, then send `SIGKILL` to survivors.
Track process-group liveness independently of the leader because the leader can exit while a child still holds output open.
Bound each JSONL record; the tested implementation uses 8 MiB.

Codex loads the service user's normal configuration, project instructions, skills, plugins, and connected apps.
Plugin presence does not prove connector authentication, and a filesystem sandbox does not disable remote app writes.
Test each connector capability that the phone gateway is expected to expose.

## Pairing and security boundary

Create the bot through the verified `@BotFather` account with `/newbot`, a display name, and a unique username.
Enter the returned token only into a no-echo local terminal prompt.
Nothing should appear while the token is typed; press Return once to submit it.
Validate it with `getMe` before storing it or replacing a known-working token.

If no user is paired, stop the serving poller and wait for it to exit before pairing so two processes cannot consume `getUpdates` concurrently.
Print a fresh high-entropy code locally, accept it only in a private chat, and save the exact sender's numeric ID only when the text matches exactly.
The tested code contains 128 random bits.
Open the bot from the link returned by BotFather, tap Start if needed, and send that code as an ordinary message to the new bot, not to BotFather.
If a user is already paired, repeated setup must keep that identity and skip pairing.

Store the token and paired ID in the operating system's user-scoped credential store.
Expose them only to the gateway process at runtime, remove them before Codex starts, and never log prompts, replies, credentials, raw Telegram responses, or raw Codex errors.
Logs and user-facing failures should contain fixed diagnostic categories only.

Telegram bot chats are cloud chats, not end-to-end encrypted Secret Chats.
Local-files read-only still permits disclosure of readable local and connected data.
Protect the Telegram account with a device passcode and two-step verification, and treat any logged-in Telegram session as a key to everything this gateway can read.
Do not send credentials, banking details, detailed medical records, or sensitive attachments through it.
Use the direct Codex client for highly sensitive source material.

`/do` and `/full` are explicit per-turn filesystem escalations.
Telegram identity remains the only gateway-level authorization, so `/full` should exist only when unrestricted remote machine access is an intentional part of the threat model.
Connected-app actions require explicit user intent regardless of the filesystem mode.

## Service lifecycle

Run the gateway as the existing user under the host's managed service system.
Give it an explicit Codex binary, `HOME`, `CODEX_HOME`, state directory, and working directory.
Start it with the user's session, restart it after failure, and use a throttle so a locked credential store or invalid configuration cannot create a tight restart loop.

The setup helper should validate credentials, pair only when needed, and then signal a running service to terminate.
Let a managed `KeepAlive` policy restart it after the service manager's throttle interval instead of synchronously forcing a restart that can block behind that throttle.
On shutdown, stop the active Codex process group before the gateway exits.

## Chat contract

- Plain text starts or resumes a local-files read-only turn.
- `/do PROMPT` grants workspace-write access for that turn.
- `/full PROMPT` grants unrestricted filesystem access for that turn.
- `/new` clears the saved resume pointer and starts a fresh thread on the next prompt.
  It does not delete the underlying Codex rollout.
- `/status` reports readiness and the saved thread ID without invoking Codex.
- `/help` displays this command summary.

Reject empty prompts, unknown commands, missing command prompts, and arguments to commands that take none.
Version 1 accepts text only.

## Verification

Do not accept a successful build, a running process, or `/status` alone as proof that the gateway works.

Unit tests should cover command parsing, private-chat and numeric-user authorization, durable offset advancement before command handling, message splitting, secret stripping, JSONL parsing, immediate thread persistence, failed-resume recovery, state permissions and atomicity, the six-day offset reset, rate-limit pacing, fatal Telegram errors, malformed and oversized input, timeout handling, and cleanup when the Codex leader exits before a child.
Run the language formatter, linter, syntax check, and configuration evaluation used by the repository.

Verify the installed service and helper rather than only their source files.
When configuration comes through a pinned private input, confirm that any temporary override reached the inner activation, then commit and push the private source, refresh the public lock, and repeat the ordinary activation without the override.
The active service must resolve to the intended installed artifact after that ordinary activation.

Run the live acceptance test from the phone:

1. Run setup twice and confirm that the second run preserves the paired identity and does not start another poller.
2. Send `/status` and confirm that the gateway reports local-files read-only mode.
3. Send a harmless ordinary prompt and receive a real local Codex response.
4. Query a connected read-only service, such as `What is my next calendar event?`, and verify the answer against that service.
5. Terminate the managed gateway, wait for automatic restart, send `/status`, and then send a follow-up that proves the saved Codex thread resumed.
6. Inspect state ownership and sanitized service logs without printing credentials or message contents.

Record the Codex version, changed managed paths, credential-delivery method, active service identity, test results, and every deviation from this design.

## Known limits

Version 1 supports text prompts and final answers only.
Replies are plain text, so Markdown markers can appear literally.
It does not relay streaming output, cancellation, images, documents, voice notes, or interactive approval requests.
Each Codex turn has a 30-minute ceiling and is never automatically retried after execution begins.
If streaming, cancellation, or phone-based approvals become necessary, migrate the Codex adapter to the stable [Codex SDK](https://learn.chatgpt.com/docs/codex-sdk) with an owned local [app-server](https://learn.chatgpt.com/docs/app-server) child rather than exposing an unauthenticated app-server WebSocket.

## Scope and boundaries

This blueprint defines a single-user personal gateway, not a public or multi-user agent service.
It does not publish a bot username, user ID, token, hostname, private repository, working directory, service label, or local credential name.
It does not prescribe Nix or launchd for every host; preserve the host's existing configuration model while keeping the behavior and acceptance checks above.
The tested contract is the source of truth across implementations.

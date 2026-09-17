# OpenClaw deployment pilot specification

[OpenClaw](https://docs.openclaw.ai/) provides a private Telegram conversation with a local Codex agent, including conversation continuity, active-task controls, approvals, a dedicated browser, and scheduled checks.
The agent uses an existing ChatGPT account, repository tools, calendar connection, Kata ledger, and filtered Hindsight memory.
OpenClaw supplies the gateway, native Codex runtime integration, sessions, approvals, and scheduler.

This specification records a tested design.
The reference deployment completed its acceptance checks on macOS on September 8, 2026, using OpenClaw `2026.9.2`, the official Codex plugin `2026.9.2`, and native Codex `0.153.4`.
The setup and runtime failures found during that work are expressed below as requirements and acceptance checks.
A September 14 review found that the managed workspace instruction file was unreadable and that the native executable was not pinned by the plugin version.
The instruction and runtime checks below include those corrections; the original acceptance report did not establish them.
Other releases, platforms, service managers, and connector sets require the full acceptance process.
The term "pilot" names the initial deployment scope; software versions are recorded separately.

## Use this specification

Give a coding agent this document with an explicit instruction:

> Set up the OpenClaw deployment pilot from this specification, preserve the existing Telegram gateway and this machine's configuration model, and run the full acceptance test.

The instruction authorizes implementation, deployment, and messages to the owner's test bot, including finite acceptance schedules.
It does not authorize purchases, messages to other people, replacement of the existing gateway, or deletion of existing state.
A bare URL or a request to review or build alone does not authorize activation.

Read the whole specification, then inspect the host, managed configuration, existing services, and authenticated integrations.
The host needs an always-on user session with outbound HTTPS, an authenticated Codex account, and the existing repository integrations selected for the pilot.
Obtain a new bot token through a local hidden prompt; ask only for unavailable authentication or decisions that materially change the requested outcome.
Continue independent preparation while waiting for local authentication or phone interaction.

In this repository, follow [AGENTS.md](../AGENTS.md) and the [development workflow](development.md).
Host assignments, paths, credentials wiring, and operational evidence belong in the private input's `docs/openclaw-deployment.md`.
Use the available managed-source checkout, including uncommitted work, rather than assuming a published revision is current.
Keep intent and completion evidence in the existing Kata ledger.

## Architecture and scope

The flow is:

```text
owner's Telegram conversation
  -> outbound polling by the isolated OpenClaw gateway
  -> native Codex app-server session
  -> existing repository tools, calendar, browser, and filtered memory
  -> result delivered to the same owner conversation
```

Use one OpenClaw agent, one named deployment profile, one dedicated browser profile, and one useful read-only workflow.
Keep the existing Telegram gateway running with its own bot token, polling state, and conversations.
Only one process may poll each token.
The new bot accepts direct messages from the owner's exact numeric identity and has group access disabled.
The gateway listens only on loopback and requires authentication; Telegram long polling needs no public inbound endpoint.

Ordinary conversation stays in its bound native thread.
Independent work uses supported separate sessions without resuming another client's active native thread.
Status requests report the current phase, last verified result, and required input.
An acknowledgement is followed by a verified result or an actual failure report.

The pilot covers text and result delivery, conversation continuity, correction and cancellation, native approval routing, browser persistence, and durable scheduled checks.
Image and voice messages, phone calls, location triggers, arbitrary-site bookings, autonomous shopping, extra channels, and multi-host execution are outside the tested scope.
Existing service replacement is a separate deployment decision.

## Package and native runtime

The tested macOS installation uses the Homebrew formula declared through nix-darwin:

```nix
homebrew.brews = [ "openclaw-cli" ];
```

Keep a single-host declaration in its host module.
The formula supplies the CLI and its Node dependency; the desktop cask is unnecessary for the tested gateway.
Verify both the installed executable and the Homebrew receipt.
A pinned tap alone does not prove the installed version, and a tap update can upgrade unrelated packages during activation.
The Homebrew declaration records installation intent rather than a fully hermetic Nix package pin.

Onboard a separate named profile with a dedicated workspace and a local gateway, skipping daemon installation.
Check the effective state and configuration paths because environment overrides can change profile defaults.
Install the official plugin into that profile using the qualified version, replacing `<profile>` with its selected name:

```bash
openclaw --profile <profile> plugins install @openclaw/codex@2026.9.2 \
  --pin --accept-capabilities
```

The plugin installs Codex `0.153.4`, but that package version does not determine the executable used by every configuration.
On macOS, `homeScope: "user"` prefers the desktop application's bundled Codex, with the plugin package as a fallback.
Desktop updates can therefore change the running Codex version without a Nix or plugin update.
An explicit `appServer.command` overrides that selection; qualify shared plugins and desktop integrations before using it to pin a different executable.
See the upstream [runtime selection rules](https://docs.openclaw.ai/plugins/codex-computer-use). Verify the service's actual executable path and version, model, account, and thread identity through an actual session.
The reference test used `gpt-6-astra` with medium effort and no configured API fallback.
Select an available model through the intended account when reproducing the deployment.

The tested settings select the Codex agent runtime for the model and use `plugins.entries.codex.config.appServer` with these values:

```json
{
  "homeScope": "user",
  "mode": "guardian",
  "approvalPolicy": "on-request",
  "sandbox": "workspace-write",
  "approvalsReviewer": "user"
}
```

Sharing the existing user Codex home provides the intended authentication and plugins.
It does not establish that every existing hook or connector works through OpenClaw.
Verify the actual calendar identity, loaded project instructions, and one existing repository helper under the service's environment.
The tested calendar plugin had destructive actions disabled, and its authenticated read returned the expected account and event.
Do not change managed Codex authentication or silently switch to API billing to bypass a failure.

Keep `agents.defaults.workspace` in a separate bootstrap directory and set `agents.defaults.cwd` to the intended repository.
Keep `skipBootstrap: true` so setup preserves the repository's own instruction files.
Codex discovers task `AGENTS.md` from its working directory; a separate workspace `AGENTS.md` does not establish that pilot guidance reaches ordinary turns.
OpenClaw rejects bootstrap symlinks, including Home Manager links into the Nix store.
Forwarding guidance through `SOUL.md` is also insufficient when native model catalog instructions replace the legacy persona carrier.
Supply the pilot policy through `before_prompt_build.prependSystemContext` in the existing local bridge, with the reviewed text supplied by the Nix configuration.
The policy callback must be independent of memory recall so an adapter failure cannot suppress the instructions.
Keep workspace persona files and repository instruction files intact.
Verify a fresh and a resumed native turn can quote a distinctive pilot rule without reading files or calling tools.
The bootstrap report's `native_unverified` status and a readable file on disk are insufficient evidence of instruction delivery.
See the upstream [workspace instruction rules](https://docs.openclaw.ai/plugins/codex-harness-reference/workspace-bootstrap-files). Do not copy repositories into the profile.

## Credentials and configuration

The tested deployment uses OpenClaw's native JSON file SecretRefs for the bot token and gateway token.
Unattended Keychain access failed with the exact service Python even though another local reader succeeded.
Protected file storage was therefore selected and verified without interaction.
Do not infer unattended credential access from an interactive setup test.

Store credentials outside Git and the Nix store in a mode-`0600` file inside a mode-`0700` directory owned by the service user.
Reject symlinks, unexpected ownership, loose permissions, and incomplete values.
The setup helper accepts the new token through a no-echo terminal prompt, verifies bot identity with `getMe`, and rejects the existing bot even if its token has rotated.
Reuse the owner's already verified numeric Telegram identity when available; otherwise establish it through a local pairing flow.
Generate a separate gateway token and preserve existing credentials on repeat setup.
Keep secret values out of arguments, logs, source files, and chat.

Configure a native file provider pointing at `<credential-file>` and reference its JSON fields from Telegram and gateway authentication.
The declarative configuration contains references and the runtime owner allowlist, while the secret values remain in the protected file.
File permissions protect access by other users; they do not isolate credentials from an agent running as the same OS user.
Run the secret audit under the deployed environment and verify that no plaintext configuration secrets or unresolved references remain.

Keep the desired non-secret configuration separate from authentication, conversations, and plugin-install metadata.
The tested setup helper inspects the installed Codex plugin version, installs the pinned version when needed, and links the reviewed Hindsight adapter.
It renders the owner allowlist at runtime, applies a native configuration patch, and validates the result.
Use the same immutable adapter directory for plugin installation and configuration loading to avoid duplicate plugin discovery.
Run setup twice and verify that authentication and native session identities survive without duplicate plugins.

The tested profile remains writable for native plugin installation and configuration patching.
Do not enable immutable Nix mode while relying on an installer that rewrites profile metadata.
Schema and secret checks use the selected profile:

```bash
openclaw --profile <profile> config validate
openclaw --profile <profile> secrets audit --check
```

## Task controls and approvals

Configure `tools.exec.mode: "ask"` and enable native Telegram approval delivery to the owner.
Native requests need an explicit reply destination.
A CLI-started request without a reply route failed closed in the reference test, while `--deliver --reply-channel telegram --reply-to <owner>` delivered an approval card.

Use the same authenticated GatewayClient connection or an authorized operator-admin client for direct gateway controls.
A separate client with insufficient scope failed to cancel a CLI-started session during qualification.
The supported control path successfully applied a correction and cancelled the exact run, after which no active native run remained.
The owner also verified that phone `/stop` interrupted its native worker without leaving the fixture running.

The approval tests verified allow-once execution, rejection of a replayed decision, a fresh request for a changed destination, denial, and expiry.
The expiry fixture waited 120 seconds, and a late approval was rejected without executing.
Decisions were exercised through the supported local operator CLI; Telegram card delivery was verified separately.
Human interaction with Telegram approval buttons is outside that evidence and needs its own test when required.

Command approvals do not enforce every business rule for purchases, bookings, cancellations, or submissions.
Obtain task-specific authority for the exact destination, action, relevant amount, dates, terms, and expiry before a consequential action.
A denial or expiry permits no action, and material changes require a new decision.
Keep ordinary authorized reads and reversible preparation within the existing task authority.

## Memory and task records

Kata remains the intent and completion ledger, while OpenClaw owns its runtime session IDs and scheduler checkpoints.
Do not create another manually synchronized task list or memory database.
Reuse the existing repository-bank resolver and filtering policy described in the [Hindsight specification](hindsight.md).

Native Hindsight hooks did not run in the tested Codex integration, including a trial with native hooks explicitly enabled.
The qualified implementation uses a small local OpenClaw plugin that calls the existing filtered recall and retain adapters.
The plugin activates at startup and has explicit conversation-hook access.
It invokes recall before prompt construction and retention after a successful agent turn.

Pass only the submitted prompt and the final assistant text, together with stable session and turn identifiers and the intended repository cwd.
Reject tool-only responses and earlier-turn assistant text.
Never read a transcript file or forward raw tool output, reasoning, or recalled context as new conversation content.
Bound adapter execution time and output size, suppress private diagnostics, and fail open with a fixed warning if memory integration fails.

Disable OpenClaw's additional memory slot, automatic memory flush, periodic heartbeat, and autonomous skill review for this scope.
Explicit native schedules remain available.
Verify a filtered synthetic retention and fresh-session recall round trip, then verify recall through the managed service after restart.

## Scheduling and action recovery

Use OpenClaw's native scheduler and supported durable trigger state for observation and delivery checkpoints.
The qualified availability watch used the read tool, stayed quiet on unchanged state, and delivered one notification for a tested change.
Another gateway restart produced no duplicate notification.
An earlier version used a shell command for the read and was blocked by ask mode after restart; the final watch needed no exec allowlist or broader permission.
Remove finite acceptance jobs after collecting their receipts.

An enabled one-shot job interrupted after an action but before acknowledgement can run again at startup in OpenClaw `2026.9.2`.
The unguarded test executed its synthetic action twice.
Manually running a disabled job did not expose that behavior, and `cron.skipMissedJobs` did not disable interrupted one-shot catch-up.
Scheduler completion records alone do not provide exactly-once external effects.

Schedule read-only checks or action tools that reconcile an authoritative operation receipt before another effect.
The qualified fixture was invoked twice across restart but applied one action because it recognized the existing receipt.
A separate incomplete receipt produced explicit uncertainty and no retry.
For a real action, use the external service's operation ID and authoritative result, then test its own recovery behavior.
The synthetic receipt establishes that reconciliation pattern only; it does not qualify arbitrary commands or external services.

## Browser and useful workflow

Use a dedicated persistent browser profile with its own browser data and an unused debugging port.
Verify the resulting page state rather than treating a successful tool call as completion.
The reference test opened example.com, preserved synthetic localStorage across a browser restart, and verified removal of the test value.
It established profile persistence and a reversible action on an unauthenticated site.
Authenticated sites, booking flows, and arbitrary-site reliability require separate qualification.
Report login requirements rather than attaching the owner's normal browser profile.

Complete one useful read-only workflow using the existing calendar and archive access, with delivery only to the owner.
The reference workflow looked for an upcoming trip and used a tomorrow-calendar brief when none was found.
The calendar fallback and owner delivery completed with source identifiers and a delivery receipt.
The trip branch was not exercised by that result.

## Service, backup, and deployment

First install and configure the selected profile, then qualify the foreground gateway:

```bash
openclaw --profile <profile> gateway run --bind loopback
```

After the foreground trial, stop that process and run the same command through the host's managed service system.
The tested macOS service uses launchd with explicit executable paths, working directory, `HOME`, `CODEX_HOME`, and PATH.
It starts with the user's session, restarts automatically, and uses a throttle and owner-only state and logs.
The gateway receives a restricted environment, and the Codex configuration clears gateway and Telegram token environment variables from its child.
Use one service manager; do not also install an OpenClaw daemon or enable Homebrew services.

Verify gateway readiness, healthy Telegram polling, and plugin status after restart.
A PID alone does not establish readiness; one qualification restart took about 92 seconds before the gateway became ready.
Recheck the original gateway's identity and health without restarting it as part of the pilot.

Add the profile state and credential directory to the existing backup system, then verify a completed backup containing the new files.
Restore representative configuration, credentials, and native session SQLite state into an isolated protected directory without starting another gateway or poller.
Compare content without printing secrets, verify ownership and modes, and run SQLite's integrity check on the restored database.
The reference deployment passed a local Time Machine restore with matching configuration and credential content, preserved modes, and a successful SQLite `PRAGMA quick_check`.
A verified local backup and representative restore satisfy this pilot's backup requirement; offsite recovery is separate qualification.

Build before activation and verify the installed artifact after activation.
For Git-backed flakes, ensure that new managed files are included and that any wrapper forwards `"$@"` to the inner command.
The reference trial initially built the wrong private revision because an app wrapper discarded the override arguments.
Treat a local input override as temporary validation.
When publication is authorized, commit and push the managed sources, refresh the dependent lock, and repeat the ordinary build and activation without the override.
Distinguish local edits, committed and pushed sources, successful builds, and activated state in the handoff.

## Acceptance matrix

Run focused tests for custom credential handling and memory filtering, along with the repository's configuration and syntax checks.
Then test the installed service against the matrix below.
Record PASS, FAIL, or NOT RUN with versions, dates, evidence, and the tested interaction path in the private deployment record.
The reference deployment completed A1 through A12 within the qualifications stated here.

| ID | Test | Required evidence |
| --- | --- | --- |
| A1 | Validate configuration and build the affected target. | Schema, secret audit, and build pass; record actual service executable paths and versions separately from package pins. Fresh and resumed turns quote a distinctive pilot rule without tools. Repeat setup preserves auth and sessions without duplicate plugins. |
| A2 | Start the managed service with the separate bot. | Ready loopback service and one poller; real Telegram-to-Codex reply; original gateway remains healthy. |
| A3 | Send a follow-up and then a separate task. | Follow-up retains native context; independent work uses a separate native thread. |
| A4 | Read the calendar and run an existing repository helper. | Correct account and calendar result; helper succeeds under the service environment and intended repository instructions. |
| A5 | Correct and cancel harmless active work. | Supported gateway correction changes the result; exact-run cancellation clears active work; owner phone stop interrupts its worker without a detached fixture. |
| A6 | Exercise native approvals with reversible fixtures. | Allow-once executes once; replay, denial, expiry, and changed-action reuse do not execute. Verify Telegram card delivery and record whether decisions came from the local operator or phone. |
| A7 | Run a finite read-only availability watch. | Unchanged state is quiet; a change delivers once; restart does not repeat the observed notification; remove the job afterward. |
| A8 | Interrupt an enabled scheduled action before acknowledgement. | Repeated invocation reconciles an authoritative receipt without a second effect; an uncertain receipt stops without retry. Qualify each real action tool separately. |
| A9 | Reopen the dedicated browser profile. | Profile separation, persistent synthetic state, and a verified reversible action on the test site. Record authenticated-site tests separately. |
| A10 | Check Kata and filtered Hindsight. | Intent and completion evidence remain retrievable; synthetic retention and fresh-session recall use the expected repository bank, including after service restart. |
| A11 | Restart the service and restore representative state. | Readiness, context, ownership, and modes survive; a completed backup contains the pilot; isolated configuration, credential, and SQLite restore checks pass. |
| A12 | Complete one useful read-only workflow. | Verified calendar/archive result and owner delivery receipt; state which branch ran and which user interventions were needed. |

A missing login or unperformed interaction remains NOT RUN for that capability.
Keep historical failures in the private evidence record, with the final result and its qualifications clearly identified.
Do not claim broader approval, browser, scheduling, or recovery guarantees than the tests establish.

## Scope and boundaries

This blueprint describes a single-user deployment with existing repository tools and authenticated integrations.
It does not publish hostnames, bot usernames, user IDs, private repository paths, service labels, credential locations, or live deployment identifiers.
Preserve each host's configuration model while retaining the tested behavior and acceptance checks.
The public specification is the canonical reusable design; private overlays contain deployment choices and operational evidence.

For version-specific implementation, consult the upstream [CLI](https://docs.openclaw.ai/cli), [Codex harness](https://docs.openclaw.ai/plugins/codex-harness), [Telegram](https://docs.openclaw.ai/channels/telegram), [secrets](https://docs.openclaw.ai/gateway/secrets), and [plugin management](https://docs.openclaw.ai/cli/plugins) documentation alongside the selected release's schema and help.

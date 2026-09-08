# OpenClaw v1 implementation specification

Status: implementation specification, September 8, 2026.
Live deployment status and acceptance results belong in the private deployment overlay.

## Start here in a new session

This document is the implementation entry point and does not require the originating conversation.
Read this repository's AGENTS.md, [development workflow](development.md), and the private input's `docs/openclaw-deployment.md` before making changes.
The private overlay supplies the host, paths, existing services, and chosen defaults.
Locate it through the flake's `private` input and the operator's available working checkout; inspect local changes before choosing the source to edit.
Use the local documents when they contain uncommitted work, rather than assuming a GitHub link already contains that work.
If the private checkout is unavailable, continue public inspection and report the missing access without reconstructing private settings.

A complete implementation request can be given as:

```text
Implement and deploy the OpenClaw v1 pilot specified in docs/openclaw.md,
including the private input's docs/openclaw-deployment.md.
Follow the implementation phases and acceptance matrix, preserve the existing
Telegram gateway, and record the results in the private deployment document.
```

Treat the current user's request as the authority for the session.
Reading this specification or asking for a build alone does not authorize activation.
An explicit implementation-and-deployment request covers the pilot service and messages to the owner's test bot, including temporary acceptance-test schedules.
It does not authorize purchases, messages to other people, replacement of the existing gateway, or deletion of existing state.
Use prior authorization within its scope and ask only for missing credentials, interactive authentication, or decisions that materially change the requested outcome.

Inspect current Git status and Kata work before creating or resuming an implementation issue.
The documentation task is not the deployment task.
Use the existing implementation issue if present; otherwise create one covering the full v1 outcome.
Do not stop after adding the package when the requested scope is implementation and deployment.

## Required v1 outcome

The owner can use a private Telegram conversation to give work to an always-on local Codex agent, receive its result, and interact while it runs.
The assistant can read an existing connected calendar, execute a selected repository workflow, and perform a scheduled check with meaningful-change notification.
The implementation uses OpenClaw's existing runtime facilities wherever they meet the contract.
Do not build a replacement scheduler, gateway, approval engine, memory service, or task database as part of this pilot.

V1 includes text and result delivery, conversation continuity, task separation, correction/cancellation, interactive decisions, one dedicated browser profile, and durable scheduling.
Image and voice-message handling can be smoke-tested if supported by the selected installation, but are not required for v1 completion.
Phone calls, location triggers, arbitrary-site booking reliability, autonomous shopping, additional chat channels, and multi-host execution are later work.

### Task and interaction contract

- Ordinary conversation preserves context in its own bound native thread.
  Independent long-running work uses a separate task/session through supported OpenClaw facilities; it must not seize another client's active Codex thread.
  The owner can ask for status, and receive the current phase, last verified result, and any required input.
- An acknowledgement is not a completion report.
  Final reports identify the outcome and supporting artifact or external confirmation, or explain the actual failure.
  Corrections and stop requests must remain responsive while a worker is active.
- Reversible preparation and reads proceed under the owner's task instructions.
  Approval requests for consequential actions state the destination, exact action, relevant amount/date/terms, and expiry when applicable.
  Bind a decision to the proposed action and ask again only if its material details or authority change.
  Command approvals alone do not enforce business-level purchase or cancellation rules.
- A denied or expired approval does not execute the action.
  A restart or timeout must not blindly replay an action with an uncertain external result.
  Inspect the authoritative result before retrying; otherwise report the uncertainty and preserve the task for reconciliation.

### Integration contract

| Integration | Required behavior |
| --- | --- |
| Codex | Use the native app-server runtime and the intended existing account. Verify the selected model, native thread identity, connector identity, and loaded project instructions. Do not silently fall back to API billing or a different account. |
| Repository tools and skills | Reuse the existing managed sources and execute in the intended repository context. Do not copy private repositories or overwrite their bootstrap/instruction files. Verify service PATH and working directory with one actual existing tool. |
| Kata | Keep intent and completion evidence in the existing ledger. OpenClaw may retain runtime task IDs and checkpoints; record their relationship without a second manually synchronized task list. A Kata schedule alone does not execute work. |
| Hindsight | Preserve existing repository-bank selection and filtered retention. Verify a synthetic recall/retention round trip through the chosen runtime. If hooks cannot work as configured, document and resolve the integration before claiming full v1 completion; do not silently enable broad transcript retention. |
| Calendar | Perform an authenticated read and verify it against the correct calendar. Live writes require task-specific authority. |
| Browser | Use a dedicated persistent profile and one tested site. Detect login/interaction requirements and report them. Browser success must be established from resulting page/service state. |
| Notifications | Deliver to the owner's configured test conversation. Stay quiet on unchanged monitor state and notify on meaningful changes, completion, failure, or required input. Persist enough observation/delivery state to avoid ordinary duplicate notifications after restart. |

Use supported configuration and narrow wrappers for existing tools before writing custom plugins.
Where a documented capability fails qualification, record the exact version and observed boundary, then try a supported configuration adjustment.
Do not hide a failed requirement by broadening permissions or substituting another runtime without explaining the change.

### Resolve during implementation

These are technical qualification steps for the implementing agent, not unanswered product questions for the owner.
Use the selected release's schema/help and a small smoke test to resolve them, then record the effective settings privately.

| Question | Required resolution |
| --- | --- |
| Which CLI/plugin/runtime versions work together? | Choose a supported stable combination with the required native Codex and interaction features. Record exact versions and resolved executable paths. |
| How does managed configuration coexist with plugin installation? | Identify installer-owned state, provision the pinned plugin, and render reproducible non-secret configuration. Check that a second setup preserves auth and conversations. |
| How does the separate OpenClaw workspace execute repository tasks? | Verify a supported working-directory/instruction path using an actual task, without overwriting repository instructions or copying the whole repository into the profile. |
| How are permissions and decisions routed? | Configure native approval delivery to the owner. Ordinary authorized reads and reversible preparation should not require repeated confirmation; platform-required escalation and materially new transaction authority use the interactive path. Do not inherit the old wrapper's unconditional `-a never` as a substitute for testing approvals. |
| How do memory hooks and scheduled tasks behave in this runtime? | Test the actual native-runtime path, including a restart. Preserve the existing filtering and account policy, and record any supported adaptation. |

If a required feature is unavailable, complete independent work and state the failing acceptance case with the smallest concrete alternative.
Do not declare the requirement satisfied by documentation alone.

Manage the package and persistent service through this repository.
Keep host assignments and settings in the private input, following [module ownership](development.md#ownership-and-layout).
Credentials, authentication sessions, browser profiles, conversations, and scheduler state stay outside Git and the Nix store.

## Package choice

Start on macOS with the Homebrew formula declared through nix-darwin:

```nix
homebrew.brews = [ "openclaw-cli" ];
```

Put the declaration in the private host module if only one machine should run it.
The formula supplies the `openclaw` executable and its Node dependency.
The separate `openclaw` cask is the desktop application and is optional for a Telegram pilot.
As of this review, the [Homebrew formula](https://formulae.brew.sh/formula/openclaw-cli) provides version 2026.9.2.

The upstream [nix-openclaw module](https://github.com/openclaw/nix-openclaw) remains an option for fully Nix-packaged deployment.
However, revision `5cbb2f1bdaf89575076cf95e9cee59c851c967fe` pins OpenClaw to `2026.7.1-2` and its Codex plugin to `2026.7.1`.
That plugin pins Codex `0.144.3`, while the September OpenClaw runtime documentation specifies managed Codex `0.153.4`.
Do not apply September configuration examples to that default package without checking compatibility.
[Pinned source](https://github.com/openclaw/nix-openclaw/blob/5cbb2f1bdaf89575076cf95e9cee59c851c967fe/nix/sources/openclaw-source.nix), [pinned Codex plugin](https://github.com/openclaw/nix-openclaw/blob/5cbb2f1bdaf89575076cf95e9cee59c851c967fe/nix/generated/openclaw-runtime-plugins/codex.nix).

A Homebrew declaration manages installation intent; it is not a fully hermetic Nix package pin.
Check the formula and installed executable version at deployment, and record them together with the Codex plugin version.
Review any tap update separately because this repository enables Homebrew upgrades during activation.

## Run a foreground trial

First install only the CLI through the normal [build and apply workflow](development.md#build-and-apply).
Use a separate named OpenClaw profile and a dedicated workspace for the trial.
The CLI's `--profile <name>` option selects separate state and configuration paths.
Run guided onboarding in that profile, select a local gateway, and decline daemon installation during this stage.
Verify the installed release's onboarding options before automating them.
[CLI profiles](https://docs.openclaw.ai/cli), [onboarding](https://docs.openclaw.ai/cli/onboard).

Choose the native Codex runtime and install the matching official Codex plugin in the trial profile.
Use existing ChatGPT authentication through the supported Codex setup; an API-billed route is a separate choice.
OpenClaw's default Codex home is agent-scoped.
Sharing the operator's native home requires explicit `appServer.homeScope: "user"` configuration and verification of the existing plugins and hooks.
Keep independent writers on separate native threads.
[Codex harness](https://docs.openclaw.ai/plugins/codex-harness).

Create a separate test bot through [BotFather](https://t.me/BotFather). Provide its token through a local secret prompt or file reference, and restrict direct messages to the owner's numeric identity.
Disable group access for the pilot.
Keep one poller per bot token.
Bind the gateway to loopback and use gateway authentication; Telegram long polling does not require an inbound public endpoint.
[Telegram setup](https://docs.openclaw.ai/channels/telegram), [gateway](https://docs.openclaw.ai/cli/gateway).

After configuring the named profile, these commands validate it and run the gateway in the foreground:

```bash
openclaw --profile pilot config validate
openclaw --profile pilot gateway run --bind loopback
```

Use the same profile for plugin, authentication, and diagnostic commands.
An explicit custom state/config environment can override profile defaults, so check the effective paths before onboarding.

## Make the tested configuration persistent

Once the foreground trial passes, add a small private module for the desired OpenClaw settings and launchd service.
The module should run the foreground gateway command with explicit paths, working directory, restart behavior, and owner-only logs/state.
Use one service manager; do not also run Homebrew services or OpenClaw's daemon installer.

Keep desired configuration separate from runtime auth and plugin-install metadata.
Determine which files the selected plugin installer writes before making the production configuration immutable.
OpenClaw's Nix mode can enforce immutable configuration, but also disables plugin install/update commands.
Provision pinned plugins before enabling that mode, or package their verified roots declaratively.
Do not mix an immutable configuration with an installer that expects to rewrite it.
[Nix mode](https://docs.openclaw.ai/install/nix), [plugin management](https://docs.openclaw.ai/cli/plugins).

A runtime helper can obtain credentials from the host credential store and supply file or environment references.
Secret values must never be interpolated into Nix-generated files or command-line arguments.
Capture any browser permissions and login prerequisites in the private deployment notes.

Start with one agent, one browser profile, and one useful workflow.
Reuse the existing task ledger and memory policy where compatible.
Additional channels, voice calls, external skill catalogs, and extra memory engines can be added when a specific task needs them.

## Acceptance and handoff

Verify a real Telegram response, a follow-up in the same conversation, and an authenticated read such as the next calendar event.
While work is running, test a correction, an approval decision, and a stop request.
Test a scheduled notification across a gateway restart, including duplicate suppression.
Browser actions need an explicit expected result and verification of that result.

Record package/runtime versions, active service identity, effective configuration paths, credential wiring, and test evidence privately.
Only then replace an existing bot gateway if replacement is the chosen deployment scope.
Disabling a service preserves its conversations and state; removing runtime data is a separate action.

## Implementation phases

1. Inspect the live baseline and managed sources, including existing gateway, package resolution, credentials wiring, Codex configuration ownership, and memory hooks.
   Verify version-sensitive schema and commands against the selected release and its CLI help.
   The versions above are research observations, not permission to assume they remain current.
2. Add the host-scoped package declaration and setup/run helpers in the private overlay.
   Build without activation, then activate when deployment is in scope.
   Obtain any new token through a local no-echo setup flow; never request that the owner paste it into the conversation.
   Continue source and build checks while any required user login or bot creation is pending.
3. Qualify one foreground profile with the native Codex runtime, test Telegram identity, loaded instructions, and calendar read.
   Use a finite foreground process owned by the session and stop it before starting the managed service.
   Capture proven configuration in managed sources, with runtime auth/plugin state kept separate.
4. Add launchd persistence, task controls, the dedicated browser, and the scheduled-check workflow.
   Verify memory/ledger behavior and state backup coverage.
   Complete the matrix below against the installed service, then record the actual deployment and remaining limitations privately.

Use the repository's build, commit, lock-update, and activation rules.
Preserve unrelated staged and unstaged work, and do not treat pre-existing staged changes as yours to commit.
When a pinned private input is involved, distinguish a temporary override from an ordinary reproducible deployment.
No commit, push, or deployment should be claimed unless performed and verified.

## Acceptance matrix

Record each result as PASS, FAIL, or NOT RUN with the observed version, time, and concise evidence.
Use synthetic content where possible and keep personal results in the private record.

| ID | Test | Required evidence |
| --- | --- | --- |
| A1 | Validate configuration and build the affected target. | Schema validation and build succeed; installed CLI/plugin/runtime versions match the qualified combination. |
| A2 | Start the managed service with the test bot. | One service and one poller; a real Telegram-to-Codex response; existing gateway remains healthy. |
| A3 | Send a follow-up and then a separate task. | Follow-up retains context; independent work does not overwrite or concurrently mutate another native thread. |
| A4 | Read the calendar and run an existing repository helper. | Correct account/calendar result and a real helper result under the service's environment; intended repository instructions are effective. |
| A5 | Run a harmless long task, correct it, then stop it. | Correction affects the active task; cancellation reaches the worker; report any detached work rather than claiming it stopped. |
| A6 | Exercise an approval checkpoint with a reversible fixture. | Approve executes once; deny and expiry execute nothing; changed action cannot reuse the old decision. |
| A7 | Schedule a finite synthetic availability watch. | Unchanged state is quiet; a change produces one notification; restart does not duplicate the observed change; test job expires or is removed afterward. |
| A8 | Interrupt a fixture between action and acknowledgement. | Reconciliation or explicit uncertainty replaces blind replay; no duplicate fixture action. |
| A9 | Use the dedicated browser and reopen its session. | Profile separation, expected persistence, and a verified reversible action; report authentication requirements. |
| A10 | Check Kata and Hindsight using synthetic task content. | Intent/completion evidence is retrievable; memory uses the expected repository bank and retention policy without secret or raw-tool leakage. |
| A11 | Restart the installed service and inspect storage. | Service recovers, context/state remains usable, protected files have appropriate ownership, and backup coverage is verified for persistent deployment. |
| A12 | Complete one useful owner-selected workflow. | End-to-end result with evidence, required user interventions, and observed limitations. Use the private overlay's default when no alternative is supplied. |

A missing login or unperformed phone test is NOT RUN, not PASS.
Do not describe v1 as fully deployed while a required acceptance case remains unresolved.
If the session ends early, update the implementation issue's attention and leave a precise next command/action plus the blocking fact in the private progress record.
Use the repository's scheduling or review convention for remaining work, without inventing a recurring automation.

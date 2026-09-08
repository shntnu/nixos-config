# Working in nixos-config

`CLAUDE.md` links to this file; both products use the same instructions.
Complete action requests within their scope, using prior decisions and authorization.
User instructions take precedence over skill defaults.
Preserve existing work; do not reset, discard, stash, overwrite, or amend commits without authorization.
When told to stop, stop mutations and report the state before attempting recovery.
A request to review or build alone does not authorize activation, sending, publishing, or merging a pull request.
If an instruction causes a pause, link and quote the exact rule and explain why it applies.

## Ownership and documentation

Nix source lives in `flake.nix` and the matching modules.
This repository owns Darwin systems and standalone Linux Home Manager profiles; Linux system configuration belongs to its separate repository.
Read [docs/development.md](docs/development.md) for Nix changes, builds, activation, or module ownership questions.

Keep READMEs as short introductions and indexes, agent rules here, and reusable workflows in `docs/`.
Keep durable project guidance shared; do not substitute agent-private memory.
Record new general gotchas in `LEARNING_LOG.md`.
Host roles, service locations, endpoints, private paths, credentials wiring, backup topology, personal corpora, and live deployment records belong in the private input's documentation.
Public Markdown must describe reusable behavior with placeholders; do not reconstruct private configuration from modules, logs, or prior sessions.
A public host key does not authorize publishing private service assignments.
Consult the matching private module and deployment notes before changing host-specific behavior.
Keep actual credentials out of both repositories and the Nix store.

## Verification and handoff

For documentation-only changes, check the diff and referenced paths; no Nix build or activation is needed.
For Nix changes, inspect the working tree and run `git add .` before building because Git-backed flakes omit untracked files.
Build the affected host without activation first, using [the platform workflow](docs/development.md#build-and-apply).
Shared module changes require coverage of both Darwin and headless consumers.
Apply when activation is in scope, using that platform's workflow.
For installation or service changes, verify the active executable or service on every requested host; a successful build does not prove running processes use it.
Run `git diff --check` and checks appropriate to changed behavior; broaden or repeat only for new changes, failures, or unresolved concerns.
At handoff, distinguish local, committed, pushed, built, and activated state, and name remaining restart or deployment steps.

## Conditional workflows

- This repository uses Kata as its shared work ledger.
  For repository work, run `direnv exec . kata quickstart` at session start and read [Kata workflow](docs/agent-workflows.md#kata-issue-tracker).
  Search before creating, close only verified work, and keep `work.*` metadata truthful on issues you work.
  Never delete or purge issues without explicit user authorization.
- Third-party skills are project-local, installer-owned, and ignored; track `skills-lock.json` as inventory, not a reproducible lock.
  Before skill installation or updates, read [the exact replay and maintenance procedure](docs/agent-workflows.md#third-party-skills).
  Never install globally as a fallback.
- Write plain, precise prose with complete sentences and ASCII punctuation, without rhetorical filler or invented compounds.
  For substantial prose drafting or restructuring, read [WRITING.md](WRITING.md).
  Small edits can follow the surrounding style; the full guide and its examples are not required for a typo fix.

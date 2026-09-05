# AGENTS.md

This file provides guidance to coding agents when working with code in this repository.
`CLAUDE.md` is a symlink to this file, so both agents read the same guidance.

Read and follow `CONSTITUTION.md` for baseline operating principles and `WRITING.md` for prose style.
Direct user instructions and the more specific guidance in this file override both.

@CONSTITUTION.md
@WRITING.md

## Execution and handoff

Treat action requests such as "help me" or "can you fix" as instructions to implement and verify the requested change.
Resolve routine choices from the existing configuration and state material assumptions.
Carry unfinished authorized work through follow-up questions, incorporating corrections without restarting completed steps.
If approval is required, finish independent inspection, preparation, and validation first, then present the exact remaining action.
Do not ask again for authorization already provided in the conversation.

User instructions take precedence over skill guidelines.
If a skill would block requested work, link the exact `SKILL.md`, quote the relevant instruction, and explain whether the restriction is explicit or your interpretation.

## Repository boundaries

Read [docs/development.md](docs/development.md) for the module map, build commands, and update workflows.
Use `flake.nix` and the matching modules as the source of truth for available targets.
This flake owns Darwin systems and standalone Linux Home Manager profiles; Linux system configuration belongs to its separate repository.

Keep each README as a short introduction and index.
Keep agent rules here, reusable workflows and specifications in `docs/`, and general lessons in `LEARNING_LOG.md`.
Do not duplicate module inventories or operating procedures in agent instructions.

Host roles, service locations, endpoints, private paths, credential wiring, backup topology, personal corpora, and live deployment records belong in the private input's documentation.
Public Markdown must describe reusable behavior with placeholders, without reconstructing private configuration from modules, logs, or prior sessions.
An existing public host key is not permission to publish its private service assignments.
Consult the matching private module and deployment notes before changing host-specific behavior.
Keep actual credentials out of both repositories and the Nix store.

## Verification and handoff

For documentation-only changes, check the diff and referenced paths; no Nix build or activation is needed.
For Nix changes, inspect the working tree and run `git add .` before building, because Git-backed flakes omit untracked files.
Build the affected host configuration without activation first, using [the platform workflow](docs/development.md#build-and-apply).
Shared module changes require coverage of both Darwin and headless consumers.

Apply changes when activation is in scope, using the correct platform workflow.
A request to build or review alone does not authorize activation.
For installation or service changes, verify the active executable or service after activation on every requested host.
A successful build does not prove that running processes use the new configuration.

Run `git diff --check` and any checks appropriate to changed behavior.
Once checks pass, repeat or broaden them only for new changes, failures, or unresolved concerns.
At handoff, distinguish local edits, committed or pushed changes, built configurations, and activated hosts.
Name any remaining restart or deployment step explicitly.

Record new general gotchas in `LEARNING_LOG.md`; keep host-specific incidents in the private operations record.

<!-- BEGIN KATA (managed by `kata init --with-agents`) -->
## kata issue tracker

This project uses [kata](https://github.com/kenn-io/kata) as its shared issue
ledger. Run `kata quickstart` at the start of each session for the full agent
contract. The short version:

- Search before creating: `kata search "<keywords>" --agent`.
- Prefer updating existing issues over duplicates (`kata comment`, `kata label add`, `kata edit`).
- Default to `--agent` for ordinary reads and mutations; use `--json` only when a script needs structured data.
- Close only verified work: `kata close <ref> --done --message "<scope + verification>" --commit <sha>`.
- If work is incomplete, label `needs-review` and comment what remains rather than closing.
- Never `kata delete` or `kata purge` without explicit user authorization.

## kata work.* conventions (agent orchestration)

When working a kata-tracked issue, keep its `work.*` metadata truthful
(see <https://katatracker.com/operations/agent-orchestration/> for the full recipe):

- On claim/start: `kata meta set <ref> work.attention ok`; if the work has a
  dedicated branch, stamp it once with `kata meta set <ref> work.branch <branch>`.
- Signal live state: `kata meta set <ref> work.attention stuck|needs-human|ok`
  plus a one-line `work.attention_msg` saying why. Raise `stuck` when you cannot
  proceed, `needs-human` when you want review; clear back to `ok` when unblocked.
- Never stop with the signal stale: close the issue, or leave the attention
  pair reflecting the hand-off.
- Coordinators read `work.*` on issues they delegated; only the working agent
  writes them. `work.*` on closed issues is meaningless.
<!-- END KATA -->

## Third-party skills

Third-party skills are installed per project, never globally.
The canonical policy is `~/.local/share/chezmoi/AGENTS.md`; the procedures are `~/.agents/docs/skills.md`.

`skills-lock.json` is tracked as an inventory and drift record.
The installer owns `.agents/skills/<name>/` and the matching `.claude/skills/<name>` link, so both are ignored rather than committed.
`skills-lock.json` records a content hash but does not pin an upstream revision, so it is not a reproducible lock.

To restore the skills in a fresh clone, replay the exact install command:

```bash
npx skills@1.5.20 add docwriter-org/plain-writing-skill \
  -s plain-writing \
  -a claude-code \
  -a codex \
  -y
```

The `skills` version is pinned because install and link behavior changes between releases.
Upgrade only after testing install, reinstall, and link behavior in an isolated repository.
Do not use `skills update -p` or `experimental_install`; in 1.5.20 the latter restores every entry under `.agents/skills` only, which loses the Claude Code links.

## Writing

Prose in this repository follows [`WRITING.md`](./WRITING.md).
It is a vendored copy of the `plain-writing` skill body, committed so that this file can import it and the rules are always in context rather than waiting for the skill to trigger.
The installed skill at `.agents/skills/plain-writing/` is gitignored, so it cannot be imported from a fresh clone; the vendored copy exists for that reason and still carries its MIT notice and source hash.
Keep the two in step: after replaying the install command above, copy the new skill body back into `WRITING.md`, above the provenance footer.

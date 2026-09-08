# Conditional agent workflows

Read the relevant section when working with Kata or maintaining this project's skills and writing guide.
Commands below run from the repository root.
Run noninteractive Kata commands through `direnv exec .`.
If its shell does not provide authentication, inspect the Nix shell wrapper and use its existing Kata-only credential launcher; do not print credentials or place them in tracked environment files.

## kata issue tracker

This project uses [kata](https://github.com/kenn-io/kata) as its shared issue ledger.
Run `kata quickstart` at the start of each session for the full agent contract.
The short version:

- Search before creating: `kata search "<keywords>" --agent`.
- Prefer updating existing issues over duplicates (`kata comment`, `kata label add`, `kata edit`).
- Default to `--agent` for ordinary reads and mutations; use `--json` only when a script needs structured data.
- Close only verified work: `kata close <ref> --done --message "<scope + verification>" --commit <sha>`.
- If work is incomplete, label `needs-review` and comment what remains rather than closing.
- Never `kata delete` or `kata purge` without explicit user authorization.

## kata work.* conventions (agent orchestration)

When working a kata-tracked issue, keep its `work.*` metadata truthful (see <https://katatracker.com/operations/agent-orchestration/> for the full recipe):

- On claim/start: `kata meta set <ref> work.attention ok`; if the work has a dedicated branch, stamp it once with `kata meta set <ref> work.branch <branch>`.
- Signal live state: `kata meta set <ref> work.attention stuck|needs-human|ok` plus a one-line `work.attention_msg` saying why.
  Raise `stuck` when you cannot proceed, `needs-human` when you want review; clear back to `ok` when unblocked.
- Never stop with the signal stale: close the issue, or leave the attention pair reflecting the hand-off.
- Coordinators read `work.*` on issues they delegated; only the working agent writes them.
  `work.*` on closed issues is meaningless.

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

Prose in this repository follows [`WRITING.md`](../WRITING.md).
It is a vendored copy of the `plain-writing` skill body, committed so agents can read it for substantial writing without depending on an installed skill.
The installed skill at `.agents/skills/plain-writing/` is gitignored, so it cannot be imported from a fresh clone; the vendored copy exists for that reason and still carries its MIT notice and source hash.
Keep the two in step: after replaying the install command above, copy the new skill body back into `WRITING.md`, above the provenance footer.

## Baseline reference

[`CONSTITUTION.md`](../CONSTITUTION.md) records the baseline used when these instructions were authored.
It is retained with its attribution for instruction maintenance and harness comparison; it is not an automatic import.
Repository constraints live in `AGENTS.md`.

# Zvec-Grep evaluation for Nix-managed lab environments

Zvec-Grep works on Spirit and usefully retrieves conceptually related code, but its current packaging and resource costs do not justify making it a shared default.
A bounded opt-in pilot on one host and one or two large repositories is the appropriate next step.
The pilot should retain `rg` for exact searches and should not use Zvec-Grep's imperative installer against managed Codex configuration.

The evidence applies to a September 4, 2026 runtime trial, not to a reproducible Nix package or production deployment.

## Question and scope

This evaluation asked whether Zvec-Grep runs in our Nix-managed environment, retrieves useful code, and has acceptable operational costs for lab use.
[Zvec-Grep](https://zvec.org/en/blog/2026-08-28-zvec-grep-open-source/) is a local-first repository search tool that combines lexical and vector retrieval, then fuses their rankings.
It also includes ripgrep for literal and regular-expression searches and can expose search through the Model Context Protocol (MCP).
The [upstream architecture](https://github.com/zvec-ai/zvec-grep/blob/7d73ca1b5d845dc46ad6afb19d1fc545878e1504/docs/05-architecture.md) describes the retrieval pipeline and the per-workspace `.zvec-grep/` index.

The runtime test used Spirit, an `x86_64-linux` NixOS server, with Node.js 24.19.0 and npm 11.17.0 from the existing Home Manager profile.
The tested package was [`@zvec/zvec-grep` 0.2.1](https://github.com/zvec-ai/zvec-grep/blob/7d73ca1b5d845dc46ad6afb19d1fc545878e1504/package.json), which requires Node.js 22 or newer and uses the Apache-2.0 license.
Upstream source was inspected at commit [`7d73ca1b`](https://github.com/zvec-ai/zvec-grep/commit/7d73ca1b5d845dc46ad6afb19d1fc545878e1504).

The evaluation covered CLI indexing and querying, local embedding models, incremental indexing, the persistent server, an actual MCP exchange, the Codex installer, disk use, and process memory.
It did not cover Apple Silicon runtime behavior, a hermetic Nix derivation, sustained concurrent use, remote embedding providers, or comparative agent task completion.

## Test design

The evaluation installed Zvec-Grep into a disposable npm prefix through `direnv exec .`, preserving the existing Home Manager profile.
The default `local/potion-code-16m-v2` model supplied embeddings locally after its initial download.
A second run compared `local/potion-retrieval-32m` with the default model.

The retrieval test used two corpora with different sizes and purposes.
The small corpus was a clean snapshot of this `nixos-config` repository.
The larger corpus was a tracked-file snapshot of the JUMP production repository.
The test did not modify either source repository.

The corpus coverage excluded several formats that occur in scientific repositories.
The [documented pipeline](https://github.com/zvec-ai/zvec-grep/blob/7d73ca1b5d845dc46ad6afb19d1fc545878e1504/docs/04-pipeline.md) does not list Nix among its structurally parsed languages, so Nix files received generic text chunking.
The pipeline also skips formats such as PDF, Office documents, archives, and databases; the larger scan skipped one ZIP archive.

Each corpus received ten repository-specific questions written after inspecting its contents.
For each question, the endpoint was whether the expected file appeared first or within the first five results.
These post-hoc questions test whether semantic retrieval can recover known relevant files; they do not estimate performance on unseen repositories or establish a general accuracy rate.

The evaluation left no deployed service or active test state.
The disposable daemon was stopped, and its packages, models, indexes, and repository snapshots were moved to trash.

## Zvec-Grep retrieved the expected file for most questions

The npm distribution indexed both corpora and completed semantic searches through the CLI and MCP.
The default model placed the expected file among the first five results for 9 of 10 questions in each corpus.

| Corpus | Indexed files | Chunks | Tool-reported initial indexing time | Final index size | Expected file first | Expected file in top five |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `nixos-config` | 30 | 251 | 2.8 s | 3.9 MiB | 7/10 | 9/10 |
| JUMP production snapshot | 275 | 16,849 | 28.3 s | 91 MiB | 6/10 | 9/10 |

Conceptual questions produced the clearest retrieval benefit.
Zvec-Grep often found the intended implementation when the query described behavior without using the repository's exact identifiers or file names.
Whether this behavior reduces repeated `rg`, open, and reformulate cycles is the main benefit that a real-use pilot should measure.

The TERMINFO miss shows why exact configuration questions still require `rg`.
Both local models missed a question about the TERMINFO configuration, even though the relevant text was easy to locate with a literal search.
This miss supports a complementary workflow in which Zvec-Grep discovers concepts and `rg` locates and confirms exact text.

The larger local model yielded little benefit on this small comparison.
Changing from the default 16-million-parameter code model to the 32-million-parameter retrieval model improved first-place retrieval from 7 of 10 to 8 of 10 questions in `nixos-config`, while top-five retrieval remained 9 of 10.
That one-question change does not justify selecting the larger model without a longer trial on real searches.

## A persistent MCP process made searches fast after startup

Warm persistent-MCP searches returned in approximately 16 to 24 milliseconds after the model and index were loaded.
The first search took approximately 0.65 seconds, while separate one-process CLI searches took 1.4 to 1.6 seconds because each command paid process and model startup costs.

The MCP command configured for Codex also worked with an independent protocol client.
An MCP client initialized successfully, listed the default `zvec_grep_search` tool, and retrieved the intended Hindsight documentation in a live tool call.

Incremental indexing avoided rescanning unchanged content but still imposed noticeable fixed overhead for a changed repository.
A no-change reindex took 0.13 seconds inside Zvec-Grep and 1.87 seconds end to end.
Adding one small file took 4.35 seconds inside Zvec-Grep and 8.43 seconds end to end.
Process startup and changed-index work therefore remained material even when content comparison was cheap.

## The stock package consumed substantial disk and memory

The stock npm dependency tree occupied 1.6 GiB, which is too large for an unexamined shared-profile dependency.
Large contributors included `node-llama-cpp`, ONNX Runtime, and native artifacts for CUDA, Vulkan, multiple platforms, image handling, and parsing.
This measurement describes the installed npm tree, not a demonstrated minimum installation size.

The default embedding model added approximately 32 MiB to the model cache.
Caching both tested models increased that cache to 157 MiB.
The larger repository's final index occupied 91 MiB after compaction, compared with 3.9 MiB for `nixos-config`.

The persistent daemon retained approximately 0.6 GiB of private memory after a query.
Its resident set size was approximately 126 MiB before searching, 663 MiB after searching `nixos-config`, and 722 MiB after searching the larger corpus.
A direct CLI query reached approximately 634 MiB peak resident memory.
The pilot must determine whether this working set is acceptable on shared servers; it is disproportionate to occasional searches in a small repository.

## Runtime compatibility does not yet establish reproducible Nix packaging

Zvec-Grep ran successfully with the Nix-managed Node.js runtime on Spirit.
That result establishes practical `x86_64-linux` runtime compatibility in the current profile, but the disposable npm installation did not prove that `nix build` can construct the package offline and reproducibly.

The native dependency chain creates the main packaging risk.
The prebuilt Zvec Node binding loaded during the trial even though a standalone `ldd` check could not resolve `libstdc++.so.6`.
A Nix derivation will probably need `buildNpmPackage`, `autoPatchelfHook`, explicit C++ runtime libraries, and checks for the prebuilt `.node`, `.so`, and bundled ripgrep binaries.

The npm installation also warned that npm 11 had blocked lifecycle scripts for Zvec, ONNX Runtime, `sharp`, `node-llama-cpp`, and `protobufjs`.
The tested default path still worked, but a Nix build must determine whether optional or future functionality depends on those scripts.

A minimal default-Model2Vec packaging spike should test whether `node-llama-cpp` can be omitted without breaking the tested path.
The installed `@node-llama-cpp` platform-package subtree occupied approximately 703 MiB; omitting `node-llama-cpp` and those transitive artifacts was not tested and would forfeit the GGUF embedding options.
A blanket npm `--omit=optional` remains unsuitable because Zvec and ripgrep also obtain required platform bindings through optional dependencies.

Model files form a separate reproducibility boundary.
The local Model2Vec catalog pins Hugging Face revisions and supports a writable `ZVEC_GREP_MODEL_CACHE`, so a later package could fetch models as fixed-output derivations.
The first pilot should instead keep the cache outside the Nix store and treat the one-time model download as an explicit runtime step.
The [embedding documentation](https://github.com/zvec-ai/zvec-grep/blob/7d73ca1b5d845dc46ad6afb19d1fc545878e1504/docs/07-embedding.md) describes the local and remote model choices.

The published Zvec binding matrix covers the architectures currently deployed here, although only Spirit was tested.
Upstream publishes native bindings for Linux on x86-64 and ARM64 and for macOS on ARM64, which covers the lab servers and Apple Silicon Macs in this repository.
A package exposed through [all flake systems](../flake.nix) would need to guard or mark unsupported the `x86_64-darwin` target, for which upstream does not currently publish a prebuilt binding; a profile-only integration would not evaluate that target.

## Managed configuration should replace the upstream installer

The upstream Codex installer was idempotent and preserved unrelated content in an isolated test, but its imperative write path does not fit this environment.
It added one MCP configuration block and one global instruction block.
When it encountered a running daemon with an incompatible toolset, however, it wrote the configuration before reporting the error, so the operation was not transactional.

The durable integration should package `zg` and declare its MCP configuration without running `zg install` during Home Manager activation.
The installer writes `~/.codex/config.toml` and `~/.codex/AGENTS.md`, while chezmoi owns durable configuration under `~/.codex` in this environment.
The [agent integration documentation](https://github.com/zvec-ai/zvec-grep/blob/7d73ca1b5d845dc46ad6afb19d1fc545878e1504/docs/01-agents.md) describes the files that the installer changes.

Repository indexes also need an explicit ownership rule.
Zvec-Grep stores an index in `.zvec-grep/` at each workspace root, and the trial showed that this directory appears as untracked content unless the repository or global Git ignore policy excludes it.
Indexes should remain mutable runtime data outside Git and outside the Nix store.

## Shared servers require an authentication decision

The default loopback daemon does not meet the lab's multi-user threat model without authentication.
Cross-account access was not tested, but loopback normally restricts access to the host rather than to one local account.
The [server documentation](https://github.com/zvec-ai/zvec-grep/blob/7d73ca1b5d845dc46ad6afb19d1fc545878e1504/docs/06-server.md) supports bearer authentication but leaves it disabled by default.
A persistent deployment on Spirit, Oppy, or Karkinos should therefore require a bearer token stored outside Git and the Nix store.
Users who do not want a daemon can run indexed CLI searches in direct mode, but the current MCP integration still requires the local server.

Local embeddings preserve the strongest data boundary.
Scanning, chunking, embedding, indexing, and querying remained local during this evaluation after the model download.
Remote embeddings were not tested because they would send repository or query text to a provider and require a separate data-governance decision.

## Upstream evidence supports experimentation rather than broad adoption

Upstream describes Zvec-Grep as early-stage software, and its current roadmap still lists installation lifecycle, concurrency, service recovery, diagnostics, and index compatibility as areas under development.
These open contracts increase the maintenance burden of carrying a Nix package today.
The [roadmap](https://github.com/zvec-ai/zvec-grep/blob/7d73ca1b5d845dc46ad6afb19d1fc545878e1504/docs/08-roadmap.md) should be checked again before promoting a pilot to shared infrastructure.

The upstream benchmark results are promising but do not replace a local trial.
The published BrowseComp results report reduced input tokens, tool calls, and agent time, but the headline run used a remote Qwen embedding model and excluded index preparation.
The benchmark is also vendor-run and depends on stochastic agent decisions.
The [benchmark documentation](https://github.com/zvec-ai/zvec-grep/tree/7d73ca1b5d845dc46ad6afb19d1fc545878e1504/benchmarks) provides the design and reported results.

## Recommended pilot

A useful next step is a reversible pilot with explicit success and stop criteria.
The pilot should use these constraints:

- Package the tested path by pinning Zvec-Grep 0.2.1, testing a minimal default-Model2Vec Nix derivation with native-library fixups, and keeping its writable model cache outside the Nix store.
- Integrate through the existing declarative owner, exclude `.zvec-grep/` from Git, and require bearer authentication for MCP on shared hosts; use direct CLI mode when no daemon is desired.
- Retain `rg` for exact work and record approximately 25 genuine conceptual-navigation tasks in one or two large repositories.

Broader adoption should require a clear benefit on real lab work.
For each task, the user should record whether the first semantic query returned a relevant file among the first five results, whether discovery required query reformulation or fallback to `rg`, elapsed time, and query and file-open actions.
A task should count as a Zvec-Grep win when it reaches a relevant file without semantic-query reformulation or an `rg` discovery fallback; later `rg` confirmation does not count as fallback.
A reasonable promotion threshold is a win on at least half of the recorded tasks without unacceptable memory, storage, or indexing overhead.
Failure to meet that threshold should end the pilot and leave Zvec-Grep as an on-demand tool rather than a managed service.

## Conclusion

Zvec-Grep is promising enough to pilot and too immature to make a shared default.
The Spirit trial demonstrated useful semantic retrieval, low warm-query latency, successful MCP transport, and Codex registration within the existing Nix-managed runtime.
A bounded pilot can now determine whether those benefits survive ordinary lab work and justify the cost of a maintained Nix package.

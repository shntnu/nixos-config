# Repository guidance

Read `CLAUDE.md` for repository architecture and `docs/kata.md` before changing Kata packaging, configuration, or documentation.
Never commit Kata tokens or place them in Nix store paths.
Preserve the live Kata database and ledger.
Verify protected access with the correct token and prove that missing and deliberately wrong tokens are rejected without printing any credential.

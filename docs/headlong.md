# Headlong with Tinker

I run [Headlong](https://github.com/laude-institute/headlong) locally in Docker on macOS.
The installation is managed imperatively with Docker rather than Nix.
The dashboard listens only on `127.0.0.1:8080`, and a Docker volume stores the persistent state.

The current local image contains Headlong commit `87d4e7916b4b2fbb2cf1601fd8cfd20b32191ddc`.
The image also contains a local dashboard path fix, so this note is a record of the installation rather than a reproducible build.

## Tinker configuration

The installation uses [Tinker's API that is compatible with the OpenAI API](https://tinker-docs.thinkingmachines.ai/tinker/compatible-apis/openai/) and the `openai/gpt-oss-20b` model.

```dotenv
SHELLM_MODEL=openai/gpt-oss-20b
LLM_API_URL=https://tinker.thinkingmachines.dev/services/tinker-prod/oai/api/v1/chat/completions
SHELLM_API_URL=https://tinker.thinkingmachines.dev/services/tinker-prod/oai/api/v1/chat/completions
OPENROUTER_API_KEY=<Tinker API key>
```

`OPENROUTER_API_KEY` contains a Tinker key.
The variable name is a Headlong compatibility detail because the slash form model name selects Headlong's OpenRouter request format.

Both URL variables are required by this Headlong revision.
The direct `llm` command reads `LLM_API_URL`, while the persistent `shellm` process reads `SHELLM_API_URL`.

The key is stored outside Git and is never included in this document or the image.
The identity, conversations, local secret path, and volume contents are also private.

## Limits

Headlong is alpha software that runs model generated shell commands and can call the model continuously.
I use a dedicated key with a spending limit.

Tinker describes its compatible inference API as beta and intended for testing and low traffic internal use.
The [upstream Headlong documentation](https://github.com/laude-institute/headlong) covers installation and lifecycle commands.

# Headlong with Tinker

Provider compatibility notes for [Headlong](https://github.com/laude-institute/headlong) revision `87d4e7916b4b2fbb2cf1601fd8cfd20b32191ddc`.

## Tinker configuration

To use [Tinker's API that is compatible with the OpenAI API](https://tinker-docs.thinkingmachines.ai/tinker/compatible-apis/openai/) and the `openai/gpt-oss-20b` model, configure:

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

Keep the key outside Git and the image.

## Limits

Headlong is alpha software that runs model generated shell commands and can call the model continuously.
Use a dedicated key with a spending limit.

Tinker describes its compatible inference API as beta and intended for testing and low traffic internal use.
The [upstream Headlong documentation](https://github.com/laude-institute/headlong) covers installation and lifecycle commands.

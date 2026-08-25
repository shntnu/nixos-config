# Run a persistent Headlong agent in a pinned Docker container

[Headlong](https://github.com/laude-institute/headlong) is an open source agent harness that keeps an identity active between messages.
The agent calls a language model continuously, writes its memory and trajectory to local state, and runs model-generated shell commands.
The container in this specification confines those commands to Docker and exposes the dashboard only on the host loopback interface.

The tested source is Headlong commit [`87d4e7916b4b2fbb2cf1601fd8cfd20b32191ddc`](https://github.com/laude-institute/headlong/tree/87d4e7916b4b2fbb2cf1601fd8cfd20b32191ddc) from August 24, 2026.
Headlong had no release or tag at qualification time, so the full commit and the source archive SHA-256 are part of the deployment contract.
The repository includes the [Compose definition](../deploy/headlong/compose.yaml), [image build](../deploy/headlong/Dockerfile), [container entry point](../deploy/headlong/entrypoint.sh), [identity lifecycle helper](../deploy/headlong/lifecycle.sh), and [dashboard wrapper](../deploy/headlong/web-wrapper.sh) used by this specification.

## Give this specification to a coding agent

Give a coding agent this document and identify the target host.
Then say:

> Set up and qualify a persistent Headlong identity from this specification.

> Resolve the deployment values with me, preserve the host configuration model and any existing Headlong state, and run the complete acceptance process in an isolated deployment before changing production.

The agent must read the whole document before changing anything.
It must inspect the host, Docker, existing Headlong artifacts, current configuration management, credential delivery, listener, and durable storage first.
It must ask for any identity text or deployment choice that it cannot derive safely.
It must never infer identity text from unrelated personal files.

The setup instruction authorizes an isolated qualification and the requested deployment.
It does not authorize deleting an existing identity or volume, publishing the dashboard, mounting host files into the agent, exposing the Docker socket, changing network policy, using an uncapped credential, or pushing a repository.

## Required outcome

One named Docker container runs one Headlong identity from one reviewable Compose definition.
The container restarts unless it was deliberately stopped, and Docker stores mutable state in one named volume.
The dashboard is reachable through `127.0.0.1` and is not published on another host interface.

```text
operator chat and dashboard
        |
        v
127.0.0.1:<host-port>
        |
        v
one pinned Headlong container
        |
        +-- one named state volume
        |
        +-- one spend-capped provider key
        |
        +-- outbound HTTPS to the selected model endpoint
```

The image contains the pinned Headlong application and its command links.
The named volume contains the identity, memories, trajectory, generated environment, logs, run files, and dashboard state.
The host supplies one provider key as a Compose secret.

## Resolve the deployment values

Resolve and record these values before building:

- `<container-name>` names the container and defaults to `headlong`.
- `<volume-name>` names the durable state volume and defaults to `headlong-data`.
- `<image-name>` names the locally built image and defaults to `headlong-local:87d4e7916b4`.
- `<host-port>` publishes container port `8080` on `127.0.0.1` and defaults to `8080`.
- `<identity-name>` uses lowercase letters, digits, and hyphens.
- `<model>` is the exact model or checkpoint string accepted by the selected endpoint.
- `<key-variable>` is one of `ANTHROPIC_API_KEY`, `OPENAI_API_KEY`, `GEMINI_API_KEY`, or `OPENROUTER_API_KEY`.
- `<llm-url>` is the complete chat endpoint used by Headlong's direct `llm` command.
- `<shellm-url>` is the complete chat endpoint used by the active `shellm` process.
- `<secret-file>` is an absolute path to a mode `0600` file containing only the provider key.
- `<deployment-env>` is a non-secret Compose environment file.
- `<backup-directory>` is an owner-only directory outside the Docker volume.

Keep the identity name, identity text, operator details, chosen private model, host-specific paths, and credential source in the deployment's private configuration.
The public specification needs placeholders and behavior only.

## Execution rules

Preserve any existing installation until its state has a tested backup.
Do not run Headlong's one-line installer on the host.
Do not run a noninteractive installer until the command is already inside the intended container.
Do not create `~/.headlong`, `~/.headlong-thinkers`, `~/.skills/core-skills`, or Headlong links under `~/.local/bin` on the host.

Use the Compose files from this repository instead of translating the current container into a new command by hand.
Do not replace the pinned Headlong revision, source hash, base image digest, or `uv` checksums without following the upgrade process.
Record the built image digest because Debian package indexes can change between builds even though the base image and downloaded source artifacts are pinned.

Build and qualify with a disposable image name, container name, volume, project name, and host port first.
Do not attach the production volume to a qualification container.
Do not stop, restart, or recreate the production container during isolated qualification.

Never print a credential or put it in Git, the Nix store, a Compose environment file, a process argument, an issue, a chat message, or ordinary logs.
Do not inspect the full container environment or a process command line because provider clients can place authorization headers in child process arguments.
Read only named non-secret fields, and report a key as `present` or `missing`.

## Safety boundaries

Headlong is an autonomous process with continuing API cost and local action authority.
Use a dedicated, spend-capped provider key and monitor provider usage.
Stop the identity or container when continuous thinking is not wanted.

The container grants the agent root access inside its own filesystem and named volume.
It grants outbound network access so the agent can call the provider and other public services.
It does not mount a host workspace, home directory, credential directory, or Docker socket.
It does not publish another inbound port.

The dashboard has no separate authentication boundary in this design.
The fixed `127.0.0.1` binding is therefore an invariant, and remote access requires a separately reviewed authenticated tunnel.

The persistent volume is sensitive.
It contains the provider key, identity prompt, conversations, memory, trajectories, logs, and any files the identity creates under its managed state.
Backups inherit the same sensitivity and must remain owner-only.

## Declarative and mutable boundaries

The following parts are declarative:

- The Compose service name, container name, restart policy, init process, port binding, volume mount, secret mount, and health check are declared in `compose.yaml`.
- The base image digest, Headlong commit, Headlong archive hash, `uv` version, and `uv` archive hashes are declared in the image build.
- The entry point validates and writes the selected model, both endpoint variables, key variable, application path, and container sandbox setting on every start.

The following parts remain mutable:

- Debian packages are resolved from the repository associated with the pinned base image when the image is built.
- The dashboard uses Headlong's locked Python environment and may create its virtual environment on first use.
- Identity creation is an explicit one-time operation because its prompt is personal and mutable.
- Identity memory, trajectory, thinker state, logs, generated environment, and dashboard files live in the named volume.

The image stores Headlong at `/opt/headlong`.
The entry point maps `/opt/headlong/.identities` to `/root/.headlong/.identities` in the volume and records `/opt/headlong` as the active application directory.
The container's `headlong-web` wrapper makes the dashboard scan `/root/.headlong`, where `.identities` is a real directory rather than a symlink.
Upstream dashboard discovery skips symlinked directories, so serving `/opt/headlong` would return HTTP 200 while showing no identities.
On restart, it starts both the monolith and responder because the pinned upstream `persona start` command starts only the monolith.
The source is absent from the mutable volume, which prevents an installer update from silently changing the deployed revision.

## Prerequisites

The host must have a working Docker Engine with Compose support, enough durable storage for the state volume, outbound HTTPS to the model provider, and an unused loopback host port.
Docker Desktop is acceptable on macOS when it already belongs to the host's managed setup.

Before creating anything, record these checks:

```bash
docker version
docker compose version
docker info --format 'os={{.OSType}} arch={{.Architecture}}'
docker container inspect <container-name>
docker volume inspect <volume-name>
lsof -nP -iTCP:<host-port> -sTCP:LISTEN
```

An expected `No such container`, `no such volume`, or empty listener result is acceptable for a fresh deployment.
Existing results require preservation and migration planning.

Record whether each forbidden host path existed before setup:

```text
~/.headlong
~/.headlong-thinkers
~/.skills/core-skills
~/.local/bin/headlong-init
~/.local/bin/headlong-web
~/.local/bin/persona
~/.local/bin/<identity-name>
```

Do not delete a pre-existing path merely because it appears in this list.
Determine its owner and purpose first.

## Secret contract

Create `<secret-file>` with `umask 077` and mode `0600` through the host's approved secret manager.
The file contains the raw provider key and one final newline, with no variable name or surrounding quotes.
The parent directory must be mode `0700`.

The Compose definition mounts the file read-only at `/run/secrets/llm_api_key`.
The entry point reads the secret, validates that it has one nonempty line, and writes the provider variable to `/root/.headlong/.env` with mode `0600`.
Docker container configuration therefore contains the non-secret variable name and endpoint, while the secret value stays out of `docker inspect` configuration output.

The generated state environment is owned by the container and is replaced on each container start.
Change the source secret file and recreate the container to rotate the key.

## Provider and endpoint contract

Native Anthropic, OpenAI, Gemini, and OpenRouter deployments use the provider key variable and endpoint accepted by the pinned Headlong `llm` command.
A slash-form model makes Headlong select its OpenRouter request format, so another OpenAI-compatible provider with slash-form model names uses `OPENROUTER_API_KEY` as a compatibility variable.
The variable name describes Headlong's request path and does not claim that the provider is OpenRouter.

Set both endpoint variables to the intended chat completion endpoint.
The values may be identical, and they must be identical for the tested Tinker-compatible setup.

```text
HEADLONG_LLM_API_URL=<complete-chat-endpoint>
HEADLONG_SHELLM_API_URL=<complete-chat-endpoint>
```

The duplication is required by the pinned upstream behavior.
Headlong initialization validates with `llm`, which reads `LLM_API_URL`.
The active monolith runs through `shellm`, which clears inherited `LLM_API_URL` and restores it only from `SHELLM_API_URL`.
A deployment with only `LLM_API_URL` can pass initialization and then send the credential to the wrong default endpoint.

The tested Tinker-compatible endpoint is:

```text
https://tinker.thinkingmachines.dev/services/tinker-prod/oai/api/v1/chat/completions
```

Tinker documents the OpenAI-compatible API as beta and intended for testing, evaluation, and low internal traffic.
Continuous Headlong use can exceed that intended traffic pattern, so monitor reliability and cost and choose another endpoint when needed.

## Build and initialize

Create `<deployment-env>` with these non-secret values:

```dotenv
HEADLONG_PROJECT_NAME=<compose-project-name>
HEADLONG_CONTAINER_NAME=<container-name>
HEADLONG_VOLUME_NAME=<volume-name>
HEADLONG_IMAGE=<image-name>
HEADLONG_HOST_PORT=<host-port>
HEADLONG_KEY_ENV=<key-variable>
HEADLONG_MODEL=<model>
HEADLONG_LLM_API_URL=<llm-url>
HEADLONG_SHELLM_API_URL=<shellm-url>
HEADLONG_SECRET_FILE=<absolute-secret-file>
```

Run Compose from the repository root:

```bash
compose_file=deploy/headlong/compose.yaml
docker compose --env-file <deployment-env> -f "$compose_file" config --quiet
docker compose --env-file <deployment-env> -f "$compose_file" build --pull headlong
docker image inspect <image-name> \
  --format 'id={{.Id}} revision={{index .Config.Labels "org.opencontainers.image.revision"}} repo_digests={{json .RepoDigests}}'
docker compose --env-file <deployment-env> -f "$compose_file" up -d --no-build
```

The first start has no identity, so the dashboard health check remains unhealthy until initialization.
Run the identity interview inside the container:

```bash
docker compose --env-file <deployment-env> -f "$compose_file" exec headlong headlong-init
```

Enter the private identity and operator text at the prompts.
Do not pass private identity text through process arguments or save it in the public repository.
The provider key and model are already present, so the initializer must validate the selected model and must not ask for another key or replace the model.

The image already contains `uv` and Node.js.
Stop if initialization offers to download another runtime because the running image does not match this specification.

## Normal operation

Use the identity command inside the container:

```bash
docker compose --env-file <deployment-env> -f "$compose_file" exec headlong headlong-identity <identity-name> status
docker compose --env-file <deployment-env> -f "$compose_file" exec headlong persona <identity-name>
docker compose --env-file <deployment-env> -f "$compose_file" exec headlong persona <identity-name> say "hello"
docker compose --env-file <deployment-env> -f "$compose_file" exec headlong headlong-identity <identity-name> stop
docker compose --env-file <deployment-env> -f "$compose_file" exec headlong headlong-identity <identity-name> start
```

Stopping the identity pauses the mind and dashboard but leaves the container running.
Stopping the container pauses every Headlong process and prevents API use until the container starts again.

```bash
docker compose --env-file <deployment-env> -f "$compose_file" stop
docker compose --env-file <deployment-env> -f "$compose_file" start
docker compose --env-file <deployment-env> -f "$compose_file" restart
```

## Verification

A running container, successful initializer, or HTTP response alone does not prove that Headlong works.
Run every check below against the installed deployment.

### Host cleanliness and structure

Compare the forbidden host paths with the recorded baseline and prove that setup created none of them.
Then inspect only non-secret container fields:

```bash
docker inspect <container-name> --format \
  'image={{.Config.Image}} restart={{.HostConfig.RestartPolicy.Name}} init={{.HostConfig.Init}} ports={{json .HostConfig.PortBindings}} mounts={{range .Mounts}}{{.Type}}:{{.Name}}:{{.Destination}} {{end}}'
```

The result must show the pinned local image, `unless-stopped`, init enabled, the expected named volume at `/root/.headlong`, and only `127.0.0.1:<host-port>` mapped to container port `8080`.
Inspect the actual listener with `lsof` or the host's equivalent and confirm that no wildcard or non-loopback listener owns `<host-port>`.
Confirm that the image revision label and `/opt/headlong/.headlong-revision` contain the full pinned Headlong commit.
Confirm that `bash`, `curl`, `git`, `jq`, `node`, `npm`, `uv`, and the Headlong command links are available inside the container.

### Dashboard and direct model health

The dashboard must return HTTP 200 through loopback and must discover the selected identity:

```bash
curl --fail --silent --show-error --output /dev/null \
  --write-out 'dashboard_status=%{http_code}\n' \
  http://127.0.0.1:<host-port>/
curl --fail --silent --show-error \
  http://127.0.0.1:<host-port>/api/identities \
  | jq --exit-status --arg name <identity-name> \
    'any(.[]; .name == $name)' >/dev/null
```

The first request proves that the web process is reachable.
The second request proves that it scans the persistent identity root.

Run one minimal direct request inside the container without printing the key:

```bash
docker exec <container-name> bash -lc '
  source /root/.headlong/.env
  response=$(llm -m "$SHELLM_MODEL" "Reply with exactly DIRECT_OK")
  [[ "$response" == *DIRECT_OK* ]]
  printf "direct_model_health=ok\n"
'
```

### Active dispatcher environment

Read the active dispatcher environment by name and redact the key value:

```bash
docker exec <container-name> bash -lc '
  identity_name=<identity-name>
  pid=$(cat "/root/.headlong/.identities/$identity_name/run/dispatcher.pid")
  for name in SHELLM_MODEL LLM_API_URL SHELLM_API_URL <key-variable>; do
    value=$(tr "\0" "\n" < "/proc/$pid/environ" | sed -n "s/^$name=//p")
    if [[ "$name" == "<key-variable>" ]]; then
      [[ -n "$value" ]] && printf "%s=present\n" "$name"
    else
      printf "%s=%s\n" "$name" "$value"
    fi
  done
'
```

The model and both endpoints must equal the resolved deployment values, and the key must report `present`.
Do not print the complete process environment.

### Monolith and responder

Initialization queues a real monolith wake.
Wait for a durable step from that wake instead of accepting a live dispatcher as proof:

```bash
docker exec <container-name> bash -lc '
  identity_name=<identity-name>
  trajectory=$(find "/root/.headlong/.identities/$identity_name/trajectories" \
    -path "*-root/trajectory.jsonl" -type f -print -quit)
  for attempt in $(seq 1 60); do
    if tail -n 40 "$trajectory" | jq -e \
      "select(.source == \"monolith\" and (.type == \"final\" or .type == \"idle\" or .type == \"thought\" or .type == \"observation\"))" \
      >/dev/null 2>&1; then
      printf "monolith_durable_step=ok\n"
      exit 0
    fi
    sleep 2
  done
  printf "monolith_durable_step=missing\n" >&2
  exit 1
'
```

Send a real one-shot message and require the requested response:

```bash
docker exec <container-name> persona <identity-name> say "Reply with exactly RESPONDER_OK"
```

### False-positive endpoint regression

The Compose contract must reject a deployment that has only the initializer endpoint:

```bash
env -u HEADLONG_SHELLM_API_URL \
  docker compose --env-file <deployment-env-without-shellm-url> \
  -f deploy/headlong/compose.yaml config --quiet
```

The command must fail because `HEADLONG_SHELLM_API_URL` is required.
The active dispatcher check and durable monolith check must also pass, which proves that both runtime paths use the intended endpoint.

### Identity and container lifecycle

Record the identity name, root trajectory ID, model, endpoints, thinker roster, and dashboard status.
Then stop and start the identity:

```bash
docker exec <container-name> headlong-identity <identity-name> stop
docker exec <container-name> headlong-identity <identity-name> start
docker exec <container-name> headlong-identity <identity-name> status
```

Confirm that the same identity, memory files, root trajectory, model, endpoints, monolith, responder, and dashboard return.

Restart the container and repeat the same checks:

```bash
docker restart <container-name>
```

Finally recreate it from Compose without running initialization:

```bash
docker compose --env-file <deployment-env> -f deploy/headlong/compose.yaml \
  up -d --force-recreate --no-build
```

The same identity and state must return after both operations.

## Backup and restore

Pause the identity before copying the volume so all state files are stable:

```bash
docker exec <container-name> headlong-identity <identity-name> stop
docker compose --env-file <deployment-env> -f deploy/headlong/compose.yaml stop
```

Create an owner-only archive with the pinned image:

```bash
umask 077
mkdir -p <backup-directory>
docker run --rm --entrypoint tar \
  -v <volume-name>:/state:ro \
  -v <backup-directory>:/backup \
  <image-name> \
  -C /state -czf /backup/headlong-state.tgz .
shasum -a 256 <backup-directory>/headlong-state.tgz \
  > <backup-directory>/headlong-state.tgz.sha256
chmod 600 <backup-directory>/headlong-state.tgz*
docker compose --env-file <deployment-env> -f deploy/headlong/compose.yaml start
```

The archive contains the provider key and identity data.
Do not print, commit, or attach it to an issue.

Qualify restore with an isolated name, volume, project, and port:

```bash
docker volume create <restore-volume>
docker run --rm --entrypoint tar \
  -v <restore-volume>:/state \
  -v <backup-directory>:/backup:ro \
  <image-name> \
  -C /state -xzf /backup/headlong-state.tgz
```

Start the restored copy with a separate deployment environment that names `<restore-volume>` and an unused loopback port.
Confirm the same identity, memory, trajectory, model, endpoints, monolith, responder, and dashboard.
Stop the restored copy before resuming production so two copies of one identity never think at the same time.

Clean up the restored Compose project and volume only after resolving their exact names:

```bash
docker compose --env-file <restore-deployment-env> -f deploy/headlong/compose.yaml down --volumes
trash <restore-deployment-env>
```

Keep a durable backup according to the owner's retention policy.
Move a disposable qualification archive to Trash after the restore test.

## Upgrade and rollback

Treat every Headlong upgrade as a source and state migration.
First inspect upstream changes and choose one exact commit.
Second compute and review the source archive SHA-256.
Third update the revision, archive hash, and image tag in both the Dockerfile and Compose file.
Fourth create and restore-test a state backup before recreating production.
Fifth build a new image and run the complete isolated acceptance process.

Do not run `curl -fsSL https://headlong.ai/install.sh | bash` to upgrade this deployment.
The installer pulls the current upstream branch into mutable state and would defeat the image pin.

For an application rollback, stop the identity and preserve the current volume.
Build the prior pinned image and test it against an isolated restore of the pre-upgrade backup.
Recreate production with the prior image only after the restore proves that the older code accepts that state.
If state changed incompatibly, restore the pre-upgrade backup instead of attaching older code to newer state.

The original imperative Docker deployment may retain a checkout and identity under `/root/.headlong/app` during migration.
Keep that tree until the declarative deployment and an isolated restore pass.
Its presence is a rollback copy, while `/root/.headlong/.identities` is the active declarative identity root.

## Uninstall

To remove the service while preserving state, run:

```bash
docker compose --env-file <deployment-env> -f deploy/headlong/compose.yaml down
docker volume inspect <volume-name>
```

The named volume and secret source remain.
Re-running `up -d --no-build` restores the service without another identity interview.

Deleting the volume permanently removes the identity, provider key copy, memory, trajectory, and logs.
Require explicit owner approval and a verified backup before running:

```bash
docker compose --env-file <deployment-env> -f deploy/headlong/compose.yaml down --volumes
trash <secret-file> <deployment-env>
```

Inspect the exact container, project, volume, and file names immediately before full removal.

## Failure modes

Initialization can pass while the monolith fails with an authentication error when `LLM_API_URL` is set and `SHELLM_API_URL` is missing.
The required Compose variable, active dispatcher inspection, and durable monolith test detect that state.

A running dispatcher does not prove that a thinker completed work.
Read the durable trajectory and sanitized thinker logs when `persona status` shows a live process but no new step appears.

The pinned upstream `persona start` command starts the monolith but not the responder.
The container entry point starts the responder separately, and the responder acceptance check detects any regression in that restart path.

A dashboard HTTP 200 does not prove identity discovery, model access, or responder behavior.
Require a nonempty identity result from `/api/identities`, and run the direct model, monolith, and responder checks separately.

A recreated container can start with no identity when it uses the wrong or empty volume.
Stop it before initialization, inspect the resolved volume name, and attach the intended state instead of creating a second identity.

An installer prompt to download `uv`, Bun, or Node.js means the built image does not match this specification.
Stop and rebuild the image rather than accepting an unpinned runtime install.

A secret file with extra lines, shell syntax, or a variable name is rejected by the entry point.
Write only the raw key as one line.

## Known limits

Headlong is alpha research software, and the pinned source has no formal release.
The exact source commit passed this acceptance process, while other commits remain unqualified.

The image build pins downloaded source artifacts and the base image digest but does not pin Debian package repository snapshots.
The resulting image is reviewable and versioned, but it is not bit-for-bit reproducible across build dates.
Record and retain the accepted image digest if identical deployment bytes are required.

The deployment uses one root user inside the container.
The container boundary, lack of host mounts, lack of Docker socket, and loopback port reduce host exposure, but they do not make arbitrary model-generated shell commands safe.

The Compose health check covers the dashboard and requires at least one discovered identity.
Provider authentication, monolith progress, and responder behavior require the operational checks in this document.

The state volume holds its own provider-key copy because upstream Headlong loads a shell environment file.
Key rotation requires container recreation, and old backups retain old key material until they are deleted under the owner's retention policy.

## Qualification record

The reference acceptance completed on August 24, 2026, with Docker Desktop on macOS, Docker Engine 29.7.2, Compose 5.4.0, and a Linux `aarch64` container environment.
It used Headlong revision `87d4e7916b4b2fbb2cf1601fd8cfd20b32191ddc` and source archive SHA-256 `d254d1662f6ee139dc85134827a80ec5a3b4ad05c7bd0e478455cc70d6b0017a`.
The accepted production image ID was `sha256:9bfa2df0b217a936a729e452f6958b6c37df9778216c7a0dbf459ff9b8d97534`.

The first isolated run used disposable `headlong-qual-*` names, a unique loopback port, a synthetic identity, the Tinker-compatible provider path, and a slash-form OpenAI-compatible model.
It passed host cleanliness, image and runtime structure, the loopback listener, dashboard health, direct model health, named dispatcher environment checks, a durable monolith step, responder chat, Compose recreation, backup, isolated restore, state-preserving uninstall, and false-positive endpoint rejection.
It exposed two defects in the draft: upstream `persona start` did not restore the responder, and a shared fixed image tag did not isolate concurrent qualification builds.

The revised fresh-agent run used the public document alone, a unique image tag, port `18085`, and another disposable namespace.
Its image ID was `sha256:2580609325eddba6a3f198005a235157e58df5b1280015de8c697d4482602d21`.
The lifecycle helper restored both thinkers after identity stop and start, and a plain Docker restart preserved the same identity, root trajectory, memory fingerprint, model, endpoints, key presence, durable monolith state, responder, dashboard, and image ID.

The production migration then restore-tested a pre-migration state archive before changing the existing volume.
The Compose deployment preserved the private identity and root trajectory through identity restart, plain container restart, and forced Compose recreation.
Direct model health, both configured endpoint paths, key presence without disclosure, monolith progress, responder requests, the loopback dashboard, revision marker, active application path, and named volume all passed.

All disposable qualification containers, volumes, networks, images, and listeners were removed.
Temporary qualification directories and the disposable pre-migration archive were moved to Trash.
The forbidden macOS host paths remained absent.
The production volume retains the original imperative application and identity trees under an ignored legacy directory, while the declarative identity tree is active.

A live browser check after the first acceptance run found that HTTP health still passed when the dashboard discovered zero identities.
The corrective run moved the dashboard scan root from `/opt/headlong` to `/root/.headlong`, moved active state to the real `/root/.headlong/.identities` directory, and changed Compose health to require a nonempty `/api/identities` response.
The corrected production image ID was `sha256:c9a0d1dda78f7522a718f865729bb261a093f741adb36a7b69994f128bedc228`.
An isolated synthetic identity test passed, and the production API then returned exactly one discovered identity with the container healthy.

The unresolved limits are the alpha upstream source, the beta and low-traffic status of the tested Tinker-compatible interface, changing Debian package repositories, root execution inside the container, and the absence of a specification-wide backup retention destination.
A deployment owner must still select a canonical off-host backup root and retention policy.

## Scope

The specification defines one private, single-operator Headlong identity in one Docker container.
It does not define Slack, Telegram, a public dashboard, shared multi-user state, host workspace mounts, Docker socket access, model training, or a managed remote inference service.
Add any of those capabilities only through a separate threat model and acceptance process.

The public document is the behavioral source of truth.
A thin private overlay may record the chosen host, identity name, model, endpoint, secret-manager reference, Compose environment path, backup path, and production migration notes.
The private overlay must not contain the provider key itself.

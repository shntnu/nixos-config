FROM buildpack-deps@sha256:94754d58ac54626fa712c5c06535980417dc44f82c883f9b10f7059dc9000f5f

ARG HEADLONG_REV=87d4e7916b4b2fbb2cf1601fd8cfd20b32191ddc
ARG HEADLONG_SHA256=d254d1662f6ee139dc85134827a80ec5a3b4ad05c7bd0e478455cc70d6b0017a
ARG UV_VERSION=0.12.5
ARG UV_AARCH64_SHA256=9bf43b4d1a07665bf64d4c4e710930b382321a785e0eb10aac07f46471f86a31
ARG UV_X86_64_SHA256=68a509da24b06b4223a1c0175fb5eb5bc79342b76cbeff0cfe51ac3f5b17b6b2

ENV HEADLONG_HOME=/root/.headlong \
    HEADLONG_APP_DIR=/opt/headlong \
    PATH=/usr/local/bin:/usr/local/sbin:/usr/sbin:/usr/bin:/sbin:/bin

LABEL org.opencontainers.image.source="https://github.com/laude-institute/headlong" \
      org.opencontainers.image.revision="$HEADLONG_REV"

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends git jq nodejs npm procps \
    && apt-get clean \
    && find /var/lib/apt/lists -mindepth 1 -delete

RUN set -eu; \
    machine="$(uname -m)"; \
    case "$machine" in \
      aarch64) uv_arch=aarch64; uv_sha="$UV_AARCH64_SHA256" ;; \
      x86_64) uv_arch=x86_64; uv_sha="$UV_X86_64_SHA256" ;; \
      *) echo "unsupported architecture: $machine" >&2; exit 1 ;; \
    esac; \
    curl -fsSL -o /tmp/uv.tar.gz \
      "https://github.com/astral-sh/uv/releases/download/${UV_VERSION}/uv-${uv_arch}-unknown-linux-gnu.tar.gz"; \
    printf '%s  %s\n' "$uv_sha" /tmp/uv.tar.gz | sha256sum -c -; \
    tar -xzf /tmp/uv.tar.gz -C /tmp; \
    install -m 0755 "/tmp/uv-${uv_arch}-unknown-linux-gnu/uv" /usr/local/bin/uv; \
    install -m 0755 "/tmp/uv-${uv_arch}-unknown-linux-gnu/uvx" /usr/local/bin/uvx; \
    find /tmp -mindepth 1 -delete

RUN curl -fsSL -o /tmp/headlong.tar.gz \
      "https://github.com/laude-institute/headlong/archive/${HEADLONG_REV}.tar.gz" \
    && printf '%s  %s\n' "$HEADLONG_SHA256" /tmp/headlong.tar.gz | sha256sum -c - \
    && mkdir -p /opt/headlong \
    && tar -xzf /tmp/headlong.tar.gz --strip-components=1 -C /opt/headlong \
    && printf '%s\n' "$HEADLONG_REV" > /opt/headlong/.headlong-revision \
    && find /tmp -mindepth 1 -delete \
    && bash /opt/headlong/install.sh --symlinks --prefix /usr/local/bin \
    && ln -s /root/.headlong/identities /opt/headlong/.identities

COPY entrypoint.sh /usr/local/bin/headlong-container-entrypoint
COPY lifecycle.sh /usr/local/bin/headlong-identity

EXPOSE 8080
VOLUME ["/root/.headlong"]
ENTRYPOINT ["/usr/local/bin/headlong-container-entrypoint"]

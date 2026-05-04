{ pkgs, lib ? pkgs.lib }:

with pkgs; [
  # General packages for development and system management
  aspell
  aspellDicts.en
  bash-completion
  bat
  btop
  coreutils
  duckdb
  killall
  fastfetch
  openssh
  sqlite
  wget
  zip

  # Encryption and security tools
  age
  age-plugin-yubikey
  gnupg
  libfido2

  # Cloud-related tools and SDKs
  # awscli via Homebrew (see modules/darwin/home-manager.nix brews)
  # docker and docker-compose handled by Docker Desktop via Homebrew cask
  # AWS CDK moved to Node.js section above
  rclone
  s5cmd
  tailscale

  # Version control and development tools
  gh
  just
  just-lsp

  # Email archive (msgvault flake input -> overlay in flake.nix)
  msgvault

  # Workflow management
  jdk17  # Java runtime for Nextflow
  nextflow  # Bioinformatics workflow manager, works with Docker Desktop
  nf-test  # Testing framework for Nextflow pipelines

  # Media-related packages
  emacs-all-the-icons-fonts
  dejavu_fonts
  ffmpeg
  fd
  sox
  font-awesome
  hack-font
  noto-fonts
  noto-fonts-color-emoji
  meslo-lgs-nf

  # Node.js development tools
  nodejs_24
  aws-cdk-cli
  pi-coding-agent  # trails npm by days; if needed: npm install -g @mariozechner/pi-coding-agent

  # Terminal support (Linux only; macOS uses Ghostty cask which ships its own terminfo)
] ++ lib.optionals (!pkgs.stdenv.isDarwin) [
  ghostty.terminfo
] ++ [
  # Text and terminal utilities
  trash-cli
  hunspell
  iftop
  jq
  parallel
  ripgrep
  tree
  eza  # Modern ls/tree replacement with colors and icons
  yazi  # Terminal file manager
  tldr
  tmux
  unrar
  unzip
  starship
  atuin
  zoxide

  # Theorem proving
  elan  # Lean 4 toolchain manager (provides lean, lake)

  # Python packages
  python3
  virtualenv
  uv
  pixi

  # Linting and formatting
  markdownlint-cli
  pre-commit
  ruff
  nil # Nix LSP for VSCode
  nixpkgs-fmt # Nix formatter

  # Note taking tools
  # obsidian — moved to Homebrew cask (modules/darwin/casks.nix) for v1.12+ CLI support

  # AI Coding tools
  ollama  # local LLM runtime; daemon: `ollama serve`, models: `ollama pull <name>`
  # claude-code installed imperatively:
  #   Install: nix profile install github:sadjow/claude-code-nix
  #   Upgrade: nix profile upgrade claude-code-nix --refresh
  # gemini-cli installed imperatively:
  #   Install: nix profile install github:sadjow/gemini-cli-nix
  #   Upgrade: nix profile upgrade gemini-cli-nix --refresh
  # codex-cli installed imperatively:
  #   Install: nix profile install github:sadjow/codex-cli-nix
  #   Upgrade: nix profile upgrade codex-cli-nix --refresh
  # qmd (Query Markup Documents) — no nix flake wrapper yet, uses npm:
  #   Install: npm install -g @tobilu/qmd
  #   Upgrade: npm update -g @tobilu/qmd
  #   Repo: https://github.com/tobi/qmd

  # Utils
  graphviz
  mermaid-cli
  pandoc
  poppler-utils
  texlive.combined.scheme-medium
  whisper-cpp
]

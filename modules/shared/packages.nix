{ pkgs }:

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
  neofetch
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

  # Workflow management
  jdk17  # Java runtime for Nextflow
  nextflow  # Bioinformatics workflow manager, works with Docker Desktop
  nf-test  # Testing framework for Nextflow pipelines

  # Media-related packages
  emacs-all-the-icons-fonts
  dejavu_fonts
  ffmpeg
  fd
  font-awesome
  hack-font
  noto-fonts
  noto-fonts-color-emoji
  meslo-lgs-nf

  # Node.js development tools
  nodejs_24
  nodePackages.aws-cdk

  # Text and terminal utilities
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
  obsidian

  # AI Coding tools
  # claude-code installed imperatively:
  #   Install: nix profile install github:sadjow/claude-code-nix
  #   Upgrade: nix profile upgrade claude-code-nix --refresh
  # gemini-cli installed imperatively:
  #   Install: nix profile install github:sadjow/gemini-cli-nix
  #   Upgrade: nix profile upgrade gemini-cli-nix --refresh

  # Utils
  graphviz
  mermaid-cli
  pandoc
  poppler-utils
  texlive.combined.scheme-medium
  whisper-cpp
]

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
  awscli2
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

  # Media-related packages
  emacs-all-the-icons-fonts
  dejavu_fonts
  ffmpeg
  fd
  font-awesome
  hack-font
  noto-fonts
  noto-fonts-emoji
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
  pre-commit
  ruff
  nil # Nix LSP for VSCode
  nixpkgs-fmt # Nix formatter

  # Note taking tools
  obsidian

  # AI Coding tools
  claude-code

  # Utils
  graphviz
  pandoc
  poppler-utils
  texlive.combined.scheme-medium
  whisper-cpp
]

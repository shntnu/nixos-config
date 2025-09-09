{ pkgs }:

with pkgs; [
  # General packages for development and system management
  # alacritty
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
  docker
  docker-compose
  rclone
  s5cmd
  tailscale

  # Version control and development tools
  gh
  just

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

  # Text and terminal utilities
  htop
  hunspell
  iftop
  # jetbrains-mono
  jq
  parallel
  ripgrep
  tree
  tmux
  unrar
  unzip
  starship
  atuin
  z-lua

  # Python packages
  python3
  virtualenv
  uv
  pixi

  # Linting and formatting
  pre-commit
  ruff

  # Note taking tools
  obsidian

  # AI Coding tools
  claude-code

  # Utils
  whisper-cpp
  graphviz
  pandoc
  texlive.combined.scheme-medium
]

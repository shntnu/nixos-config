{ pkgs }:

with pkgs; [
  awscli2  # Mac gets awscli via Homebrew; servers have no Homebrew, so add it here

  duf
  httpie
  mtr
  yq-go

  docker
  docker-compose

  ranger

  nixpkgs-fmt

  nvitop
  lazygit
  htop
  imagemagick
  nix-output-monitor
  p7zip
]

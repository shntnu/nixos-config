{ pkgs }:

with pkgs; [
  # Server-oriented tools that are useful on lab machines but not part of the
  # macOS baseline.
  duf
  httpie
  mtr
  yq-go

  # Containers and cloud data movement.
  docker
  docker-compose

  # Terminal file managers.
  ranger

  # Shared lab workflow tools.
  nixpkgs-fmt
]

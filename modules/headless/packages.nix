{ pkgs }:

with pkgs; [
  awscli2  # Mac gets awscli via Homebrew; servers have no Homebrew, so add it here

  duf
  httpie
  mtr
  yq-go

  docker
  docker-compose

  neovim  # servers set EDITOR/VISUAL=nvim (see headless/home-manager.nix)

  ghostty  # only useful on karkinos (it has a display); dead weight on oppy/spirit
  google-chrome  # ditto: karkinos has a display. Unfree (allowUnfree is on in shared/nixpkgs.nix)

  ranger

  nixpkgs-fmt

  nvitop
  lazygit
  htop
  imagemagick
  nix-output-monitor
  p7zip
]

# Nix Learning Log

## 2025-01-21: System vs User Level Management

**Key Insight:** Ubuntu needs different commands than NixOS/macOS because it lacks system-level rebuild tools.

Three management approaches exist:
- NixOS: `nixos-rebuild` manages entire Linux system (kernel, services, packages)
- macOS: `darwin-rebuild` manages macOS system settings and packages
- Ubuntu: Home Manager standalone manages user environment only

Commands differ by platform:
```bash
# NixOS/macOS - system-level
nix run .#build-switch

# Ubuntu/WSL - user-level only
nix run 'home-manager/master' -- switch --flake '.#shsingh'
```

Ubuntu gets CLI tools and dotfiles but not GUI apps or system services. Those need `apt install`.

## 2025-01-21: Home Manager's Two Modes

**Key Insight:** Home Manager runs in integrated mode on NixOS/macOS (inside system rebuild) but standalone mode on Ubuntu.

Home Manager isn't just for Ubuntu - it's used everywhere, differently:
- NixOS/macOS: Loaded as a module in system configurations, runs during `nixos-rebuild`/`darwin-rebuild`
- Ubuntu: Runs standalone via `home-manager switch` since no system rebuild exists

Same Home Manager, different delivery mechanism. System rebuild carries it on NixOS/macOS; Ubuntu runs it directly.

---

## Entry Guidelines

Keep entries brief. Structure each as:
- Date and descriptive title
- **Key Insight:** One sentence capturing the core learning
- 2-4 sentences of essential context
- Optional: Relevant command or code snippet
- Optional: Link to docs for deeper dive

Focus on "what" and "why", not detailed "how". Reader can consult docs for implementation details.

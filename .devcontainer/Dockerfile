# Optional, reproducible covalence dev environment — built on the repo's own
# flake.nix so the container and the native `nix develop` shell are the SAME
# environment (one source of truth for the toolchain). This is opt-in: nothing
# in the normal build path depends on it.
#
# Pin `nixos/nix` to a specific tag for full reproducibility once you've chosen
# one; `latest` is used here so the file works out of the box.
FROM nixos/nix:latest

# Enable the flakes CLI, and keep build outputs/derivations so the flake
# devshell stays cached across container restarts.
RUN mkdir -p /etc/nix \
 && printf 'experimental-features = nix-command flakes\nmax-jobs = auto\nkeep-outputs = true\nkeep-derivations = true\n' \
      >> /etc/nix/nix.conf

# direnv + nix-direnv so `cd`-ing into the repo auto-loads the flake devshell
# (the repo's .envrc is `use flake`).
RUN nix profile install nixpkgs#direnv nixpkgs#nix-direnv nixpkgs#bashInteractive \
 && mkdir -p /root/.config/direnv \
 && printf 'source "$HOME/.nix-profile/share/nix-direnv/direnvrc"\n' > /root/.config/direnv/direnvrc \
 && printf '\neval "$(direnv hook bash)"\n' >> /root/.bashrc

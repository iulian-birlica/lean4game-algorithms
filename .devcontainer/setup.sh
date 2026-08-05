#!/bin/bash
set -euo pipefail

# Install Lean from the repo's pinned toolchain.
export LEAN_VERSION="$(cat lean-toolchain)"
echo "LEAN_VERSION is: $LEAN_VERSION"
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain "$LEAN_VERSION"
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
export PATH="$HOME/.elan/bin:$PATH"

# Prime the Lean side of the workspace.
cd Game
lake update -R
lake exe cache get

# Install lean4game dependencies that power the browser UI.
cd ../vendor/lean4game
npm install

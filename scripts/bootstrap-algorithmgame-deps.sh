#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
game_dir="$repo_root/game"
lean4game_dir="$repo_root/lean4game"
toolchain_file="$game_dir/lean-toolchain"

if [[ ! -d "$game_dir" ]]; then
  echo "Expected Game at $game_dir" >&2
  exit 1
fi

if [[ ! -f "$toolchain_file" ]]; then
  echo "Missing $toolchain_file" >&2
  exit 1
fi

lean4game_ref="$(sed -n 's#leanprover/lean4:##p' "$toolchain_file")"
if [[ -z "$lean4game_ref" ]]; then
  echo "Could not determine lean4game ref from $toolchain_file" >&2
  exit 1
fi

if [[ -d "$lean4game_dir/.git" ]]; then
  echo "lean4game already present at $lean4game_dir"
else
  git clone --branch "$lean4game_ref" --depth 1 \
    https://github.com/leanprover-community/lean4game.git \
    "$lean4game_dir"
fi

cat <<EOF
Dependencies downloaded.

Next steps:
  cd "$game_dir"
  lake update -R -Klean4game.local
  lake exe cache get
  lake build
EOF

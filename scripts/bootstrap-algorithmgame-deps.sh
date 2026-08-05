#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
game_dir="$repo_root/game"

if [[ ! -d "$game_dir" ]]; then
  echo "Expected Game at $game_dir" >&2
  exit 1
fi

cat <<EOF
No local bootstrap is needed anymore.

Next steps:
  cd "$game_dir"
  lake update -R
  lake exe cache get
  lake build
EOF

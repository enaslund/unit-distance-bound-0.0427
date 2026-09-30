#!/usr/bin/env bash
# Reproduce public verification tools in an ignored project-local cache.
# Prerequisites: Git, elan, Cargo, and Go. Toolchains stay in this task's cache.
set -euo pipefail
project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
tools_dir=${UNIT_DISTANCE_VERIFICATION_TOOLS:-"$project_dir/.cache/verification-tools"}
mkdir -p "$tools_dir/bin" "$tools_dir/go-build" "$tools_dir/go-path" "$tools_dir/cargo"
for program in git cargo go elan; do
  command -v "$program" >/dev/null || { echo "error: $program is required" >&2; exit 2; }
done

checkout() {
  local url=$1 target=$2 revision=$3
  if [[ ! -d "$target/.git" ]]; then
    git clone --filter=blob:none "$url" "$target"
  fi
  if [[ -n "$(git -C "$target" status --porcelain --untracked-files=no)" ]]; then
    echo "error: refusing to change a modified tooling checkout: $target" >&2
    exit 2
  fi
  git -C "$target" fetch --depth 1 origin "$revision"
  git -C "$target" checkout --detach "$revision"
}

checkout https://github.com/leanprover/comparator.git "$tools_dir/comparator" 575674928e239f5bc452aab72d1dd7b0f1326494
checkout https://github.com/leanprover/lean4export.git "$tools_dir/lean4export" 4e7915201d3f9f04470d9eae002fa695f7cdc589
checkout https://github.com/robsimmons/nanoda_lib.git "$tools_dir/nanoda" 68d5ca9db226849b41a6fff59d796ff19d0a8840
cmp "$project_dir/lean-toolchain" "$tools_dir/lean4export/lean-toolchain"
build_lean_tool() {
  local target_dir=$1 target_name=$2
  local target_toolchain
  target_toolchain=$(cat "$target_dir/lean-toolchain")
  ELAN_HOME="$tools_dir/elan" elan toolchain install "$target_toolchain"
  (cd "$target_dir" && ELAN_HOME="$tools_dir/elan" elan run "$target_toolchain" lake build "$target_name")
}
build_lean_tool "$tools_dir/comparator" comparator
build_lean_tool "$tools_dir/lean4export" lean4export
(cd "$tools_dir/nanoda" && CARGO_HOME="$tools_dir/cargo" cargo build --release --locked)
GOBIN="$tools_dir/bin" GOPATH="$tools_dir/go-path" GOCACHE="$tools_dir/go-build" \
  CGO_ENABLED=0 go install github.com/zouuup/landrun/cmd/landrun@811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
echo "Verification tools are ready under $tools_dir"

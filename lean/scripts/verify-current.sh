#!/usr/bin/env bash
# Build both conditional theorems and audit their axioms; independent replay is separate.
set -euo pipefail
project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
source "$project_dir/env.sh"
cd "$project_dir"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
lake build +ChallengeZeta241:olean +SolutionZeta241:olean +ChallengeZeta:olean +SolutionZeta:olean +AuditSupport:olean
lake env lean -DstderrAsMessages=false verification/sqrt241-v2-20261008/audit/Sqrt241V2Audit.lean
lake env lean -DstderrAsMessages=false verification/ZetaAudit.lean

#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
export LEAN_PATH=".:../.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
"$LEAN" Canonical.lean -o Canonical.olean
"$LEAN" ReturnSafety.lean -o ReturnSafety.olean
"$LEAN" ParetoGuard.lean -o ParetoGuard.olean
"$LEAN" Voting.lean -o Voting.olean
"$LEAN" Anonymity.lean -o Anonymity.olean
"$LEAN" Pareto.lean -o Pareto.olean
"$LEAN" TopChoices.lean -o TopChoices.olean
"$LEAN" Monotonicity.lean -o Monotonicity.olean
"$LEAN" NotMonotone.lean -o NotMonotone.olean
"$LEAN" AuditAnonymity.lean
"$LEAN" AuditPareto.lean
"$LEAN" AuditMonotonicity.lean
"$LEAN" AuditTopChoices.lean
"$LEAN" --run TestVoting.lean
"$LEAN" --run TestTopChoices.lean

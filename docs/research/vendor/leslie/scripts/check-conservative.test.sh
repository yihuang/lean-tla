#!/usr/bin/env bash
# scripts/check-conservative.test.sh
#
# Synthetic-diff tests for scripts/check-conservative.sh.
#
# Each test feeds a fake diff (via CONSERVATIVE_CHECK_DIFF_CMD) and
# asserts the script exits with the expected status:
#
#   expect_violation — script should reject (exit 1)
#   expect_pass      — script should accept (exit 0)
#
# Run from repo root:  bash scripts/check-conservative.test.sh

set -uo pipefail

CHECK="bash $(dirname "$0")/check-conservative.sh"
PASS=0
FAIL=0

expect_violation() {
  local desc="$1"; shift
  local paths="$*"
  if CONSERVATIVE_CHECK_DIFF_CMD="printf '%s\n' $paths" $CHECK > /dev/null 2>&1; then
    printf 'FAIL  %-55s [expected violation, got pass]\n' "$desc"
    FAIL=$((FAIL+1))
  else
    printf 'PASS  %-55s\n' "$desc"
    PASS=$((PASS+1))
  fi
}

expect_pass() {
  local desc="$1"; shift
  local paths="$*"
  if CONSERVATIVE_CHECK_DIFF_CMD="printf '%s\n' $paths" $CHECK > /dev/null 2>&1; then
    printf 'PASS  %-55s\n' "$desc"
    PASS=$((PASS+1))
  else
    printf 'FAIL  %-55s [expected pass, got violation]\n' "$desc"
    FAIL=$((FAIL+1))
  fi
}

echo "## Conservative-extension regex tests"
echo ""

# --- Violations: existing protected files ---
echo "### Should reject (protected files):"
expect_violation "core: Leslie/Refinement.lean"           "Leslie/Refinement.lean"
expect_violation "core: Leslie/Action.lean"                "Leslie/Action.lean"
expect_violation "core: Leslie/Cutoff.lean"                "Leslie/Cutoff.lean"
expect_violation "rules: Leslie/Rules/WF.lean"             "Leslie/Rules/WF.lean"
expect_violation "tactics (non-Prob)"                      "Leslie/Tactics/Basic.lean"
expect_violation "gadgets"                                 "Leslie/Gadgets/SetFn.lean"
expect_violation "Rust subdir"                             "Leslie/Rust/Bridge.lean"
expect_violation "single-file example"                     "Leslie/Examples/BenOr.lean"
expect_violation "nested example: Combinators"            "Leslie/Examples/Combinators/PhaseCombinator.lean"
expect_violation "nested example: Paxos"                   "Leslie/Examples/Paxos/MessagePaxos.lean"
expect_violation "nested example: CacheCoherence"          "Leslie/Examples/CacheCoherence/TileLink/Messages/Bracket.lean"
expect_violation "nested example: VerusBridge"             "Leslie/Examples/VerusBridge/Adder.lean"
expect_violation "nested example: LastVotingPhased"        "Leslie/Examples/LastVotingPhased/X.lean"
expect_violation "Leslie root entry"                       "Leslie.lean"
expect_violation "MANUAL.md"                               "MANUAL.md"
expect_violation "README.md"                               "README.md"
expect_violation "AGENTS.md"                               "AGENTS.md"
expect_violation "rust/ (lowercase, separate work)"        "rust/Cargo.toml"
expect_violation "mixed: one allowed + one protected"      "docs/foo.md Leslie/Refinement.lean"

echo ""
echo "### Should accept (allowlisted):"
# --- Pass: allowlisted ---
expect_pass "Leslie/Prob/ — new code"           "Leslie/Prob/Action.lean"
expect_pass "Leslie/Prob/Spike/ — spike"        "Leslie/Prob/Spike/CoinFlip.lean"
expect_pass "Leslie/UC/ — new code"             "Leslie/UC/Realize.lean"
expect_pass "Leslie/Tactics/Prob.lean"          "Leslie/Tactics/Prob.lean"
expect_pass "Leslie/Examples/Prob/ — new"       "Leslie/Examples/Prob/Shamir.lean"
expect_pass "docs/ — design"                    "docs/randomized-leslie-plan.md"
expect_pass "docs/ — nested spike"              "docs/randomized-leslie-spike/01-trace-measure.md"
expect_pass "scripts/ — this file's tree"       "scripts/check-conservative.sh"
expect_pass ".github/ — CI"                     ".github/workflows/ci.yml"
expect_pass "lakefile.lean — Mathlib add"       "lakefile.lean"
expect_pass "lake-manifest.json — pin update"   "lake-manifest.json"
expect_pass "lean-toolchain — bump"             "lean-toolchain"
expect_pass "empty diff (nothing to check)"     ""
expect_pass "all-allowed mixed diff"            "Leslie/Prob/Action.lean docs/x.md lakefile.lean"

echo ""
echo "---"
printf 'Passed: %d\nFailed: %d\n' "$PASS" "$FAIL"

if [[ $FAIL -eq 0 ]]; then
  exit 0
else
  exit 1
fi

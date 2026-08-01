#!/usr/bin/env bash
# scripts/check-conservative.sh
#
# Conservative-extension check for the randomized-leslie branch.
#
# Verifies that a diff against `origin/main` only touches files inside
# the randomized-leslie *allowlist*: new modules under `Leslie/Prob/`,
# `Leslie/UC/`, the single new tactic file `Leslie/Tactics/Prob.lean`,
# new examples under `Leslie/Examples/Prob/`, documentation under
# `docs/`, the script tree itself (`scripts/`), CI config
# (`.github/`), and the Mathlib-affected build-system files
# (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`).
#
# Anything outside the allowlist is reported as a violation. This
# protects the existing Leslie codebase byte-for-byte while permitting
# Mathlib version bumps and randomized-leslie additions.
#
# Why allowlist (not blocklist):
#   The previous protected-list regex (`^Leslie/Examples/[^/]+\.lean$`)
#   missed nested example directories like `Leslie/Examples/Combinators/`,
#   `Leslie/Examples/Paxos/`, `Leslie/Examples/CacheCoherence/`. An
#   allowlist is robust against new top-level files anywhere in the
#   repo and against the addition of new nested directories.
#
# Self-protection / trust model:
#   `scripts/` and `.github/` ARE in the allowlist (so this gate can
#   evolve), but the allowlist alone is not what makes the gate safe:
#   a PR could otherwise weaken the regex while modifying a protected
#   file. Safety comes from `.github/workflows/conservativity.yml`
#   running this script via `pull_request_target`, which reads both
#   the workflow YAML and `scripts/check-conservative.sh` from the
#   base branch (main), not the PR head. The PR head is consumed
#   only as a list of changed paths, never sourced. See the workflow
#   header for the full trust model.
#
# Usage:
#   bash scripts/check-conservative.sh
#
# Test override:
#   CONSERVATIVE_CHECK_DIFF_CMD='echo path/a.lean path/b.lean' \
#     bash scripts/check-conservative.sh
#   (overrides the git-diff source for unit testing)

set -euo pipefail

# Allowed paths (anchored at repo root). Newline-delimited for
# readability; joined with `|` for grep -E.
ALLOWED_PATHS=$(cat <<'EOF'
^Leslie/Prob/
^Leslie/UC/
^Leslie/Tactics/Prob\.lean$
^Leslie/Examples/Prob/
^docs/
^scripts/
^\.github/
^lakefile\.lean$
^lake-manifest\.json$
^lean-toolchain$
EOF
)

# Compose into a single alternation regex.
ALLOWED_RE=$(echo "$ALLOWED_PATHS" | tr '\n' '|' | sed 's/|$//')

# Source of changed paths. Default: diff against origin/main since
# branch divergence. Override via env var for testing.
DIFF_CMD="${CONSERVATIVE_CHECK_DIFF_CMD:-git diff --name-only origin/main...HEAD}"

# Files outside the allowlist (a non-empty result is a violation).
# `|| true` keeps the pipeline alive when grep finds nothing.
VIOLATIONS=$(eval "$DIFF_CMD" | grep -vE "$ALLOWED_RE" || true)

if [[ -n "$VIOLATIONS" ]]; then
  echo "Conservative-extension violation: the following files are outside the allowlist:"
  echo "$VIOLATIONS" | sed 's/^/  /'
  echo ""
  echo "Allowed paths (regex):"
  echo "$ALLOWED_PATHS" | sed 's/^/  /'
  echo ""
  echo "If a path genuinely belongs to the randomized-leslie scope, add it to"
  echo "ALLOWED_PATHS in scripts/check-conservative.sh and rerun the test."
  exit 1
fi

echo "Conservative-extension check: OK ($(eval "$DIFF_CMD" | wc -l | tr -d ' ') files, all in allowlist)"

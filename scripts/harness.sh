#!/usr/bin/env bash
# Harness for JSP-000179 formalization.
# 1. cd lean && lake build
# 2. count sorry/admit across the repo
# 3. #print axioms nonaveraging_max_size_sharp
# 4. append verdict to HARNESS_LOG.md
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
SHA="$(git rev-parse HEAD 2>/dev/null || echo 'no-git')"

export PATH="$HOME/.elan/bin:$PATH"

echo "=== harness $TS  sha=$SHA ==="

# --- gate 1: build -------------------------------------------------------
cd "$ROOT/lean"
BUILD_OUT="$(lake build 2>&1)"
BUILD_RC=$?
echo "$BUILD_OUT" | tail -40
if [ $BUILD_RC -eq 0 ]; then BUILD="green"; else BUILD="red"; fi
cd "$ROOT"

# --- gate 2: sorry / admit count ----------------------------------------
SORRY_COUNT=$(grep -rniE '\b(sorry|admit)\b' --include='*.lean' \
  --exclude-dir=.lake lean \
  | grep -v 'sorryAx' | wc -l | tr -d ' ')
echo "sorries: $SORRY_COUNT"

# --- gate 3: axioms ------------------------------------------------------
AXIOM_FILE="$ROOT/lean/AxiomCheck.lean"
cat > "$AXIOM_FILE" <<'EOF'
import Nonaveraging
#print axioms Nonaveraging.nonaveraging_max_size_sharp
EOF
cd "$ROOT/lean"
AXIOMS_OUT="$(lake env lean AxiomCheck.lean 2>&1)"
cd "$ROOT"
echo "$AXIOMS_OUT"
AXIOMS="green"
for extra in sorryAx Lean.ofReduceBool; do
  if echo "$AXIOMS_OUT" | grep -q "$extra"; then AXIOMS="red"; fi
done
rm -f "$AXIOM_FILE"

# --- verdict -------------------------------------------------------------
GATE="red"
if [ "$BUILD" = "green" ] && [ "$SORRY_COUNT" = "0" ] && [ "$AXIOMS" = "green" ]; then
  GATE="green"
fi

{
  echo ""
  echo "## $TS"
  echo "- sha: $SHA"
  echo "- build: $BUILD (rc=$BUILD_RC)"
  echo "- sorries: $SORRY_COUNT"
  echo "- axioms: $AXIOMS"
  echo "- **gate: $GATE**"
} >> "$ROOT/HARNESS_LOG.md"

echo "=== gate: $GATE ==="
[ "$GATE" = "green" ]

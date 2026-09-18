#!/usr/bin/env bash
# Machine-readable status: {build, sorries, axioms, gate}
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

cd lean
lake build >/dev/null 2>&1
BUILD_RC=$?
cd ..

SORRY_COUNT=$(grep -rniE '\b(sorry|admit)\b' --include='*.lean' lean \
  | grep -v 'sorryAx' | wc -l | tr -d ' ')

cd lean
AXIOMS_OUT="$(cat > AxiomCheck.lean <<'EOF'
import Nonaveraging
#print axioms Nonaveraging.nonaveraging_max_size_sharp
EOF
lake env lean AxiomCheck.lean 2>&1)"
cd ..
rm -f lean/AxiomCheck.lean
AXIOMS="clean"
echo "$AXIOMS_OUT" | grep -q 'sorryAx' && AXIOMS="sorryAx"

GATE="red"
if [ "$BUILD_RC" = "0" ] && [ "$SORRY_COUNT" = "0" ] && [ "$AXIOMS" = "clean" ]; then
  GATE="green"
fi

printf '{build: %s, sorries: %s, axioms: %s, gate: %s}\n' \
  "$([ $BUILD_RC = 0 ] && echo ok || echo fail)" "$SORRY_COUNT" "$AXIOMS" "$GATE"

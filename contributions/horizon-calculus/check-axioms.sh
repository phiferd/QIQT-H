#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p logs
for module in UniformHeatGuard NonuniformHeatWitness HorizonCalculus HalfLineCalculus CompactWitness; do
  lake env lean "$module.lean" > "logs/$module.axioms.log" 2>&1
  cat "logs/$module.axioms.log"
done

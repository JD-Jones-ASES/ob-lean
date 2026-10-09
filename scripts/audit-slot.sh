#!/usr/bin/env bash
# Desk only: Palomar's core-notation audit of the Challenge, run inside one of the two lane build slots
# (it needs ~4 GB). Usage: bash scripts/audit-slot.sh > .scratch/audit.json
LOCKDIR=/c/GitHub_Files/Claude-Repos/ob-lean/.lanes-lock
mkdir -p "$LOCKDIR"
slot=""
for _ in $(seq 1 720); do
  for s in slot1 slot2; do
    if mkdir "$LOCKDIR/$s" 2>/dev/null; then slot="$s"; break; fi
  done
  [ -n "$slot" ] && break
  sleep 5
done
[ -z "$slot" ] && { echo "no slot" >&2; exit 2; }
trap 'rmdir "$LOCKDIR/$slot" 2>/dev/null; rm -f /c/GitHub_Files/Claude-Repos/BOX-LOCK' EXIT
echo "audit: $(date) in $slot" > /c/GitHub_Files/Claude-Repos/BOX-LOCK
args=(Challenge)
for t in odd_length_mem odd_exists_iff unique aperiodic_eq skew fold doubling run_bounds four_dvd_of_even existsRealCirculantHadamard_of_even exists_iff_of_even length_le_thirteen_of_even exists_iff_of_circulantHadamard length_le_thirteen_of_circulantHadamard; do args+=(theorem "OddBarker.$t"); done
for d in IsSign aperiodic IsBarker RealMatrix IsCirculant IsSignHadamard ExistsRealCirculantHadamard canon; do args+=(def "OddBarker.$d"); done
lake env lean --run scripts/core_notation_audit.lean "${args[@]}"

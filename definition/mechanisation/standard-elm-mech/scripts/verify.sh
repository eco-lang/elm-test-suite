#!/usr/bin/env bash
# The project's verification, in one command (plan step 11, after milestone (g)).
#
#   scripts/verify.sh quick   # certify, incremental build of Certs/CertsAll and the root,
#                             # certify --check, and the fast checks (translator --check, no sorry/axiom)
#   scripts/verify.sh full    # quick, then run-examples, measure-cores, compare-e2e, check-axioms,
#                             # measure-w, check-hypotheses, syn-report
#
# Environment: K (default 4) is the most `lean` processes Lake runs at once (Lake 5 has no job flag;
# it runs as many jobs as the Lean task manager has threads, `LEAN_NUM_THREADS`). VERIFY_MEM (default
# 24G) is the memory of the systemd scope the whole run is in (MemorySwapMax=0): the script re-runs
# itself inside `systemd-run --user --scope` unless it is already in one it started.
#
# Each step prints one line: its result, its wall time, and the largest resident set of any single
# process it ran (GNU time's %M, which for `lake build` is the largest `lean` process). At the end:
# the total wall time, the largest single process of the run, and the scope's peak memory. The logs
# are in .lake/verify/ (lean-processes.txt: each `lean` process of the builds, sampled every 0.5 s:
# its file, its peak resident set, how long it ran). Exit status 0 when every step passes.
# Run from anywhere; it works in the project folder.
set -uo pipefail
MODE=${1:-quick}
case "$MODE" in quick|full) ;; *) echo "usage: $0 quick|full" >&2; exit 2;; esac
K=${K:-4}
VERIFY_MEM=${VERIFY_MEM:-24G}
cd "$(dirname "$0")/.." || exit 2
export PATH=$HOME/.elan/bin:$PATH

if [ -z "${VERIFY_IN_SCOPE:-}" ]; then
  if command -v systemd-run >/dev/null 2>&1; then
    VERIFY_IN_SCOPE=1 exec systemd-run --user --scope -q -p MemoryMax="$VERIFY_MEM" -p MemorySwapMax=0 \
      "$0" "$@"
  fi
  echo "systemd-run is not available: run this script inside a scope of at most $VERIFY_MEM, e.g." >&2
  echo "  systemd-run --user --scope -q -p MemoryMax=$VERIFY_MEM -p MemorySwapMax=0 $0 $MODE" >&2
  exit 2
fi

export LEAN_NUM_THREADS=$K
LOG=.lake/verify
mkdir -p "$LOG"
rm -f "$LOG"/*.log "$LOG"/*.time "$LOG"/samples.txt
CG=/sys/fs/cgroup$(sed -n 's/^0:://p' /proc/self/cgroup)
START=$(date +%s.%N)
FAILS=0
MAXRSS=0
MAXRSS_STEP=""

# GB as the conventions count them: GNU time's KB / 10^6
gb() { awk -v k="$1" 'BEGIN { printf "%.2f GB", k / 1000000 }'; }

# every 0.5 s, each `lean` process: time, file, peak resident set so far (VmHWM, KB)
( while true; do
    ps=$(ps -C lean -o pid= 2>/dev/null)
    echo "$(date +%s.%N) #n $(echo $ps | wc -w)"
    for p in $ps; do
      h=$(awk '/^VmHWM:/{print $2}' "/proc/$p/status" 2>/dev/null)
      f=$( { tr '\0' '\n' < "/proc/$p/cmdline"; } 2>/dev/null | grep -m1 '\.lean$' | sed 's|.*/standard-elm-mech/||')
      [ -n "$h" ] && echo "$(date +%s.%N) ${f:-?} $h"
    done
    sleep 0.5
  done >> "$LOG/samples.txt" ) &
SAMPLER=$!
trap 'kill $SAMPLER 2>/dev/null' EXIT

# step NAME SUMMARY -- COMMAND...: runs COMMAND (output in $LOG/NAME.log), then prints one line with the
# output of the shell text SUMMARY, run with the log's path as $1 (its exit status, with COMMAND's,
# decides pass/fail)
step() {
  local name=$1 summ=$2; shift 3
  local t=$LOG/$name.time out=$LOG/$name.log
  /usr/bin/time -f '%e %M' -o "$t" "$@" > "$out" 2>&1
  local rc=$?
  local secs rss
  read -r secs rss < <(tail -1 "$t")
  local line
  line=$(bash -c "$summ" _ "$out" 2>/dev/null)
  local src=$?
  if [ "$rss" -gt "$MAXRSS" ]; then MAXRSS=$rss; MAXRSS_STEP=$name; fi
  local status=ok
  if [ $rc -ne 0 ] || [ $src -ne 0 ]; then status=FAIL; FAILS=$((FAILS + 1)); fi
  printf '%-4s %-17s %s  [%ss, max RSS %s]\n' "$status" "$name" "${line:-(no summary; see $out)}" "$secs" "$(gb "$rss")"
}

# fast checks (the translator runs with a larger stack: eco's parser recurses deeply, plans/eco-parser.md E12)
if [ -x ../../../site/node_modules/.bin/elm-pages ]; then
  step translate-check 'grep -m1 "Lean translations" "$1"; grep -q "are up to date" "$1"' -- \
    bash -c 'cd ../../.. && node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --check'
fi
step no-sorry-axiom 'n=$(wc -l < "$1"); echo "$n sorry/axiom declarations in the sources"; [ "$n" -eq 0 ]' -- \
  bash -c 'grep -rnE "^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]|(:=|by|=>)[[:space:]]*sorry\b|^[[:space:]]*sorry\b" --include=*.lean StandardElmMech scripts *.lean; true'

step certify 'grep -E "^(static semantics|refused|end to end|shards|files):" "$1" | sed -E "s/ \((Stat\.[^)]*)\)//" | paste -sd "|" | sed "s/|/; /g"' -- \
  lake exe certify
STAMP=$LOG/build.stamp
touch "$STAMP"
step build 'grep -q "Build completed successfully" "$1" || exit 1; c=$(find .lake/build/lib/lean/StandardElmMech/Certs -name "*.olean" -newer .lake/verify/build.stamp | wc -l); a=$(find .lake/build/lib/lean -name "*.olean" -newer .lake/verify/build.stamp | wc -l); s=$(grep -c "declaration uses .sorry." "$1"); n=$(awk '"'"'$2 == "#n" && $3 > m { m = $3 } END { print m + 0 }'"'"' .lake/verify/samples.txt); echo "CertsAll and root built: $a modules rebuilt ($c certificate shards), $s sorry warnings, at most $n lean processes at once (K = '"$K"')"; [ "$s" -eq 0 ]' -- \
  lake build StandardElmMech.Certs.CertsAll StandardElmMech run-examples
step certify-check 'tail -1 "$1"' -- lake exe certify --check

if [ "$MODE" = full ]; then
  step run-examples 'grep -m1 "^Total:" "$1"' -- lake exe run-examples
  step measure-cores 'a=$(grep -m1 "^Cores" "$1"); b=$(grep -m1 "^Sanity" "$1"); echo "$a; $b"; echo "$b" | grep -q "^Sanity: 0 of"' -- lake exe measure-cores
  step compare-e2e 'grep -E "^(End to end|Step 9)" "$1" | paste -sd "|" | sed "s/|/; /"' -- lake exe compare-e2e
  step check-axioms 'grep -o "check-axioms: .*" "$1" | head -1' -- lake env lean scripts/check-axioms.lean
  step measure-w 'a=$(grep -m1 "^Compile-error tests" "$1"); b=$(grep -m1 "^Compile-success tests" "$1" | sed "s/; not run.*//"); echo "$a; $b"; echo "$b" | grep -q "W refutes 0 "' -- lake exe measure-w
  step check-hypotheses 'l=$(grep -o "check-hypotheses: [0-9]* per-test theorems and [0-9]* general theorems" "$1"); echo "$l mention D11"; echo "$l" | grep -q "check-hypotheses: 0 per-test"' -- \
    lake env lean scripts/check-hypotheses.lean
  step syn-report 'grep -m1 "programs:" "$1"' -- lake exe syn-report
fi

kill $SAMPLER 2>/dev/null
wait $SAMPLER 2>/dev/null
# per lean process (by file): peak resident set, seconds seen
awk '$2 != "#n" { if ($3 > peak[$2]) peak[$2] = $3; if (!($2 in first)) first[$2] = $1; last[$2] = $1 }
     END { for (f in peak) printf "%8.2f GB %7.1f s  %s\n", peak[f] / 1000000, last[f] - first[f], f }' \
  "$LOG/samples.txt" 2>/dev/null | sort -rn > "$LOG/lean-processes.txt"
END=$(date +%s.%N)
peak=$( [ -r "$CG/memory.peak" ] && cat "$CG/memory.peak" || echo 0)
echo "---"
echo "$MODE: $(awk -v a="$START" -v b="$END" 'BEGIN { s = b - a; printf "%d min %d s", s / 60, s % 60 }') wall;" \
  "largest single process $(gb "$MAXRSS") ($MAXRSS_STEP); scope peak $(awk -v p="$peak" 'BEGIN { printf "%.2f GB", p / 1000000000 }') of $VERIFY_MEM;" \
  "K = $K"
[ -s "$LOG/lean-processes.txt" ] && echo "largest lean process: $(head -1 "$LOG/lean-processes.txt" | sed 's/  */ /g')"
if [ $FAILS -eq 0 ]; then echo "all steps passed"; else echo "$FAILS step(s) FAILED (logs in $LOG)"; fi
[ $FAILS -eq 0 ]

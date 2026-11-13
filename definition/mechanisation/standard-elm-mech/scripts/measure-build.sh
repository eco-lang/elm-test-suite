#!/usr/bin/env bash
# Measures the build's memory as plans/lean-full-definition/conventions.md defines it: the largest
# single lean process (resident set, from /usr/bin/time -v) and the peak of the summed proportional
# set size of all concurrent lean processes, on a clean build of a copy of this project. Run from
# the project folder. It never deletes inside the repository: every deletion is in the copy.
set -euo pipefail
COPY=$(mktemp -d "${TMPDIR:-/tmp}/sem-measure.XXXXXX")
# The copy sits two levels below a link to the book's sources, as the project does, because
# Stat/RuleCount.lean reads ../../tex.
mkdir -p "${COPY:?}/definition/mechanisation"
ln -s "$(cd ../../tex && pwd)" "${COPY:?}/definition/tex"
cp -r . "${COPY:?}/definition/mechanisation/proj"
rm -rf "${COPY:?}/definition/mechanisation/proj/.lake/build"
cd "${COPY:?}/definition/mechanisation/proj"
echo 0 > "${COPY:?}/pss-peak"
# At each new peak, also record which files the concurrent lean processes are compiling.
( set +eu +o pipefail; peak=0; while sleep 0.5; do
    s=0; files=""; for p in $(pgrep -x lean || true); do
      v=$(awk '/^Pss:/{print $2}' "/proc/$p/smaps_rollup" 2>/dev/null || echo 0); s=$((s+${v:-0}))
      f=$(tr '\0' '\n' < "/proc/$p/cmdline" 2>/dev/null | grep -m1 '\.lean$' | sed 's|.*/StandardElmMech/|StandardElmMech/|')
      files="$files ${f:-?}:${v:-0}"; done
    if [ "$s" -gt "$peak" ]; then peak=$s; echo "$peak" > "${COPY:?}/pss-peak"; echo "$files" > "${COPY:?}/pss-peak-files"; fi
  done ) & SAMPLER=$!
/usr/bin/time -v lake build 2> "${COPY:?}/time.txt" > "${COPY:?}/build.txt" || true
kill "$SAMPLER" 2>/dev/null || true
echo "max single-process RSS (KB): $(awk -F': ' '/Maximum resident set size/{print $2}' "${COPY:?}/time.txt")"
echo "wall clock: $(awk -F': ' '/Elapsed \(wall clock\)/{print $2}' "${COPY:?}/time.txt")"
echo "peak summed PSS (KB): $(cat "${COPY:?}/pss-peak")"
echo "at the peak (file:PSS KB):$(cat "${COPY:?}/pss-peak-files" 2>/dev/null)"
grep -q "Exit status: 0" "${COPY:?}/time.txt" || { echo "the build FAILED:"; grep -E "^error|✖" "${COPY:?}/build.txt" | head -20; }
for f in StandardElmMech/Generated/Checks*.lean StandardElmMech/Generated/Syn*.lean; do
  [ "$f" = StandardElmMech/Generated/SynAll.lean ] && continue
  /usr/bin/time -f "$f %M KB %e s" lake env lean "$f" 2>&1 >/dev/null | tail -1
done
rm -rf "${COPY:?}"

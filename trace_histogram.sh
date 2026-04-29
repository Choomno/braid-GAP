#!/usr/bin/env bash
# Summarize a saved SGrobnerTrace output file.
#
# Usage: trace_histogram.sh path/to/grobner_basis_zipper-...gap
#
# Streams over the file (no GAP, no full load), reporting:
#   - file size
#   - number of basis elements (rec entries)
#   - total trace tuples
#   - per-input-relation usage histogram (which I[k] each tuple references)
#
# The trace tuple format saved by GBNP is
#     [ <leftWord>, <inputIdx>, <rightWord>, <coefficient> ]
# so a `], <number>, [` pattern uniquely picks out the inputIdx field.

set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <basis-file.gap>" >&2
  exit 2
fi

file="$1"
if [[ ! -f "$file" ]]; then
  echo "error: file not found: $file" >&2
  exit 1
fi

echo "=== File ==="
ls -lh "$file" | awk '{printf "  path: %s\n  size: %s\n", $9, $5}'

# Extract n (number of strands) from the saved file's `n := <int>;` line.
# This determines how many input relations there are and what each one is.
n=$(grep -m1 -E '^n := [0-9]+;' "$file" | grep -oE '[0-9]+' | head -1)
if [[ -z "${n:-}" ]]; then
  echo "  warning: could not extract n; labels will fall back to bare indices" >&2
  n=0
fi
echo "  n = $n strands"

# Build labels matching zipper.gap's input order:
#   1. invertibility:           x_i*y_i=1, y_i*x_i=1   for i=1..n-1
#   2. far-comm/braid:          one (i,j) loop
#   3. mixed-sign braid conseq: one i=1..n-2 loop, 4 each
#   4. complex (simplified):    zipper i=2, then i=3..n-1; untwist i=2, then i=3..n
labels=()
if (( n >= 2 )); then
  for ((i=1; i<n; i++)); do
    labels+=("x${i}*y${i}=1")
    labels+=("y${i}*x${i}=1")
  done
  for ((i=1; i<n-1; i++)); do
    for ((j=i+1; j<n; j++)); do
      if (( j - i >= 2 )); then
        labels+=("[x${i},x${j}]")
        labels+=("[y${i},y${j}]")
        labels+=("[y${i},x${j}]")
        labels+=("[x${i},y${j}]")
      else
        labels+=("x-braid(${i},${j})")
        labels+=("y-braid(${i},${j})")
      fi
    done
  done
  for ((i=1; i<n-1; i++)); do
    j=$((i+1))
    labels+=("xxy(${i},${j})")
    labels+=("yyx(${i},${j})")
    labels+=("xyy(${i},${j})")
    labels+=("yxx(${i},${j})")
  done
  labels+=("zipper(i=2)")
  for ((i=3; i<n; i++)); do labels+=("zipper(i=${i})"); done
  labels+=("untwist(i=2)")
  for ((i=3; i<=n; i++)); do labels+=("untwist(i=${i})"); done
fi

echo
echo "=== Basis elements ==="
basis_count=$(grep -c 'pol :=' "$file" || true)
echo "  basis size: $basis_count"

echo
echo "=== Trace tuple usage by input-relation index ==="
# grep -oE matches non-overlapping; one tuple's idx field is one match.
tmp=$(mktemp)
labels_file=$(mktemp)
trap 'rm -f "$tmp" "$labels_file"' EXIT

grep -oE '\], [0-9]+, \[' "$file" \
  | grep -oE '[0-9]+' \
  | sort -n | uniq -c > "$tmp"

total=$(awk '{s+=$1} END {print s+0}' "$tmp")
echo "  total trace tuples: $total"
if [[ "$basis_count" -gt 0 && "$total" -gt 0 ]]; then
  awk -v n="$basis_count" -v t="$total" \
    'BEGIN {printf "  mean tuples per basis element: %.0f\n", t/n}'
fi

# Write labels to file, one per line, indexed by line number = I[k].
: > "$labels_file"
for L in "${labels[@]}"; do printf '%s\n' "$L" >> "$labels_file"; done

echo
printf "  %-9s %-9s %-7s %s\n" count share "I[idx]" relation
printf "  %-9s %-9s %-7s %s\n" -------- -------- ------- --------
awk -v t="$total" -v lf="$labels_file" '
  BEGIN {
    while ((getline line < lf) > 0) labels[++n] = line
    close(lf)
  }
  {
    pct = (t > 0) ? (100.0 * $1 / t) : 0
    lab = ($2 in labels) ? labels[$2+0] : "?"
    printf "  %9d %8.2f%% I[%-4s] %s\n", $1, pct, $2, lab
  }
' "$tmp"

echo
echo "=== Per-basis-element analysis (pol terms, trace length) ==="
echo "=== and aggregate left/right word-length distribution     ==="
gawk '
  # State machine over the GBT section.
  # Each basis element = rec( pol := <NP poly>, trace := <list of tuples> ).
  # We track which section we are in and accumulate counters.

  /pol := / {
    if (state == "trace") {
      idx++
      pol_size[idx] = saved_pol
      trace_size[idx] = trace_tuples
    }
    state = "pol"
    pol_terms = 0
    trace_tuples = 0
  }

  /trace := / {
    saved_pol = pol_terms
    state = "trace"
    trace_tuples = 0
  }

  {
    if (state == "pol") {
      # Each monomial has exactly one ZmodpZObj coefficient.
      s = $0
      while (match(s, /ZmodpZObj\(/)) {
        pol_terms++
        s = substr(s, RSTART + RLENGTH)
      }
    } else if (state == "trace") {
      # Count trace-tuple idx fields (`], N, [` between leftWord and rightWord).
      s = $0
      while (match(s, /\], [0-9]+, \[/)) {
        trace_tuples++
        s = substr(s, RSTART + RLENGTH)
      }

      # Extract left/right word lengths per tuple.
      # Pattern: [ [ <leftContents> ], <idx>, [ <rightContents> ], ZmodpZObj
      # <leftContents> and <rightContents> contain integers separated by commas
      # (or just whitespace if the word is empty).
      s = $0
      while (match(s, /\[ \[([^][]*)\], [0-9]+, \[([^][]*)\], ZmodpZObj/, capt)) {
        left = capt[1]; right = capt[2]
        gsub(/^[[:space:]]+|[[:space:]]+$/, "", left)
        gsub(/^[[:space:]]+|[[:space:]]+$/, "", right)
        if (left == "") { ll = 0 } else { tmp = left; gsub(/[^,]/, "", tmp); ll = length(tmp) + 1 }
        if (right == "") { rl = 0 } else { tmp = right; gsub(/[^,]/, "", tmp); rl = length(tmp) + 1 }
        left_dist[ll]++; right_dist[rl]++
        s = substr(s, RSTART + RLENGTH)
      }
    }
  }

  END {
    if (state == "trace") {
      idx++
      pol_size[idx] = saved_pol
      trace_size[idx] = trace_tuples
    }

    printf "\n  %-6s %10s  %14s\n", "elem", "pol_terms", "trace_tuples"
    printf "  %-6s %10s  %14s\n",   "----", "---------", "------------"
    for (i = 1; i <= idx; i++) {
      printf "  B[%-3d] %10d  %14d\n", i, pol_size[i], trace_size[i]
    }

    # Compute simple summary stats over trace_size and pol_size.
    if (idx > 0) {
      tmin = trace_size[1]; tmax = tmin; tsum = 0
      pmin = pol_size[1];   pmax = pmin; psum = 0
      for (i = 1; i <= idx; i++) {
        if (trace_size[i] < tmin) tmin = trace_size[i]
        if (trace_size[i] > tmax) tmax = trace_size[i]
        tsum += trace_size[i]
        if (pol_size[i] < pmin) pmin = pol_size[i]
        if (pol_size[i] > pmax) pmax = pol_size[i]
        psum += pol_size[i]
      }
      printf "\n  trace length:  min=%d  mean=%d  max=%d\n", tmin, tsum/idx, tmax
      printf "  pol terms:     min=%d  mean=%d  max=%d\n",   pmin, psum/idx, pmax
    }

    print ""
    print "  word len | left tuples |  right tuples"
    print "  -------- | ----------- |  ------------"
    maxlen = 0
    for (l in left_dist)  if (l+0 > maxlen) maxlen = l+0
    for (l in right_dist) if (l+0 > maxlen) maxlen = l+0
    for (l = 0; l <= maxlen; l++) {
      if ((l in left_dist) || (l in right_dist)) {
        lc = (l in left_dist)  ? left_dist[l]  : 0
        rc = (l in right_dist) ? right_dist[l] : 0
        printf "  %8d | %11d |  %12d\n", l, lc, rc
      }
    }
  }
' "$file"

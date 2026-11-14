#!/bin/bash
# X2 axiom and hygiene audit.
#
# Usage (from anywhere; the repo root is found from the script location), after the X2 modules are built
# (`lake build PrimeBHT.TimeFrequency.X2.Final`):
#     scripts/axiom_audit_x2.sh
#
# Part 1 (axioms).  Writes a scratch Lean file into a temporary directory (nothing under the repo or `.lake` is
# written), importing the key X2 modules and running `#print axioms` on the headline theorems; fails if any theorem
# depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`, if a name does not resolve, or if
# Lean reports an error.
#
# Part 2 (source hygiene).  Scans every `.lean` file under `PrimeBHT/TimeFrequency/X2/` for the tokens
#     sorry, sorryAx, admit, native_decide, axiom, maxHeartbeats, unsafe, opaque, implemented_by
# as whole words, in CODE only (comments `-- ...`, `/- ... -/` (nested) and string literals are stripped first;
# matches that occur only inside comments are listed separately as information, they do not fail).
#
# Exit status 0 iff both parts are clean.
#
# `AXIOM_AUDIT_LEAN` overrides the command used to run Lean (default `lake env lean`).
set -u
cd "$(dirname "$0")/.." || exit 2

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/axiom_audit_x2.XXXXXX")" || exit 2
trap 'rm -rf "$tmpdir"' EXIT
scratch="$tmpdir/AxiomAuditX2.lean"

NS="PrimeBHT.TimeFrequency.X2"
# Headline declarations (fully qualified). Keep this list in sync with docs/x2-proof-map.md.
NAMES=(
  "$NS.x2Statement_final"
  "$NS.x2Statement_of_selectable"
  "$NS.oSelectable_proved"
  "$NS.kernel_DT"
  "$NS.Absorb.quadrantKernel"
  "$NS.pint_nonHilbert_O"
  "$NS.overlap_O2"
  "$NS.x2Statement_of_hyps"
  "$NS.x2Statement_of_v16"
  "$NS.discretization"
  "$NS.V16.v16_of_hyps_rev5_nonHilbert"
  "$NS.energyLemmaTopG_nonHilbert"
  "$NS.treeLemmaSingleScale"
  "$NS.engLeTailMass"
  "$NS.energyLemmaO"
  "$NS.hardPart_of_overlapPspLean"
  "$NS.treeLemmaRev2_of_O2"
  "$NS.pint_two_O_statement"
  "$NS.goodTree_maxTree"
  "$NS.top_separation_pair"
)

{
  echo "import $NS.Final"
  echo "import $NS.TopSelect"
  echo "import $NS.GoodTree"
  echo "import $NS.EngTail.Tree"
  echo "import $NS.EnergyLemmaO"
  echo "import $NS.Psp.TreeHardFinal"
  echo "import $NS.Psp.OverlapAssemble"
  echo "import $NS.Ortho.PintNested"
  echo "import $NS.TreeS.Main"
  echo "import $NS.TreeS.FinalTB4"
  echo "import $NS.TopEnergy.MainNH"
  echo "import $NS.Disc.Final"
  echo
  for n in "${NAMES[@]}"; do echo "#print axioms $n"; done
  echo '#eval IO.println "axiom_audit_x2: scratch file ran to the end"'
} > "$scratch"

lean_cmd="${AXIOM_AUDIT_LEAN:-lake env lean}"
echo "== Part 1: #print axioms for ${#NAMES[@]} headline theorems =="
# shellcheck disable=SC2086
output="$($lean_cmd "$scratch" 2>&1)"
status=$?
fail=0

printf '%s\n' "$output" > "$tmpdir/lean_output.txt"
python3 - "$tmpdir/lean_output.txt" "${NAMES[@]}" <<'PY'
import re, sys
out = open(sys.argv[1], encoding="utf-8").read()
names = sys.argv[2:]
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = False
if "scratch file ran to the end" not in out:
    print("FAIL: the scratch file did not run to the end (module not built, or Lean error)")
    bad = True
for line in out.splitlines():
    if re.search(r"\berror\b", line) or "declaration uses" in line:
        print("FAIL: Lean reported:", line); bad = True
# collapse wrapped lines, then parse
flat = re.sub(r"\s+", " ", out)
found = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat):
    found[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
for m in re.finditer(r"'([^']+)' does not depend on any axioms", flat):
    found[m.group(1)] = set()
for n in names:
    if n not in found:
        print(f"FAIL: {n}: no `#print axioms` result (name does not resolve?)"); bad = True; continue
    extra = found[n] - allowed
    if extra:
        print(f"FAIL: {n}: nonstandard axioms {sorted(extra)}"); bad = True
    else:
        print(f"ok    {n}: {sorted(found[n]) if found[n] else 'no axioms'}")
sys.exit(1 if bad else 0)
PY
[ $? -eq 0 ] || fail=1
if [ "$status" -ne 0 ]; then
  echo "FAIL: lean exited with status $status"
  printf '%s\n' "$output" | head -30
  fail=1
fi

echo
echo "== Part 2: forbidden tokens in code of PrimeBHT/TimeFrequency/X2/**/*.lean =="
python3 - <<'PY'
import os, re, sys
root = "PrimeBHT/TimeFrequency/X2"
pats = ["sorry", "sorryAx", "admit", "native_decide", "axiom", "maxHeartbeats", "unsafe", "opaque", "implemented_by"]
rx = re.compile(r"(?<![A-Za-z0-9_'.])(" + "|".join(pats) + r")(?![A-Za-z0-9_'])")

def strip(src):
    """Return (code, comments) with the same line structure: comments and strings blanked out of `code`."""
    code, com = [], []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        two = src[i:i+2]
        if depth > 0:
            if two == "/-":
                depth += 1; code.append("  "); com.append(two); i += 2
            elif two == "-/":
                depth -= 1; code.append("  "); com.append(two); i += 2
            else:
                code.append("\n" if c == "\n" else " "); com.append(c); i += 1
        elif two == "/-":
            depth = 1; code.append("  "); com.append(two); i += 2
        elif two == "--":
            j = src.find("\n", i)
            j = n if j < 0 else j
            code.append(" " * (j - i)); com.append(src[i:j]); i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            seg = src[i:j]
            code.append("".join("\n" if ch == "\n" else " " for ch in seg)); com.append(seg); i = j
        else:
            code.append(c); com.append("\n" if c == "\n" else " "); i += 1
    return "".join(code), "".join(com)

files = []
for d, _, fs in os.walk(root):
    for f in fs:
        if f.endswith(".lean"):
            files.append(os.path.join(d, f))
files.sort()
code_hits, comment_hits = [], []
for p in files:
    src = open(p, encoding="utf-8").read()
    code, com = strip(src)
    for ln, line in enumerate(code.split("\n"), 1):
        for m in rx.finditer(line):
            code_hits.append((p, ln, m.group(1), src.split("\n")[ln-1].strip()[:120]))
    for ln, line in enumerate(com.split("\n"), 1):
        for m in rx.finditer(line):
            comment_hits.append((p, ln, m.group(1), src.split("\n")[ln-1].strip()[:120]))
print(f"scanned {len(files)} files")
for h in code_hits:
    print("FAIL (code): %s:%d: %s: %s" % h)
for h in comment_hits:
    print("info (comment/string only): %s:%d: %s: %s" % h)
print(f"code hits: {len(code_hits)}; comment-only hits: {len(comment_hits)}")
sys.exit(1 if code_hits else 0)
PY
[ $? -eq 0 ] || fail=1

echo
if [ "$fail" -ne 0 ]; then
  echo "axiom_audit_x2: FAILED"
  exit 1
fi
echo "axiom_audit_x2: all checks passed"

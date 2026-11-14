#!/bin/bash
# Interface check: the non-frozen Props consumed by the proofs equal the frozen statements.
#
# Usage (from the repo root, after the project modules it imports are built):
#     scripts/interface_check.sh
#
# Writes a scratch Lean file from scripts/interface_check.lean.txt into a temporary directory (nothing under
# the repo or `.lake` is written), runs `lake env lean` on it, and exits non-zero if elaboration fails
# (any `rfl`/proof check in the template), if the output contains an error or a `sorry` warning, or if the
# final sentinel line is missing. See the header of the template for exactly what is checked and why.
#
# The imports include QUARANTINED frozen modules (`PrimeBHT.Frozen.{X1,FiniteBV,Key0,MainTheorem}`): they are
# imported only by this scratch file, never by anything under `PrimeBHT/`.
#
# `INTERFACE_CHECK_LEAN` overrides the command used to run Lean (default `lake env lean`), e.g. to point
# `LEAN_PATH` at a directory of scratch `.olean` files before the new modules are added to the lake build.
set -u
cd "$(dirname "$0")/.." || exit 2

template="scripts/interface_check.lean.txt"
[ -f "$template" ] || { echo "interface_check: missing $template" >&2; exit 2; }

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/interface_check.XXXXXX")" || exit 2
trap 'rm -rf "$tmpdir"' EXIT
scratch="$tmpdir/InterfaceCheck.lean"
cp "$template" "$scratch"

lean_cmd="${INTERFACE_CHECK_LEAN:-lake env lean}"
# shellcheck disable=SC2086
output="$($lean_cmd "$scratch" 2>&1)"
status=$?
printf '%s\n' "$output"

fail=0
if [ "$status" -ne 0 ]; then
  echo "interface_check: FAILED (lean exited with status $status)" >&2
  fail=1
fi
if printf '%s\n' "$output" | grep -qE 'error|declaration uses .sorry.'; then
  echo "interface_check: FAILED (lean reported an error or a sorry)" >&2
  fail=1
fi
if ! printf '%s\n' "$output" | grep -qF 'interface_check: all checks passed'; then
  echo "interface_check: FAILED (the sentinel line is missing: the scratch file did not run to the end)" >&2
  echo "  (if a module is reported as not built, build it first, e.g. lake build PrimeBHT.Interface.X1Statement)" >&2
  fail=1
fi
if [ "$fail" -ne 0 ]; then
  exit 1
fi
echo "interface_check: OK (X1Statement, X2Statement, M2Prop, M1Prop, M1Statement, Key0Statement, X3Statement, t_maintheorem_of_inputs, t_maintheorem_of_x1_x2 and t_maintheorem_of_m1_x2 match the frozen or sealed statements)"

#!/usr/bin/python3 -I
"""Elaborated-ABI hashes of the frozen declarations (adapted from the earlier project's script).

Usage (from the repo root, after the frozen modules are built):
    scripts/frozen_abi.py [--compare <approved.lean.txt>]

Prints the SHA-256 of the fully elaborated declaration (`#print` with `pp.all` for a definition,
`#check @` with `pp.all` for a theorem, so a theorem's hash does not depend on its proof), after
whitespace collapsing and replacing auxiliary proof constants `X._proof_N` by `_proof_`.
With `--compare`, the approved file is elaborated in the namespace `PrimeBHT.StatementsApproved1`
(as a `module`, importing only the frozen modules) and compared with the frozen declarations.
"""
import hashlib, json, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NS = "PrimeBHT.Statements"
GROUPS = {
    "T0": [("PrimeBHT.Frozen.PrimeBHT", "primeBHT", "def"),
           ("PrimeBHT.Frozen.MainTheorem", "t_maintheorem", "theorem")],
    "Key0": [("PrimeBHT.Frozen.IsCutoff", "IsCutoff", "def"),
             ("PrimeBHT.Frozen.Psi", "psi", "def"),
             ("PrimeBHT.Frozen.PsiK", "psiK", "def"),
             ("PrimeBHT.Frozen.UOp", "uOp", "def"),
             ("PrimeBHT.Frozen.Key0", "p_key0", "theorem")],
    "X1": [("PrimeBHT.Frozen.BhtTrunc", "bhtTrunc", "def"),
           ("PrimeBHT.Frozen.X1", "x1_bht_smooth", "theorem")],
    "X2": [("PrimeBHT.Frozen.YNorm", "yNorm", "def"),
           ("PrimeBHT.Frozen.TensorFun", "tensorFun", "def"),
           ("PrimeBHT.Frozen.TensorFourier", "tensorFourier", "def"),
           ("PrimeBHT.Frozen.MultiplierForm", "multiplierForm", "def"),
           ("PrimeBHT.Frozen.FiniteBV", "t_finiteBV", "theorem")],
    "M2": [("PrimeBHT.Frozen.BhtKernelR", "bhtKernelR", "def"),
           ("PrimeBHT.Frozen.BhtOpR", "bhtOpR", "def"),
           ("PrimeBHT.Frozen.BhtRealSmooth", "bht_real_smooth", "theorem")],
    "M1": [("PrimeBHT.Frozen.TriValid", "TriValid", "def"),
           ("PrimeBHT.Frozen.TriIdx", "triIdx", "def"),
           ("PrimeBHT.Frozen.TimeInt", "timeInt", "def"),
           ("PrimeBHT.Frozen.FreqNum", "freqNum", "def"),
           ("PrimeBHT.Frozen.FreqInt", "freqInt", "def"),
           ("PrimeBHT.Frozen.IntervalCentre", "intervalCentre", "def"),
           ("PrimeBHT.Frozen.IsAdapted", "IsAdapted", "def"),
           ("PrimeBHT.Frozen.Pairing", "pairing", "def"),
           ("PrimeBHT.Frozen.TriForm", "triForm", "def"),
           ("PrimeBHT.Frozen.TriRestrictedEps", "tri_restricted_eps", "theorem")],
}
# Names of frozen declarations OUTSIDE a group that the group's approved text uses unqualified
# (made visible in the comparison namespace by `open PrimeBHT.Statements (name)`).
EXTERNAL_NAMES = {"X1": ["IsCutoff"], "M2": ["IsCutoff"]}
# definitions of the included earlier project (author-approved there; bound here by hash): (module, full name, kind)
VENDORED = [("PrimeCarleson.Frozen.Exp", "PrimeCarleson.e", "def"),
            ("PrimeCarleson.Frozen.RamanujanSum", "PrimeCarleson.ramanujanSum", "def"),
            ("PrimeCarleson.Frozen.BlockWeight", "PrimeCarleson.blockWeight", "def")]

def split_name(f):
    """('PrimeBHT.Statements', 'TriParam.Idx') for frozen names (dotted remainder allowed), else rsplit."""
    if f.startswith(NS + "."):
        return NS, f[len(NS) + 1:]
    return tuple(f.rsplit(".", 1))

def normalize(block):
    block = re.sub(r"\b[\w.']+\._proof_\d+\b", "_proof_", block)
    return " ".join(block.split())

def run_lean(text):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as fh:
        fh.write(text); path = fh.name
    try:
        res = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(path)
    if res.returncode != 0 and "error" in res.stdout:
        sys.exit("lean failed:\n" + res.stdout[-4000:] + res.stderr[-2000:])
    return res.stdout

def blocks(output, prefixes):
    pat = "|".join(re.escape(p) for p in prefixes)
    start = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem|structure)\s+(" + pat + r")\.([\w'.]+)"
                       r"|^@?(" + pat + r")\.([\w'.]+) :")
    found, current, buf = {}, None, []
    for line in output.split("\n") + ["/end"]:
        m = start.match(line)
        if m or line.startswith("/"):
            if current: found[current] = "\n".join(buf)
            current = (m.group(1) or m.group(3), m.group(2) or m.group(4)) if m else None
            buf = [line] if m else []
        elif current:
            buf.append(line)
    return found

def cmds(entries):
    out = ["set_option pp.all true"]
    for ns, name, kind in entries:
        out.append(f"#print {ns}.{name}" if kind in ("def", "structure") else f"#check @{ns}.{name}")
    return out

def main():
    args, approved = sys.argv[1:], {}
    while args:
        if args[0] != "--compare" or len(args) < 2 or "=" not in args[1]:
            sys.exit("usage: frozen_abi.py [--compare GROUP=<approved file>]...")
        g, path = args[1].split("=", 1); approved[g] = path; args = args[2:]
    allm = [(m, NS + "." + n, k) for grp in GROUPS.values() for m, n, k in grp] + VENDORED
    lines = ["import " + m for m, _, _ in allm] + [""]
    lines += ["set_option pp.all true"] + [(f"#print {f}" if k in ("def", "structure") else f"#check @{f}") for _, f, k in allm]
    out = run_lean("\n".join(lines) + "\n")
    found = {}
    for _, f, k in allm:
        ns, name = split_name(f)
        found.update(blocks(out, [ns]))
    result = {}
    for m, f, k in allm:
        ns, name = split_name(f)
        text = found.get((ns, name))
        if text is None: sys.exit(f"no output for {f}")
        result[f] = {"module": m, "kind": k, "abi_sha256": hashlib.sha256(normalize(text).encode()).hexdigest()}
    ok = True
    for idx, (g, path) in enumerate(sorted(approved.items()), 1):
        mine = GROUPS[g]; ns = f"PrimeBHT.StatementsApproved{idx}"
        src = open(path, encoding="utf-8").read()
        body = src[src.index("open MeasureTheory"):]
        ext = EXTERNAL_NAMES.get(g, [])
        body = body.replace("namespace PrimeBHT.Statements", f"namespace {ns}").replace("end PrimeBHT.Statements", f"end {ns}")
        ext_imports = ["public import PrimeBHT.Frozen.IsCutoff"] if ext else []
        ext_open = ["open PrimeBHT.Statements (" + " ".join(ext) + ")", ""] if ext else []
        lines = (["module", ""] + ["public import " + m for m, _, _ in mine] + ext_imports
                 + ["", "@[expose] public noncomputable section", ""] + ext_open + [body, ""])
        lines += ["set_option pp.all true"] + [(f"#print {s_}.{n}" if kd in ("def", "structure") else f"#check @{s_}.{n}") for _, n, kd in mine for s_ in (ns, NS)]
        other = blocks(run_lean("\n".join(lines) + "\n"), [ns, NS])
        for _, name, _ in mine:
            a, f = other.get((ns, name), ""), other.get((NS, name), "")
            same = bool(a) and bool(f) and normalize(re.sub(r"\b" + re.escape(ns) + r"\b", NS, a)) == normalize(f)
            result[NS + "." + name]["matches_approved"] = same; ok &= same
    print(json.dumps(result, indent=1))
    if approved and not ok:
        sys.exit("MISMATCH between frozen and approved declarations")
    if approved: print("ALL MATCH APPROVED")

main()

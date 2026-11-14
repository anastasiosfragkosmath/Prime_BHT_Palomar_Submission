#!/usr/bin/python3 -I
"""Check the included closure of the earlier project and the three frozen definitions bound by hash.

Usage (from anywhere): python3 -I scripts/check_dependency.py [--dep DIR]

The part of the author's formalization *A Variation Norm Carleson Theorem Along the Primes* that this repository needs (the
input X3, the U^3 approximation of the von Mangoldt function) is included in `PrimeCarleson/`, `vendor/openai-math/OAI/` and
`vendor/carleson/Carleson/`, in the layout of that project, and is built from here as the Lake libraries `PrimeCarleson`,
`OAI` and `Carleson` of this package. No Lake dependency on that project exists.

Checks (exit status 1 on any failure):
 1. the three frozen definitions bound by hash in scripts/data/frozen-manifest.json
    (`PrimeCarleson.e`, `ramanujanSum`, `blockWeight`) match their manifest hashes;
 2. the included sources are closed: every `import` of a module of `PrimeCarleson`, `OAI` or `Carleson`, in `PrimeBHT/`,
    `Challenge.lean`, `Solution.lean` and the included files themselves, resolves to an included file;
 3. if the earlier project is available as a git checkout (default `../variational-carleson-lean`, or `--dep DIR`) and has
    the pinned revision, every included file is byte-identical to that revision's file (git blob hash), and both use the same
    toolchain and Mathlib revision. Without such a checkout, check 3 is skipped and reported as SKIP.
"""
import hashlib, json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PIN = "f0f9299287feeaea25f6b9cedd3e078b4a98f3c7"
DEP = os.path.normpath(os.path.join(ROOT, "..", "variational-carleson-lean"))
if "--dep" in sys.argv:
    DEP = os.path.abspath(sys.argv[sys.argv.index("--dep") + 1])
SRC = {"PrimeCarleson": "", "OAI": "vendor/openai-math", "Carleson": "vendor/carleson"}
TREES = ["PrimeCarleson", "vendor"]  # every file below these directories is included material

def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()

def git(*args, cwd=None):
    r = subprocess.run(["git", *args], capture_output=True, text=True, cwd=cwd)
    return r.stdout.strip()

def strip(t):
    """Remove Lean comments: nested block comments and line comments."""
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        two = t[i:i + 2]
        if two == "/-":
            depth += 1; i += 2
        elif two == "-/" and depth:
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif two == "--":
            j = t.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(t[i]); i += 1
    return "".join(out)

IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)\s*$", re.M)

ok = True
def check(cond, msg):
    global ok
    print(("OK   " if cond else "FAIL ") + msg)
    ok &= bool(cond)

# 1. frozen definitions bound by hash
manifest = json.load(open(os.path.join(ROOT, "scripts", "data", "frozen-manifest.json")))
bound = [a for a in manifest["anchors"] if a.get("path", "").startswith("PrimeCarleson/")]
check(len(bound) == 3, f"the manifest binds {len(bound)} included frozen definitions (expected 3)")
for a in bound:
    p = os.path.join(ROOT, a["path"])
    check(os.path.exists(p) and sha(p) == a["full_file_sha256"], f"{a['path']}: included copy = manifest hash")

# 2. closure
included = []
for t in TREES:
    for r, _, fs in os.walk(os.path.join(ROOT, t)):
        included += [os.path.relpath(os.path.join(r, f), ROOT) for f in fs if f != ".DS_Store"]
lean = sorted(f for f in included if f.endswith(".lean"))
print(f"included files: {len(included)} ({len(lean)} Lean)")
scan = list(lean)
for r, _, fs in os.walk(os.path.join(ROOT, "PrimeBHT")):
    scan += [os.path.relpath(os.path.join(r, f), ROOT) for f in fs if f.endswith(".lean")]
scan += ["PrimeBHT.lean", "Challenge.lean", "Solution.lean"]
unresolved = set()
for f in scan:
    for m in IMPORT.findall(strip(open(os.path.join(ROOT, f), encoding="utf-8").read())):
        top = m.split(".")[0]
        if top in SRC and not os.path.exists(os.path.join(ROOT, SRC[top], m.replace(".", "/") + ".lean")):
            unresolved.add(m)
check(not unresolved, f"every import of PrimeCarleson/OAI/Carleson resolves to an included file ({len(unresolved)} unresolved"
      + (f": {sorted(unresolved)[:3]}" if unresolved else "") + ")")

# 3. comparison with the earlier project's pinned revision
if os.path.isdir(os.path.join(DEP, ".git")) and git("cat-file", "-t", PIN, cwd=DEP) == "commit":
    check(True, f"earlier project has the pinned revision {PIN[:12]}")
    bad = []
    for rel in included:
        want = git("rev-parse", f"{PIN}:{rel}", cwd=DEP)
        have = git("hash-object", os.path.join(ROOT, rel))
        if want != have:
            bad.append(rel)
    check(not bad, f"all included files equal the pinned revision's files ({len(bad)} differ{': ' + bad[0] if bad else ''})")
    tc = lambda d: open(os.path.join(d, "lean-toolchain")).read().strip()
    check(tc(DEP) == tc(ROOT), f"same toolchain ({tc(ROOT)})")
    mathlib = lambda d: [p["rev"] for p in json.load(open(os.path.join(d, "lake-manifest.json")))["packages"] if p["name"] == "mathlib"]
    check(mathlib(DEP) == mathlib(ROOT), f"same Mathlib revision ({mathlib(ROOT)[0][:10]})")
else:
    print("SKIP the comparison with the earlier project's pinned revision (no git checkout with that revision at " + DEP + ")")
sys.exit(0 if ok else 1)

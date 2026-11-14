#!/usr/bin/python3 -I
"""Static layout checks of the submission snapshot (the files git tracks or would track), run from the repository root:
 - every .lean file (except lakefile.lean) starts with `module` (comments may precede it) and has at most 10,000 lines;
 - Challenge.lean has at most 1,000 lines / 100 KiB and imports only Lean core and Mathlib;
 - no compiled artifacts, no symlinked .lean files, no submodules, no file over 50 MB, total at most 500 MiB;
 - the only Markdown files are README.md, semantic-audit.md, verification-report.md and the two provenance notes of the
   included third-party code (vendor/README.md, vendor/provenance/THIRD-PARTY.md);
 - exactly one root licence file, containing the Apache-2.0 text, and `license: Apache-2.0` in formalization.yaml;
 - `sorry` occurs in code only in Challenge.lean (comments stripped), including the included sources under PrimeCarleson/ and vendor/;
 - no obvious secret patterns.
"""
import os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
files = sorted(x for x in subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
               capture_output=True, check=True).stdout.decode().split("\0") if x and os.path.exists(x))
ok = True
def check(c, m):
    global ok
    print(("OK   " if c else "FAIL ") + m); ok &= bool(c)

def strip(t):
    """Remove Lean comments: nested block comments `/- ... -/` and line comments `-- ...`."""
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

lean = [f for f in files if f.endswith(".lean") and os.path.basename(f) != "lakefile.lean"]
nomod = [f for f in lean if not strip(open(f, encoding="utf-8").read()).lstrip().startswith("module")]
long_ = [f for f in lean if open(f, encoding="utf-8").read().count("\n") > 10000]
check(not nomod, f"all {len(lean)} Lean files start with `module`" + (f" (violations: {nomod[:3]})" if nomod else ""))
check(not long_, "no Lean file over 10,000 lines")
ch = open("Challenge.lean", encoding="utf-8").read()
check(ch.count("\n") <= 1000 and len(ch.encode()) <= 100 * 1024, f"Challenge.lean size ({ch.count(chr(10))} lines, {len(ch.encode())} bytes)")
imps = re.findall(r"^\s*(?:public\s+)?import\s+(\S+)", strip(ch), re.M)
check(all(i.split(".")[0] in ("Mathlib", "Lean", "Std", "Init") for i in imps), f"Challenge.lean imports only Mathlib/core ({len(imps)} imports)")
bad = [f for f in files if re.search(r"\.(olean|ilean|a|bc|dll|dylib|o|obj|so|trace)$", f)]
check(not bad, "no compiled artifacts")
check(not any(os.path.islink(f) for f in files), "no symbolic links")
check(not os.path.exists(".gitmodules"), "no git submodules")
sizes = {f: os.path.getsize(f) for f in files}
check(max(sizes.values()) < 50e6, f"largest file {max(sizes, key=sizes.get)} = {max(sizes.values())/1e6:.1f} MB")
check(sum(sizes.values()) < 500 * 2**20, f"total {sum(sizes.values())/2**20:.1f} MiB (< 500 MiB)")
allowed = {"README.md", "semantic-audit.md", "verification-report.md", "vendor/README.md", "vendor/provenance/THIRD-PARTY.md"}
md = [f for f in files if f.lower().endswith((".md", ".markdown"))]
check(set(md) <= allowed, f"Markdown files: {md}")
lic = [f for f in os.listdir(".") if re.fullmatch(r"(LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(\.md|\.markdown|\.txt)?", f, re.I)]
check(lic == ["LICENSE"] and "Apache License" in open("LICENSE", encoding="utf-8").read()
      and re.search(r"^\s*license:\s*Apache-2\.0\s*$", open("formalization.yaml", encoding="utf-8").read(), re.M),
      f"one root licence file {lic}, Apache-2.0, matches formalization.yaml")
sorry = [f for f in lean if re.search(r"\bsorry\b", strip(open(f, encoding="utf-8").read()))]
check(sorry == ["Challenge.lean"], f"`sorry` in code only in Challenge.lean (found: {sorry})")
pat = re.compile(r"ghp_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|sk-ant-|AKIA[0-9A-Z]{16}|-----BEGIN (?:RSA |OPENSSH |EC )?PRIVATE KEY|xox[baprs]-")
hits = [f for f in files if f != 'scripts/check_layout.py' and sizes[f] < 5e6 and pat.search(open(f, encoding="utf-8", errors="ignore").read())]
check(not hits, f"no secret-like strings{(' (' + str(hits[:3]) + ')') if hits else ''}")
print(f"{len(files)} files in the snapshot")
sys.exit(0 if ok else 1)

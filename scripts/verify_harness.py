#!/usr/bin/env python3
"""
Local 3-gate verification harness for Arithmetica4 (Lean 4 v4.33.1).

Gates:
  1. Static zero-cheat scan (comment-stripped): 0 sorry, admit, custom axiom,
     opaque, native_decide, unsafe, implemented_by, extern, import Mathlib.
  2. Local `lake build <Module>` + official `lake env leanchecker <Module>`.
  3. Exhaustive axiom audit verifying every constant in the module depends
     strictly on `{propext, Classical.choice, Quot.sound}`.

Usage:
  python3 scripts/verify_harness.py RHDirect/DworkWeil1Unconditional.lean [RHDirect/VinogradovThreePrimes.lean ...]
"""
import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def strip_lean_comments(src: str) -> str:
    out = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                i += 2
            elif c == "-" and nxt == "/":
                depth -= 1
                i += 2
            else:
                if c == "\n":
                    out.append("\n")
                i += 1
            continue
        if in_str:
            if c == "\\" and i + 1 < n:
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
        elif c == "/" and nxt == "-":
            depth += 1
            i += 2
        elif c == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def static_cheat_scan(path: pathlib.Path) -> list[str]:
    clean = strip_lean_comments(path.read_text(encoding="utf-8"))
    hits = []
    for idx, line in enumerate(clean.splitlines(), 1):
        if re.search(r"\b(sorry|admit|native_decide)\b", line):
            hits.append(f"{path}:{idx}: forbidden token -> {line.strip()[:80]}")
        if re.match(r"^\s*(axiom|opaque|unsafe)\b", line):
            hits.append(f"{path}:{idx}: forbidden decl -> {line.strip()[:80]}")
        if re.search(r"@\[(implemented_by|extern)\b", line):
            hits.append(f"{path}:{idx}: forbidden attribute -> {line.strip()[:80]}")
        if re.match(r"^\s*import\s+Mathlib\s*$", line):
            hits.append(f"{path}:{idx}: monolithic `import Mathlib` forbidden")
    return hits


def module_name_from_path(root: pathlib.Path, p: pathlib.Path) -> str:
    rel = p.resolve().relative_to(root.resolve())
    return ".".join(rel.with_suffix("").parts)


def check_axioms(root: pathlib.Path, mod: str) -> tuple[bool, int, list[str]]:
    script = f"""import {mod}
import Lean

open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `{mod}
    | throwError "module `{mod}` not found"
  let names := env.header.moduleData[modIdx.toNat]!.constNames
  let allowed : Std.HashSet Name := ({{}} : Std.HashSet Name).insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound
  let mut bad : Array String := #[]
  for n in names do
    let axs ← Lean.collectAxioms n
    for ax in axs do
      if !allowed.contains ax then
        bad := bad.push s!"{{n}}: {{ax}}"
  IO.println s!"CONST_COUNT={{names.size}}"
  IO.println s!"BAD_COUNT={{bad.size}}"
  for b in bad do
    IO.println s!"BAD={{b}}"
"""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=str(root), delete=False, encoding="utf-8") as tf:
        tf.write(script)
        tmp_path = pathlib.Path(tf.name)
    try:
        res = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            cwd=str(root),
            capture_output=True,
            text=True,
        )
        if res.returncode != 0:
            return False, 0, [f"axiom check script failed: {(res.stdout + res.stderr)[-400:]}"]
        count, bad = 0, []
        for line in res.stdout.splitlines():
            if line.startswith("CONST_COUNT="):
                count = int(line.split("=", 1)[1])
            elif line.startswith("BAD="):
                bad.append(line.split("=", 1)[1])
        return len(bad) == 0, count, bad
    finally:
        tmp_path.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="+", help="Lean source files (e.g. RHDirect/DworkWeil1Unconditional.lean)")
    parser.add_argument("--skip-build", action="store_true", help="Skip `lake build` (assume .olean already built)")
    args = parser.parse_args()

    root = pathlib.Path(__file__).resolve().parent.parent
    failed = False

    for f in args.files:
        p = (root / f) if not pathlib.Path(f).is_absolute() else pathlib.Path(f)
        if not p.is_file():
            print(f"[FAIL] File not found: {p}", file=sys.stderr)
            failed = True
            continue
        mod = module_name_from_path(root, p)
        print(f"=== Verifying {mod} ({p.relative_to(root)}) ===")

        hits = static_cheat_scan(p)
        if hits:
            print("  [GATE 1 FAIL] Static cheat scan:")
            for h in hits[:10]:
                print("   ", h)
            failed = True
            continue
        print("  [GATE 1 PASS] Static zero-cheat scan: 0 hits")

        if not args.skip_build:
            b = subprocess.run(["lake", "build", mod], cwd=str(root))
            if b.returncode != 0:
                print(f"  [GATE 2 FAIL] `lake build {mod}` failed")
                failed = True
                continue

        lc = subprocess.run(["lake", "env", "leanchecker", mod], cwd=str(root))
        if lc.returncode != 0:
            print(f"  [GATE 2 FAIL] `leanchecker {mod}` failed")
            failed = True
            continue
        print(f"  [GATE 2 PASS] `leanchecker {mod}`: PASS")

        ok, count, bad = check_axioms(root, mod)
        if not ok:
            print(f"  [GATE 3 FAIL] Unexpected axioms ({len(bad)}):")
            for b in bad[:10]:
                print("   ", b)
            failed = True
            continue
        print(f"  [GATE 3 PASS] Exhaustive axiom audit: {count} constants, strictly ⊆ {{propext, Classical.choice, Quot.sound}}")

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

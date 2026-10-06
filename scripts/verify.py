#!/usr/bin/env python3
"""Verify the declared algebraic supplement, not the manuscript's main theorem."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
RESULT = re.compile(
    r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|"
    r"does not depend on any axioms)\s*$", re.MULTILINE
)


def check_sources(root):
    manifest = json.loads((root / "verification/source-manifest.json").read_text())
    if manifest["main_theorem_verified"] is not False:
        raise ValueError("The declared scope must remain partial.")
    actual = {str(p.relative_to(root)) for p in (root / "Suzuki").rglob("*.lean")}
    actual |= {str(p.relative_to(root)) for p in root.glob("*.lean")}
    expected = manifest["files"]
    if actual != {name for name in expected if name.endswith(".lean")}:
        raise ValueError("Lean source set differs from the manifest.")
    for name, digest in expected.items():
        if Path(name).is_absolute() or ".." in Path(name).parts:
            raise ValueError(f"Non-relative manifest path: {name}")
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f"Source hash differs: {name}")
    requested = re.findall(r"^#print axioms (\S+)$", (root / "Audit.lean").read_text(), re.MULTILINE)
    if requested != manifest["audited_declarations"] or len(set(requested)) != len(requested):
        raise ValueError("Audit declaration list differs or contains duplicates.")
    declared = []
    for name in sorted((root / "Suzuki").glob("*.lean")):
        namespace = "Suzuki." + name.stem
        declared += [namespace + "." + n for n in re.findall(
            r"^(?:def|theorem) (\w+)", name.read_text(), re.MULTILINE)]
    if set(declared) != set(requested):
        raise ValueError("The audit does not cover every submitted declaration.")
    return requested


def check_axioms(output, expected):
    results = {}
    for match in RESULT.finditer(output):
        name, raw = match.groups()
        if name in results:
            raise ValueError(f"Duplicate audit result: {name}")
        axioms = {x.strip() for x in (raw or "").split(",") if x.strip()}
        if axioms - ALLOWED_AXIOMS:
            raise ValueError(f"Unexpected axioms for {name}: {sorted(axioms - ALLOWED_AXIOMS)}")
        results[name] = axioms
    if RESULT.sub("", output).strip():
        raise ValueError("Unparsed audit output or compiler diagnostics.")
    if set(results) != set(expected):
        raise ValueError("Audit output does not cover the exact declaration list.")
    return results


def main():
    try:
        expected = check_sources(ROOT)
        print("Scope: algebraic lemmas only; main theorem NOT verified in Lean.", flush=True)
        subprocess.run(["lake", "build"], cwd=ROOT, check=True)
        result = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"],
            cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        checked = check_axioms(result.stdout, expected)
        print(result.stdout, end="")
        print(f"PASS: 8 algebraic theorems; {len(checked)} declarations audited.")
        print("This is not a Lean verification of the manuscript's main theorem.")
        return 0
    except subprocess.CalledProcessError as error:
        if error.stdout:
            print(error.stdout, file=sys.stderr)
        print(f"Verification failed: {error}", file=sys.stderr)
    except (OSError, ValueError, KeyError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())

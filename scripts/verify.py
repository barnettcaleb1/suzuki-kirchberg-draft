#!/usr/bin/env python3
"""Verify all submitted components, not the manuscript's main theorem."""
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
    if json.loads((root / "verification/declarations.json").read_text()) != requested:
        raise ValueError("Declaration inventory differs from the audit list.")
    expected_imports = {
        "Suzuki." + p.stem for p in (root / "Suzuki").glob("*.lean")}
    actual_imports = set(re.findall(
        r"^import (Suzuki\.\S+)$", (root / "Suzuki.lean").read_text(), re.MULTILINE))
    if expected_imports != actual_imports:
        raise ValueError("Every submitted module must be imported by the default build.")
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


def check_inventory(output, expected):
    rows = [json.loads(line) for line in output.splitlines() if line.strip()]
    names = []
    for row in rows:
        if set(row) != {"name", "kind", "axioms"}:
            raise ValueError("Malformed compiled declaration inventory.")
        names.append(row["name"])
        if set(row["axioms"]) - ALLOWED_AXIOMS:
            raise ValueError(f"Disallowed axioms in {row['name']}")
        if row["kind"] == "axiom":
            raise ValueError(f"Project axiom declaration: {row['name']}")
    if len(set(names)) != len(names) or set(names) != set(expected):
        raise ValueError("Compiled inventory differs from the exact declaration audit.")
    return rows


def main():
    try:
        expected = check_sources(ROOT)
        print("Scope: partial formalization; main theorem NOT verified in Lean.", flush=True)
        subprocess.run(["lake", "build"], cwd=ROOT, check=True)
        result = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"],
            cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        checked = check_axioms(result.stdout, expected)
        inventory = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=true", "Inventory.lean"],
            cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        check_inventory(inventory.stdout, expected)
        print(result.stdout, end="")
        print(f"PASS: partial modules built; {len(checked)} declarations audited.")
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

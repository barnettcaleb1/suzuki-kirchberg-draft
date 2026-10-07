#!/usr/bin/env python3
"""Check the exact conditional MainClaim proof; external inputs stay conditional."""
from pathlib import Path
import subprocess
import sys
import tempfile

from verify import check_axioms, check_sources

ROOT = Path(__file__).resolve().parents[1]
DECLARATION = "Suzuki.fullTheoremConditional"
SOURCE = """import Suzuki
universe u v w t
set_option linter.checkUnivs false
example {K : Type v} [CategoryTheory.Category.{w} K] [CategoryTheory.Preadditive K]
    (P : Suzuki.PublishedInputs.{u,v,w,t} (K := K)) : Suzuki.Target.MainClaim.{u} :=
  Suzuki.fullTheoremConditional P
#print axioms Suzuki.fullTheoremConditional
"""


def main():
    try:
        check_sources(ROOT)
        subprocess.run(["lake", "build"], cwd=ROOT, check=True)
        with tempfile.TemporaryDirectory(prefix="suzuki-conditional-") as directory:
            target = Path(directory) / "ConditionalVerification.lean"
            target.write_text(SOURCE)
            result = subprocess.run(
                ["lake", "env", "lean", "-DwarningAsError=true", str(target)],
                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode != 0:
            print("NOT VERIFIED: an exact conditional MainClaim proof is required.")
            print(result.stdout, end="")
            return 1
        check_axioms(result.stdout, [DECLARATION])
        print(result.stdout, end="")
        print("PASS: fullTheoremConditional proves exact MainClaim from PublishedInputs.")
        print("Conditional Lean verification only: actual KK realization and published inputs remain external.")
        print("Explicit-hypothesis and manuscript/source correspondence reviews are separate gates.")
        return 0
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"Conditional verification failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

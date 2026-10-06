#!/usr/bin/env python3
"""Require an actual proof of the full MainClaim, with no extra axioms.

This command is intentionally unsuccessful until Suzuki.fullTheorem exists.
A successful build of the partial modules or of the statement is insufficient.
"""
from pathlib import Path
import subprocess
import sys
import tempfile

from verify import check_axioms

ROOT = Path(__file__).resolve().parents[1]
DECLARATION = "Suzuki.fullTheorem"
SOURCE = """import Suzuki
universe u
example : Suzuki.Target.MainClaim.{u} := Suzuki.fullTheorem
#print axioms Suzuki.fullTheorem
"""


def main():
    try:
        subprocess.run(["lake", "build"], cwd=ROOT, check=True)
        with tempfile.TemporaryDirectory(prefix="suzuki-full-") as directory:
            target = Path(directory) / "FullVerification.lean"
            target.write_text(SOURCE)
            result = subprocess.run(
                ["lake", "env", "lean", "-DwarningAsError=true", str(target)],
                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode != 0:
            print("NOT VERIFIED: a checked proof of Suzuki.Target.MainClaim is required.")
            print(result.stdout, end="")
            return 1
        check_axioms(result.stdout, [DECLARATION])
        print("PASS: Suzuki.fullTheorem has the exact MainClaim type and only allowed axioms.")
        print("The correspondence between MainClaim and the manuscript still requires review.")
        return 0
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Full verification failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

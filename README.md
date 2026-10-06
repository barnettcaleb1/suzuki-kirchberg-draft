# Kirchberg algebras as full amalgams of stably finite algebras

**Draft — unverified. The main theorem is not verified in Lean.**

This repository contains Caleb Barnett’s AI-assisted research draft and a Lean 4 supplement that checks selected algebraic lemmas. The manuscript proposes that every unital Kirchberg algebra is a full unital amalgamated free product of separable nuclear simple unital stably finite C*-algebras over a common algebra with the same properties. No UCT hypothesis is assumed on the target. The proposed proof has not received independent human mathematical verification.

Read [the manuscript source](paper.tex) and the [formalization scope](verification/SCOPE.md).

## What Lean checks

Eight general theorems, with their explicit hypotheses, are proved in two modules:

- [Matrix diagrams](Suzuki/MatrixDiagrams.lean): both commuting-square identities, the action on kernel representatives, and preservation of the chain equation and kernel map under a chain-homotopy adjustment. These are identities for arbitrary finite integer matrices of compatible sizes, not finite numerical tests.
- [Idempotent systems](Suzuki/IdempotentSystems.lean): compatible sequences are constant fixed-point sequences; the recursive correction stays in the fixed-point subgroup; and `1 - shift` is surjective for every idempotent additive endomorphism of any abelian group, without a countability hypothesis on that group.

The audit covers all ten declarations, including the two definitions. It rejects dependencies on axioms other than `propext`, `Classical.choice`, and `Quot.sound`. There are no admitted proofs or extra axioms in the submitted modules.

**A passing Lean check here does not verify the C*-algebra construction, the KK-theory argument, or the manuscript’s main theorem.** The remaining obligations are listed in [SCOPE.md](verification/SCOPE.md). No main theorem has been replaced by an assumed axiom or packaged as a conditional theorem and labeled verified.

## Reproduce

Install [elan](https://github.com/leanprover/elan), Python 3, and Git. In this repository run:

```sh
lake exe cache get
python3 scripts/verify.py
```

The toolchain is Lean 4.33.1. Mathlib is pinned to commit `0df444a360eaa60ab8c11dca51a86af692955474`; transitive dependencies are pinned by `lake-manifest.json`. The verifier checks source hashes, builds the two modules, and audits every listed declaration with `#print axioms`. GitHub Actions runs the same checks. Its workflow is named **Lean algebraic checks (partial)** to make the scope visible.

To build the manuscript locally with an existing LaTeX installation, compile `paper.tex`. This repository does not distribute third-party papers or local dependency caches.

## Status and provenance

Public draft 1, 6 October 2026. The mathematical manuscript and Lean supplement were developed with substantial AI assistance. Automated compilation and review do not substitute for human checking of the claimed result or of the correspondence between prose and formal statements. No novelty or priority assessment is asserted. Corrections are welcome.

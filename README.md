# Kirchberg algebras as full amalgams of stably finite algebras

**Draft — unverified. The main theorem is not verified in Lean.**

This repository contains Caleb Barnett’s AI-assisted research draft and a partial Lean 4 formalization. The manuscript proposes that every unital Kirchberg algebra is a full unital amalgamated free product of separable nuclear simple unital stably finite C*-algebras over a common algebra with the same properties. No UCT hypothesis is assumed on the target. The proposed proof has not received independent human mathematical verification.

Read [the manuscript source](paper.tex) and the [formalization scope](verification/SCOPE.md).

## What Lean checks

The checked components include:

- [Matrix diagrams](Suzuki/MatrixDiagrams.lean): both commuting-square identities, the action on kernel representatives, and preservation of the chain equation and kernel map under a chain-homotopy adjustment. These are identities for arbitrary finite integer matrices of compatible sizes, not finite numerical tests.
- [Idempotent systems](Suzuki/IdempotentSystems.lean): compatible sequences are constant fixed-point sequences; the recursive correction stays in the fixed-point subgroup; and `1 - shift` is surjective for every idempotent additive endomorphism of any abelian group, without a countability hypothesis on that group.
- [Simultaneous positive lifting](Suzuki/PositiveLifting.lean): arbitrary homomorphisms on actual integer-matrix kernels and cokernels lift to strictly positive compatible diagrams. For any finite family of maps and target size at least two, one common nonnegative determinant-one change of target presentation works for all channels. The proof checks the exact induced maps.
- [Multiplicity embeddings](Suzuki/MultiplicityEmbeddings.lean) and [their compositions](Suzuki/MultiplicityComposition.lean): actual embeddings between finite products of complex matrix algebras, with explicit dimensions and isometry proofs. Equal multiplicity products give explicit permutation unitaries and literal commuting squares of star homomorphisms.
- [Actual Suzuki finite diagrams](Suzuki/SuzukiFiniteDiagram.lean): the positive-lifting outputs yield both literal squares with one shared common map, certified multiplicities, seven isometries, and positive block dimensions. A finite family uses one common unimodular presentation change; assembling its channels into the total target dimensions remains open.
- [Full C*-amalgam interface](Suzuki/CStarAmalgam.lean): the full universal property for actual unital complex C*-algebras, norm-dense generation by the factors, and uniqueness up to an isometric star-algebra equivalence. These conclusions assume the universal property; this module does not construct an amalgam.
- [Stable finiteness](Suzuki/StableFiniteness.lean), [tracial functionals](Suzuki/TracialFunctional.lean), and [simple traces](Suzuki/SimpleTraces.lean): a normalized positive trace on a simple C*-algebra is faithful and rules out proper isometries in every finite matrix algebra. Existence of the traces required in the manuscript remains unproved.
- [Orthogonal channels](Suzuki/OrthogonalChannels.lean): a finite sum of star-homomorphisms with orthogonal units summing to one is a unital star-homomorphism, injective when one channel is injective.
- [Common full corners](Suzuki/CommonCorner.lean) and [full projections](Suzuki/FullProjectionFrame.lean): ideal-theoretic fullness gives a finite frame via C*-module Cauchy–Schwarz and functional calculus. The concrete corner triple then satisfies the full universal property, including existence and uniqueness of extensions. [Simplicity](Suzuki/SimpleFullness.lean) makes every nonzero projection full. The prescribed K₀-class projection is still not constructed.
- [Concrete inductive limits](Suzuki/SequentialCStarLimit.lean): constructs the norm-completed limit of an injective sequence, with isometric embeddings, density, separability, and the full universal property. Compatible full amalgams pass to these constructed limits, and injective natural families give injective limit maps.
- [Residual representations](Suzuki/ResidualRepresentations.lean): a separable unital RFD algebra has a sequence of actual finite matrix representations with every tail separating. RFD also implies ring-theoretic stable finiteness.
- [Unitization](Suzuki/UnitizationRFD.lean) and [matrix amplification](Suzuki/RFDAmplification.lean): RFD passes to external unitization, full finite matrix algebras, and finite products. The maps are actual finite matrix representations.
- [Matrix limits](Suzuki/MatrixLimits.lean): injective limits of RFD stages are stably finite at every matrix size, proved by simultaneous stage approximation and the Neumann series without assuming a limit trace.
- [Finite completely positive approximation](Suzuki/FiniteCPApproximation.lean): every finite product of complex matrix algebras admits explicit contractive, completely positive block inclusion and compression maps. [Compatible contractions](Suzuki/LimitCPMaps.lean) extend to completely positive contractions on the constructed limits; this extension alone does not establish approximation or nuclearity of those limits.
- [Approximation for split limits](Suzuki/CPApproximationLimits.lean): stage CP approximation passes to the constructed limit when the actual connecting maps have completely positive contractive left inverses. The proof constructs coherent retractions and proves their convergence. [Matrix retractions](Suzuki/MatrixRetractions.lean) supply concrete left inverses for diagonal amplification; splittings for the complete manuscript systems remain to be constructed.
- [Corner inheritance](Suzuki/CornerCPApproximation.lean): nonzero projection corners retain all four finite-constituent properties. [Pure infiniteness](Suzuki/CornerPureInfiniteness.lean) and the exact target Kirchberg predicate also pass to nonzero corners, with actual hereditary closures and restricted witnesses. [Finite corner amalgams](Suzuki/FiniteCornerAmalgam.lean) assemble these results with the full universal property.

The [target module](Suzuki/Target.lean) gives an explicit open proposition `Suzuki.Target.MainClaim` using actual C*-algebras. **A definition of this proposition is not a proof.** Its correspondence with standard nuclearity and pure-infiniteness conventions also needs formal justification.

The verifier inventories every compiled declaration under the `Suzuki` namespace, including definitions and generated declarations, and audits its transitive axiom dependencies. It rejects dependencies other than `propext`, `Classical.choice`, and `Quot.sound`, along with any project axiom declaration. Source hashes and the exact declaration list are recorded in [the manifest](verification/source-manifest.json).

**A passing Lean check here does not verify the manuscript’s complete C*-algebra construction, its KK-theory argument, or its main theorem.** The remaining obligations are listed in [SCOPE.md](verification/SCOPE.md). No main theorem has been replaced by an assumed axiom or packaged as a conditional theorem and labeled verified.

## Reproduce

Install [elan](https://github.com/leanprover/elan), Python 3, and Git. In this repository run:

```sh
lake exe cache get
python3 scripts/verify.py
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The toolchain is Lean 4.33.1. Mathlib is pinned to commit `0df444a360eaa60ab8c11dca51a86af692955474`; transitive dependencies are pinned by `lake-manifest.json`. GitHub Actions runs these component checks in a workflow named **Lean partial formalization checks**.

The separate full-proof command is:

```sh
python3 scripts/verify_full.py
```

**This command currently fails.** It requires a declaration `Suzuki.fullTheorem` of the exact type `Suzuki.Target.MainClaim`, with no extra axioms. That declaration does not exist. Passing the component checks cannot make this command pass, and a future success would still require review of the formal statement’s correspondence to the manuscript.

To build the manuscript locally with an existing LaTeX installation, compile `paper.tex`. This repository does not distribute third-party papers or local dependency caches.

## Status and provenance

Public draft 1, 6 October 2026. The mathematical manuscript and Lean supplement were developed with substantial AI assistance. Automated compilation and review do not substitute for human checking of the claimed result or of the correspondence between prose and formal statements. No novelty or priority assessment is asserted. Corrections are welcome.

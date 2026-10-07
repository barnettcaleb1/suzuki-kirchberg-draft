# Kirchberg algebras as full amalgams of stably finite algebras

**Research draft — conditional Lean verification. Independent human verification is pending.**

Caleb Barnett

The manuscript proposes that every unital Kirchberg algebra is a full unital amalgamated free product of separable nuclear simple unital stably finite C*-algebras over a common algebra with the same properties. There is no UCT hypothesis on the target or coefficient algebra.

[`Suzuki.fullTheoremConditional`](Suzuki/FullTheoremConditional.lean) now proves the exact [`Suzuki.Target.MainClaim`](Suzuki/Target.lean) from explicit [`PublishedInputs`](Suzuki/FullTheoremConditional.lean). This is **conditional Lean verification**, not an unconditional formalization of operator-algebra theory. The interfaces are intended to describe actual Kasparov KK, ordinary K-theory, and the listed published analytic results. Their realization is an external obligation; no actual KK implementation or Lean instances of those published interfaces are claimed. A clean kernel audit does not prove the interfaces.

The exact proof and its explicit hypotheses have passed an independent conditional manuscript/source review. The exact review targets and package checks are recorded in [status](verification/status.json). These reviews do not instantiate the external analytic interfaces.

Read the [manuscript](paper.tex), [precise scope](verification/SCOPE.md), [conditional argument guide](verification/CONDITIONAL.md), [field-by-field source ledger](verification/external-inputs.json), and [complete compiled hypotheses](verification/conditional-hypotheses.txt).

## External dependencies

The theorem takes the published theory as explicit inputs. The remaining obligations include realizing those interfaces in actual operator-algebra theory and checking their exact correspondence with the cited results:

- Standard graph C*-algebra simplicity, pure infiniteness, nuclearity and K-theory; finite-cone comparison and its map naturality.
- Kasparov KK products, split exactness, mapping cones, Bott and Morita equivalence, and ordinary K-theory with its projection and tensor-product normalizations.
- UCT for the scalar bootstrap graph stages, and the analytic Milnor sequence for the actual injective sequential system. **No UCT is assumed for the target or coefficient algebra.**
- Dadarlat's original published extension construction used to derive the nuclear RFD coefficient model, together with standard nuclearity permanence and Choi–Effros lifting.
- Unit-preserving Kirchberg classification, applied with its separability, nuclearity, simplicity, pure infiniteness, invertible KK-class and prescribed-unit hypotheses.
- Standard spatial tensor, Cuntz comparison and inductive-limit facts listed in the interfaces.

The [source ledger](verification/external-inputs.json) records the exact statements, hypotheses, source versions, proof uses, correspondence obligations and source-access limitations. A source-binding or kernel check alone does not discharge these inputs. Independent human mathematical review and novelty assessment remain pending.

## What the conditional proof derives

The final proof supplies the new argument's construction data internally:

- Simultaneous positive integer lifting, actual finite multiplicity embeddings and orthogonal commuting diagrams.
- The full graph/amalgam identification, including the actual common maps and both inverse maps.
- The nuclear RFD coefficient cone derived from the original published extension, its actual quotient/Bott KK equivalence, and a tail-separating matrix representation schedule.
- The actual spatial coefficient channels and their +, − and zero scalar classes under the same finite-cone coordinates; the actual bond class is the reduced split idempotent. UCT is confined to scalar bootstrap sources.
- The actual completed product limit's Kirchberg properties and the three finite constituents' simplicity, nuclearity, separability and stable finiteness. Stable finiteness is proved using faithful finite matrix evaluations and an injective matrix-limit argument.
- A nonzero stabilized common projection, its literal image in the product limit, and its prescribed class under the same κ used for every bond.
- The Milnor equivalence with its exact inverse-stage restrictions, the full corner's actual unit inclusion, and the final unit-preserving classification step.

No field of `PublishedInputs` supplies a desired bond class, a constructed limit's properties, a finite-amalgam presentation of the target, or the prescribed unit equation.

## Reproduce

Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` are pinned. With those dependencies installed:

```sh
lake build
python3 scripts/verify.py
python3 scripts/verify_conditional.py
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The component verifier checks exact source hashes and every declaration originating in a project module, including private/generated declarations in other namespaces. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The conditional verifier additionally requires the exact final theorem type and audits its kernel dependencies. The separate hypothesis and correspondence reports must also pass; these commands do not instantiate the external interfaces.

`python3 scripts/verify_full.py` is intentionally a separate unconditional gate. It requires `Suzuki.fullTheorem : Target.MainClaim` without `PublishedInputs` and remains **NOT VERIFIED**. No such unconditional result is claimed.

The included verification logs and reports record the local conditional-proof checkpoint. GitHub Actions is a separate reproducibility check; its status must be read from the actual workflow run. The 65 previously checked proof modules are preserved byte for byte. Older comments calling the target an open proposition are retained in those immutable source files; the new conditional proof is in its own module.

License: Apache-2.0. Copyright 2026 Caleb Barnett.

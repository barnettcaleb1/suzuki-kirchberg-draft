# Formalization scope

**Overall status: PARTIAL. The main theorem in the manuscript has not been formalized or verified in Lean.**

The source correspondence is to `paper.tex`, Public draft 1 (6 October 2026). Its exact SHA-256 is bound in `source-manifest.json`.

| Manuscript location | Lean declarations | Scope |
| --- | --- | --- |
| Section 3, equation (1) | `MatrixDiagrams.diagram` | Exact integer block matrix, with `A = 1 + B`. |
| Section 3, equation (2), first square | `MatrixDiagrams.first_square` | Arbitrary finite index types and integer matrices; no chain hypothesis needed. |
| Section 3, equation (2), second square | `MatrixDiagrams.second_square` | Assumes the explicit chain equation `S * B = B' * H`. |
| Section 3, action on `(-y,y)` | `MatrixDiagrams.kernel_action` | Assumes `B *ᵥ y = 0`. |
| Section 3, chain-homotopy adjustment | `MatrixDiagrams.adjusted_chain`, `adjusted_kernel` | Algebraic preservation of the chain relation and the kernel action. No positive lifting or cokernel theorem is claimed. |
| Section 6, fixed-idempotent inverse system | `IdempotentSystems.compatible_iff_constant_fixed` | Every compatible sequence is constant and its value is fixed by the given idempotent. |
| Section 6, the product formula used for `lim¹` | `IdempotentSystems.correction`, `correction_fixed`, `one_sub_shift_surjective` | An explicit preimage for `1 - shift` over any abelian group and any idempotent additive endomorphism. No countability assumption on the group. |

Names in the table are under namespace `Suzuki`. Matrix dimensions are arbitrary finite types; matrix entries are integers. The additive-group declarations take an actual additive homomorphism and an explicit idempotence hypothesis. They do not assume KK-theory in a Lean axiom.

## Main proof obligations still outside Lean

1. A formal statement of the main claim using actual unital C*-algebras, the full universal amalgamated free product, the Kirchberg hypotheses, stable finiteness, and nuclearity.
2. The graph-algebra/full-amalgam identification, its norm and universal-property arguments, and the relevant simplicity, pure-infiniteness, and nuclearity theorems.
3. Simultaneous positive lifting of arbitrary prescribed maps on kernels and cokernels, including its group-theoretic existence arguments, and its realization by actual *-homomorphisms.
4. The nuclear residually finite-dimensional coefficient model, the mapping-cone construction, and its KK-equivalence to the target.
5. The three coefficient channels, their tensor and full-product identifications, and the injective commuting diagrams.
6. The KK computations, UCT uses for finite graph stages, the analytic Milnor exact sequence, and the identification of the abstract additive calculations with the relevant Kasparov groups.
7. Simplicity and pure infiniteness of the limit, faithful traces and stable finiteness of the constituents, and preservation of the full amalgam under the limit.
8. Realization of the prescribed unit by a common projection, the common-full-corner theorem, and application of unit-preserving Kirchberg classification without UCT.

No existing Suzuki Lean proof was found in this workspace. A search of the pinned Mathlib source found C*-algebra foundations but did not locate a ready-to-use formalization of the named Kirchberg/KK-theory inputs. This is a statement about the inspected local version, not a claim that no relevant formalization exists anywhere.

The Lean supplement establishes eight algebraic lemmas. It does not certify the complete manuscript. The draft’s unverified status therefore remains unchanged.

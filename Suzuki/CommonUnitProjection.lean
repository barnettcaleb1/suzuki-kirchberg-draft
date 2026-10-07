import Suzuki.MatrixCPApproximation
import Suzuki.ConditionalAssembly
import Suzuki.SimpleFullness

/-!
# The actual initial common projection

Given two same-size coefficient projections, add the same scalar rank-one
projection to both and place them in the two k-blocks of the common algebra.
The resulting projection is nonzero even if both input projections are zero.
Equal positive k-weights and equal positive l-weights satisfy the manuscript's
balanced initial dimensions. The stabilization cancels in any additive class
map having the standard direct-sum law.

This does not construct K₀ from projections or prove the initial graph/tensor
coordinate formula. That correspondence is still required to supply the
`hprojection` hypothesis in ConditionalAssembly.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Suzuki.CommonUnitProjection
open Matrix
open scoped CStarAlgebra ComplexOrder

variable {E : Type*} [CStarAlgebra E]

/-- Adjoin one scalar unit as an actual operator-norm matrix block. -/
def stabilized {n : ℕ} (p : CStarMatrix (Fin n) (Fin n) E) :
    CStarMatrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) E :=
  CStarMatrix.ofMatrix (fromBlocks (CStarMatrix.ofMatrix.symm p) 0 0 1)

theorem stabilized_projection {n : ℕ} {p : CStarMatrix (Fin n) (Fin n) E}
    (hp : IsStarProjection p) : IsStarProjection (stabilized p) := by
  constructor
  · change fromBlocks (CStarMatrix.ofMatrix.symm p) 0 0 1 *
      fromBlocks (CStarMatrix.ofMatrix.symm p) 0 0 1 =
      fromBlocks (CStarMatrix.ofMatrix.symm p) 0 0 1
    rw [fromBlocks_multiply]
    have h : CStarMatrix.ofMatrix.symm p * CStarMatrix.ofMatrix.symm p =
        CStarMatrix.ofMatrix.symm p := hp.1
    simp [h]
  · change (fromBlocks (CStarMatrix.ofMatrix.symm p) 0 0 1).conjTranspose =
      fromBlocks (CStarMatrix.ofMatrix.symm p) 0 0 1
    rw [fromBlocks_conjTranspose]
    have h : (CStarMatrix.ofMatrix.symm p).conjTranspose = CStarMatrix.ofMatrix.symm p :=
      hp.2
    simp [h]

theorem stabilized_nonzero [Nontrivial E] {n : ℕ}
    (p : CStarMatrix (Fin n) (Fin n) E) : stabilized p ≠ 0 := by
  intro h
  have he := congrArg (fun x : CStarMatrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) E =>
    x (Sum.inr 0) (Sum.inr 0)) h
  simp [stabilized] at he

/-- Finite-index change identifies the stabilized block with size n+1. -/
def stabilizedFin {n : ℕ} (p : CStarMatrix (Fin n) (Fin n) E) :
    CStarMatrix (Fin (n+1)) (Fin (n+1)) E :=
  CStarMatrix.reindexₐ ℂ E finSumFinEquiv (stabilized p)

theorem stabilizedFin_projection {n : ℕ} {p : CStarMatrix (Fin n) (Fin n) E}
    (hp : IsStarProjection p) : IsStarProjection (stabilizedFin p) :=
  (stabilized_projection hp).map (CStarMatrix.reindexₐ ℂ E finSumFinEquiv)

theorem stabilizedFin_nonzero [Nontrivial E] {n : ℕ}
    (p : CStarMatrix (Fin n) (Fin n) E) : stabilizedFin p ≠ 0 := by
  intro h
  apply stabilized_nonzero p
  apply (CStarMatrix.reindexₐ ℂ E finSumFinEquiv).injective
  exact h.trans (map_zero _).symm

def commonSize (n : ℕ) : Fin 2 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => n+1) (fun _ => 1)
abbrev Common (E : Type*) [CStarAlgebra E] (n : ℕ) :=
  ∀ i, CStarMatrix (Fin (commonSize n i)) (Fin (commonSize n i)) E

/-- The p and q blocks are both positive projections; the graph signs enter
later through their different K₀ vertex generators, not by negating q here. -/
def commonProjection {n : ℕ} (p q : CStarMatrix (Fin n) (Fin n) E) : Common E n :=
  fun i => match i with
  | .inl i => if i = 0 then stabilizedFin p else stabilizedFin q
  | .inr _ => 0

theorem commonProjection_projection {n : ℕ} {p q : CStarMatrix (Fin n) (Fin n) E}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (commonProjection p q) := by
  constructor
  · funext i
    cases i with
    | inl i =>
      change (if i = 0 then stabilizedFin p else stabilizedFin q) *
        (if i = 0 then stabilizedFin p else stabilizedFin q) =
        (if i = 0 then stabilizedFin p else stabilizedFin q)
      split_ifs <;> first | exact (stabilizedFin_projection hp).1 | exact (stabilizedFin_projection hq).1
    | inr i => exact zero_mul _
  · funext i
    cases i with
    | inl i =>
      change star (if i = 0 then stabilizedFin p else stabilizedFin q) =
        (if i = 0 then stabilizedFin p else stabilizedFin q)
      split_ifs <;> first | exact (stabilizedFin_projection hp).2 | exact (stabilizedFin_projection hq).2
    | inr i => exact star_zero _

theorem commonProjection_nonzero [Nontrivial E] {n : ℕ}
    (p q : CStarMatrix (Fin n) (Fin n) E) : commonProjection p q ≠ 0 := by
  intro h
  have he := congrFun h (Sum.inl 0)
  apply stabilizedFin_nonzero p
  simpa [commonProjection] using he

theorem balanced_dimensions (n : ℕ) :
    (∀ i, 0 < commonSize n i) ∧
      commonSize n (Sum.inl 0) + commonSize n (Sum.inr 0) =
        commonSize n (Sum.inl 1) + commonSize n (Sum.inr 1) := by
  constructor
  · intro i; cases i <;> simp [commonSize]
  · rfl

/-- The constructed projection survives an actual injective stage embedding
and has a finite full-projection frame in a simple common limit algebra. -/
theorem commonProjection_frame [Nontrivial E] {n : ℕ}
    (p q : CStarMatrix (Fin n) (Fin n) E)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (D : Target.UnitalAlgebra) (hD : Target.IsSimple D)
    (stage : Common E n →⋆ₐ[ℂ] D) (hinj : Function.Injective stage) :
    ∃ N, Nonempty (CommonCorner.Frame
      ((commonProjection_projection hp hq).map stage) N) := by
  apply SimpleFullness.exists_frame D hD
  intro hz
  apply commonProjection_nonzero p q
  exact hinj (hz.trans (map_zero stage).symm)

/-- Adding the same scalar projection preserves the represented difference. -/
theorem stabilized_difference {G : Type*} [AddCommGroup G] (n : ℕ)
    (cl : CStarMatrix (Fin n) (Fin n) E → G)
    (cl' : CStarMatrix (Fin (n+1)) (Fin (n+1)) E → G) (scalar : G)
    (hcl : ∀ p, IsStarProjection p → cl' (stabilizedFin p) = cl p + scalar)
    (p q : CStarMatrix (Fin n) (Fin n) E)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    cl' (stabilizedFin p) - cl' (stabilizedFin q) = cl p - cl q := by
  rw [hcl p hp, hcl q hq]
  abel

end Suzuki.CommonUnitProjection

import Suzuki.MatrixLimits

/-!
# Matrix amplification of residual finite dimensionality

Finite matrix representations of the coefficient algebra are amplified and
flattened into ordinary complex matrix representations. The maps are actual
unital star homomorphisms, not prescribed maps on K-theory.
-/

noncomputable section

namespace Suzuki.RFDAmplification

open scoped CStarAlgebra ComplexOrder

variable (k m : Type*) [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

/-- Flatten a matrix of matrices, including its star and complex scalar structure. -/
def flatten : CStarMatrix k k (CStarMatrix m m ℂ) ≃⋆ₐ[ℂ]
    CStarMatrix (k × m) (k × m) ℂ where
  __ := Matrix.compRingEquiv k m ℂ
  map_star' _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq k] [DecidableEq m] in
@[simp] theorem flatten_apply (a : CStarMatrix k k (CStarMatrix m m ℂ))
    (i j : k × m) : flatten k m a i j = a i.1 j.1 i.2 j.2 := rfl

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A matrix representation of the coefficient algebra gives one of its matrix
amplification, with the exact product dimension. -/
def representation (n : ℕ) (hn : 0 < n) (ρ : ResidualRepresentations.Representation A) :
    ResidualRepresentations.Representation (CStarMatrix (Fin n) (Fin n) A) where
  dimension := n * ρ.dimension
  positive_dimension := Nat.mul_pos hn ρ.positive_dimension
  hom := (CStarMatrix.reindexₐ ℂ ℂ finProdFinEquiv).toStarAlgHom.comp
    ((flatten (Fin n) (Fin ρ.dimension)).toStarAlgHom.comp
      (MatrixLimits.matrixHom (Fin n) ρ.hom))

/-- RFD passes to every finite matrix algebra with its C⋆-norm. -/
theorem matrix_rfd (n : ℕ) (h : ResidualRepresentations.IsRFD A) :
    ResidualRepresentations.IsRFD (CStarMatrix (Fin n) (Fin n) A) := by
  classical
  intro a ha
  have hex : ∃ i j, a i j ≠ 0 := by
    by_contra! hz
    exact ha (CStarMatrix.ext hz)
  obtain ⟨i, j, hij⟩ := hex
  obtain ⟨ρ, hρ⟩ := h (a i j) hij
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  refine ⟨representation n hn ρ, ?_⟩
  intro hz
  let e := (flatten (Fin n) (Fin ρ.dimension)).trans
    (CStarMatrix.reindexₐ ℂ ℂ finProdFinEquiv)
  have hz' : e (MatrixLimits.matrixHom (Fin n) ρ.hom a) = 0 := hz
  have hmat : MatrixLimits.matrixHom (Fin n) ρ.hom a = 0 :=
    EquivLike.injective e (hz'.trans (map_zero e).symm)
  exact hρ (congrFun (congrFun hmat i) j)

section Products

variable {ι : Type*} [Fintype ι] (D : ι → Type*) [∀ i, CStarAlgebra (D i)]

/-- The finite direct product of RFD unital C⋆-algebras is RFD. -/
theorem finite_product_rfd (h : ∀ i, ResidualRepresentations.IsRFD (D i)) :
    ResidualRepresentations.IsRFD (∀ i, D i) := by
  classical
  intro a ha
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! hz
    exact ha (funext hz)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨ρ, hρ⟩ := h i (a i) hi
  exact ⟨⟨ρ.dimension, ρ.positive_dimension, ρ.hom.comp (Pi.evalStarAlgHom ℂ D i)⟩, hρ⟩

end Products

end Suzuki.RFDAmplification

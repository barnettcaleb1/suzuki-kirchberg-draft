import Suzuki.ResidualRepresentations

/-!
# Residual finite dimensionality of the external unitization

The starting algebra can be nonunital. Its finite-dimensional representations
extend by the actual universal property of the external unitization, and the
scalar quotient detects the extra scalar coordinate.
-/

noncomputable section

namespace Suzuki.UnitizationRFD

open scoped CStarAlgebra ComplexOrder

variable (F : Type*) [NonUnitalCStarAlgebra F]

structure Representation where
  dimension : ℕ
  positive_dimension : 0 < dimension
  hom : F →⋆ₙₐ[ℂ] CStarMatrix (Fin dimension) (Fin dimension) ℂ

def IsRFD : Prop := ∀ a : F, a ≠ 0 → ∃ ρ : Representation F, ρ.hom a ≠ 0

/-- The scalar quotient of the actual external unitization. -/
def augmentation : Unitization ℂ F →⋆ₐ[ℂ] ℂ where
  __ := Unitization.fstHom ℂ F
  map_star' _ := rfl

/-- The one-dimensional scalar representation, expressed in the same matrix
representation type as all other finite-dimensional representations. -/
def scalarRepresentation : ResidualRepresentations.Representation (Unitization ℂ F) where
  dimension := 1
  positive_dimension := by decide
  hom := (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ).toStarAlgHom.comp (augmentation F)

/-- An actual nonunital matrix representation extends to a unital representation. -/
def extend (ρ : Representation F) :
    ResidualRepresentations.Representation (Unitization ℂ F) where
  dimension := ρ.dimension
  positive_dimension := ρ.positive_dimension
  hom := Unitization.starLift ρ.hom

/-- RFD passes from a possibly nonunital algebra to its external unitization. -/
theorem unitization_rfd (h : IsRFD F) : ResidualRepresentations.IsRFD (Unitization ℂ F) := by
  intro a ha
  by_cases hscalar : a.fst = 0
  · have hsnd : a.snd ≠ 0 := by
      intro hz
      apply ha
      apply Unitization.toProd_injective
      exact Prod.ext hscalar hz
    obtain ⟨ρ, hρ⟩ := h a.snd hsnd
    refine ⟨extend F ρ, ?_⟩
    change algebraMap ℂ _ a.fst + ρ.hom a.snd ≠ 0
    simpa only [hscalar, map_zero, zero_add] using hρ
  · refine ⟨scalarRepresentation F, ?_⟩
    intro hz
    exact hscalar (congrFun (congrFun hz (0 : Fin 1)) (0 : Fin 1))

/-- Separability of the external unitization uses its genuine C⋆-topology. -/
instance separable [TopologicalSpace.SeparableSpace F] :
    TopologicalSpace.SeparableSpace (Unitization ℂ F) := by
  exact (Unitization.uniformEquivProd (𝕜 := ℂ) (A := F)).symm.surjective.denseRange.separableSpace
    (Unitization.uniformEquivProd (𝕜 := ℂ) (A := F)).symm.continuous

/-- The coefficient unitization therefore admits finite matrix representations
whose every tail separates points. -/
theorem exists_separating_tails [TopologicalSpace.SeparableSpace F] (h : IsRFD F) :
    ∃ ρ : ℕ → ResidualRepresentations.Representation (Unitization ℂ F),
      ResidualRepresentations.SeparatingTails (Unitization ℂ F) ρ :=
  ResidualRepresentations.exists_separating_tails (unitization_rfd F h)

end Suzuki.UnitizationRFD

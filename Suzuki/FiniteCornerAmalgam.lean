import Suzuki.CornerCPApproximation

/-!
# The finite-constituent common-corner step

This combines the concrete full-corner universal property with all proved
finite-constituent inheritance properties. It does not construct the common
projection with its prescribed K-class or identify the corner with a target
Kirchberg algebra.
-/

noncomputable section

namespace Suzuki.FiniteCornerAmalgam

open CommonCorner

universe u

variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]

/-- Restricting an injective star homomorphism to projection corners remains
injective, even though ambient corner inclusions are nonunital. -/
theorem cornerMap_injective {p : A} {q : B}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (f : A →⋆ₐ[ℂ] B) (he : f p = q) (hf : Function.Injective f) :
    Function.Injective (CommonCorner.map hp hq f he) := by
  intro a b h
  exact Subtype.ext (hf (congrArg Subtype.val h))

/-- A nonzero projection in the common finite constituent supplies an actual
finite-amalgam presentation of the corresponding product corner. -/
theorem hasFiniteAmalgam (D A₀ A₁ P : Target.UnitalAlgebra.{u})
    (hD : Target.IsFiniteConstituent D) (h₀ : Target.IsFiniteConstituent A₀)
    (h₁ : Target.IsFiniteConstituent A₁)
    (i₀ : D →⋆ₐ[ℂ] A₀) (i₁ : D →⋆ₐ[ℂ] A₁)
    (j₀ : A₀ →⋆ₐ[ℂ] P) (j₁ : A₁ →⋆ₐ[ℂ] P)
    (hi₀ : Function.Injective i₀) (hi₁ : Function.Injective i₁)
    (hfull : CStarAmalgam.IsFullAmalgam i₀ i₁ j₀ j₁)
    {p : D} (hp : IsStarProjection p) (hne : p ≠ 0) :
    Target.HasFiniteAmalgam ⟨Corner ((hp.map i₀).map j₀), inferInstance⟩ := by
  have hp₀ : IsStarProjection (i₀ p) := hp.map i₀
  have hp₁ : IsStarProjection (i₁ p) := hp.map i₁
  have hpP : IsStarProjection (j₀ (i₀ p)) := hp₀.map j₀
  have he : j₁ (i₁ p) = j₀ (i₀ p) := (DFunLike.congr_fun hfull.commutes p).symm
  have hne₀ : i₀ p ≠ 0 := by
    intro h
    exact hne (hi₀ (h.trans (map_zero i₀).symm))
  have hne₁ : i₁ p ≠ 0 := by
    intro h
    exact hne (hi₁ (h.trans (map_zero i₁).symm))
  refine ⟨⟨Corner hp, inferInstance⟩, ⟨Corner hp₀, inferInstance⟩,
    ⟨Corner hp₁, inferInstance⟩,
    CornerCPApproximation.isFiniteConstituent D hD hp hne,
    CornerCPApproximation.isFiniteConstituent A₀ h₀ hp₀ hne₀,
    CornerCPApproximation.isFiniteConstituent A₁ h₁ hp₁ hne₁,
    CommonCorner.map hp hp₀ i₀ rfl, CommonCorner.map hp hp₁ i₁ rfl,
    CommonCorner.map hp₀ hpP j₀ rfl, CommonCorner.map hp₁ hpP j₁ he,
    cornerMap_injective hp hp₀ i₀ rfl hi₀,
    cornerMap_injective hp hp₁ i₁ rfl hi₁, ?_⟩
  exact CommonCorner.isFullAmalgam_of_fullProjection hfull hp hp₀ hp₁ hpP
    rfl rfl rfl he (SimpleFullness.full_of_nonzero hD.2.2.1.2 hne)

end Suzuki.FiniteCornerAmalgam

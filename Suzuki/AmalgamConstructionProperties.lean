import Suzuki.UniversalAmalgam
import Suzuki.GraphDensity

/-! Genuine permanence properties of the constructed full Cstar amalgam.
Separability is unconditional for separable factors; injectivity is tied to
an explicit compatible representation, not presumed from universality. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Suzuki.AmalgamConstructionProperties
open scoped CStarAlgebra

universe u
variable {D A₀ A₁ P : Type u}
variable [CStarAlgebra D] [CStarAlgebra A₀] [CStarAlgebra A₁] [CStarAlgebra P]
variable {i₀ : D →⋆ₐ[ℂ] A₀} {i₁ : D →⋆ₐ[ℂ] A₁}
variable {j₀ : A₀ →⋆ₐ[ℂ] P} {j₁ : A₁ →⋆ₐ[ℂ] P}

/-- The actual universal property and separability of both factors suffice. -/
theorem separable (h : CStarAmalgam.IsFullAmalgam i₀ i₁ j₀ j₁)
    [TopologicalSpace.SeparableSpace A₀] [TopologicalSpace.SeparableSpace A₁] :
    TopologicalSpace.SeparableSpace P := by
  obtain ⟨s₀, hc₀, hd₀⟩ := TopologicalSpace.exists_countable_dense A₀
  obtain ⟨s₁, hc₁, hd₁⟩ := TopologicalSpace.exists_countable_dense A₁
  let s : Set P := j₀ '' s₀ ∪ j₁ '' s₁
  let S := (StarAlgebra.adjoin ℂ s).topologicalClosure
  have hclosed : IsClosed (S : Set P) := StarSubalgebra.isClosed_topologicalClosure _
  have hm : s ⊆ (S : Set P) :=
    (StarAlgebra.subset_adjoin ℂ s).trans (StarSubalgebra.le_topologicalClosure _)
  have hcj₀ : Continuous (j₀ : A₀ → P) := map_continuous j₀
  have hcj₁ : Continuous (j₁ : A₁ → P) := map_continuous j₁
  have h₀ : ∀ a, j₀ a ∈ S := by
    intro a
    exact closure_minimal (s := s₀) (t := j₀ ⁻¹' (S : Set P))
      (fun x hx => hm (Set.mem_union_left _ ⟨x, hx, rfl⟩))
      (hclosed.preimage hcj₀) (hd₀ a)
  have h₁ : ∀ a, j₁ a ∈ S := by
    intro a
    exact closure_minimal (s := s₁) (t := j₁ ⁻¹' (S : Set P))
      (fun x hx => hm (Set.mem_union_right _ ⟨x, hx, rfl⟩))
      (hclosed.preimage hcj₁) (hd₁ a)
  have heq : S = ⊤ := h.eq_top_of_isClosed S hclosed h₀ h₁
  have hs : s.Countable := (hc₀.image j₀).union (hc₁.image j₁)
  have hsep := GraphDensity.closed_adjoin_separable hs
  change TopologicalSpace.IsSeparable (S : Set P) at hsep
  rw [heq] at hsep
  exact TopologicalSpace.isSeparable_univ_iff.mp hsep

variable (i₀ i₁)

instance constructedSeparable [TopologicalSpace.SeparableSpace A₀]
    [TopologicalSpace.SeparableSpace A₁] :
    TopologicalSpace.SeparableSpace (UniversalAmalgam.Algebra i₀ i₁) :=
  separable (UniversalAmalgam.isFullAmalgam i₀ i₁)

variable {B : Type u} [CStarAlgebra B]

/-- Any compatible pair with faithful left map certifies the constructed left
map. Existence of such a pair is an explicit hypothesis of this result. -/
theorem left_injective (f₀ : A₀ →⋆ₐ[ℂ] B) (f₁ : A₁ →⋆ₐ[ℂ] B)
    (hf : f₀.comp i₀ = f₁.comp i₁) (hinj : Function.Injective f₀) :
    Function.Injective (UniversalAmalgam.left i₀ i₁) := by
  intro a b hab
  apply hinj
  simpa only [UniversalAmalgam.lift_left] using
    congrArg (UniversalAmalgam.lift i₀ i₁ f₀ f₁ hf) hab

theorem right_injective (f₀ : A₀ →⋆ₐ[ℂ] B) (f₁ : A₁ →⋆ₐ[ℂ] B)
    (hf : f₀.comp i₀ = f₁.comp i₁) (hinj : Function.Injective f₁) :
    Function.Injective (UniversalAmalgam.right i₀ i₁) := by
  intro a b hab
  apply hinj
  simpa only [UniversalAmalgam.lift_right] using
    congrArg (UniversalAmalgam.lift i₀ i₁ f₀ f₁ hf) hab

theorem left_isometry (f₀ : A₀ →⋆ₐ[ℂ] B) (f₁ : A₁ →⋆ₐ[ℂ] B)
    (hf : f₀.comp i₀ = f₁.comp i₁) (hinj : Function.Injective f₀) :
    Isometry (UniversalAmalgam.left i₀ i₁) :=
  NonUnitalStarAlgHom.isometry _ (left_injective i₀ i₁ f₀ f₁ hf hinj)

theorem right_isometry (f₀ : A₀ →⋆ₐ[ℂ] B) (f₁ : A₁ →⋆ₐ[ℂ] B)
    (hf : f₀.comp i₀ = f₁.comp i₁) (hinj : Function.Injective f₁) :
    Isometry (UniversalAmalgam.right i₀ i₁) :=
  NonUnitalStarAlgHom.isometry _ (right_injective i₀ i₁ f₀ f₁ hf hinj)

/-- A compatible representation into any genuine nontrivial Cstar algebra
certifies nontriviality of the constructed algebra. -/
theorem nontrivial [Nontrivial B] (f₀ : A₀ →⋆ₐ[ℂ] B) (f₁ : A₁ →⋆ₐ[ℂ] B)
    (hf : f₀.comp i₀ = f₁.comp i₁) : Nontrivial (UniversalAmalgam.Algebra i₀ i₁) := by
  apply nontrivial_of_ne (1 : UniversalAmalgam.Algebra i₀ i₁) 0
  intro h
  have he := congrArg (UniversalAmalgam.lift i₀ i₁ f₀ f₁ hf) h
  exact one_ne_zero (by simpa only [map_one, map_zero] using he)

end Suzuki.AmalgamConstructionProperties

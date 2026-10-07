import Suzuki.Target
import Mathlib.CategoryTheory.Iso

/-!
# Exact classification input and actual final transport

The abstract KK objects and unit classes below are explicit parameters.
Their intended correspondence with actual Kasparov theory is external.
The classification input is precisely the unit-preserving, KK-equivalence
form of Phillips, arXiv:funct-an/9506010v2, Corollary 4.2.2 (p.42).
It has no UCT premise on either algebra. Its target predicates use the exact
MainClaim conventions; their correspondence with published conventions must
be checked externally.

`conclude` is only the final assembly step. Its finite-amalgam witness and
unit-preserving equivalence must be constructed by the manuscript's new
argument; they are not included in `ClassificationInput` or asserted here.
-/

namespace Suzuki.ConditionalClassification
open CategoryTheory
universe u v w

/-- The full universal property transfers along an actual unital star equivalence. -/
theorem hasFiniteAmalgam_of_equiv {A B : Target.UnitalAlgebra.{u}}
    (hA : Target.HasFiniteAmalgam A) (e : A ≃⋆ₐ[ℂ] B) : Target.HasFiniteAmalgam B := by
  obtain ⟨D, A₀, A₁, hD, h₀, h₁, i₀, i₁, j₀, j₁, hi₀, hi₁, h⟩ := hA
  refine ⟨D, A₀, A₁, hD, h₀, h₁, i₀, i₁,
    e.toStarAlgHom.comp j₀, e.toStarAlgHom.comp j₁, hi₀, hi₁, ?_⟩
  constructor
  · simp only [StarAlgHom.comp_assoc, h.commutes]
  · intro C inst f₀ f₁ hf
    let μ := h.lift f₀ f₁ hf
    let φ := μ.comp e.symm.toStarAlgHom
    have hleft : φ.comp (e.toStarAlgHom.comp j₀) = f₀ := by
      apply StarAlgHom.ext
      intro a
      change μ (e.symm (e (j₀ a))) = f₀ a
      rw [e.symm_apply_apply]
      exact DFunLike.congr_fun (h.lift_left f₀ f₁ hf) a
    have hright : φ.comp (e.toStarAlgHom.comp j₁) = f₁ := by
      apply StarAlgHom.ext
      intro a
      change μ (e.symm (e (j₁ a))) = f₁ a
      rw [e.symm_apply_apply]
      exact DFunLike.congr_fun (h.lift_right f₀ f₁ hf) a
    refine ⟨φ, ⟨hleft, hright⟩, ?_⟩
    intro ψ hψ
    have heq : ψ.comp e.toStarAlgHom = μ := by
      apply h.lift_unique f₀ f₁ hf
      · simpa only [StarAlgHom.comp_assoc] using hψ.1
      · simpa only [StarAlgHom.comp_assoc] using hψ.2
    apply StarAlgHom.ext
    intro b
    have hb := DFunLike.congr_fun heq (e.symm b)
    change ψ (e (e.symm b)) = μ (e.symm b) at hb
    change ψ b = μ (e.symm b)
    simpa only [e.apply_symm_apply] using hb

variable {K : Type v} [Category.{w} K]
variable (object : Target.UnitalAlgebra.{u} → K) (scalar : K)
variable (unit : ∀ A : Target.UnitalAlgebra.{u}, scalar ⟶ object A)

/-- EXTERNAL INPUT: KK equivalence preserving the distinguished unit implies
an actual unital complex star equivalence for Kirchberg algebras. -/
def ClassificationInput : Prop :=
  ∀ (A B : Target.UnitalAlgebra.{u}), Target.IsKirchberg A → Target.IsKirchberg B →
    ∀ ξ : object A ≅ object B, unit A ≫ ξ.hom = unit B → Nonempty (A ≃⋆ₐ[ℂ] B)

/-- Final assembly only: the new argument still owes A, its actual finite
amalgam, ξ and the unit equation. These are visible local hypotheses. -/
theorem conclude (classify : ClassificationInput object scalar unit)
    (A B : Target.UnitalAlgebra.{u}) (hA : Target.IsKirchberg A) (hB : Target.IsKirchberg B)
    (presentation : Target.HasFiniteAmalgam A)
    (ξ : object A ≅ object B) (hunit : unit A ≫ ξ.hom = unit B) :
    Target.HasFiniteAmalgam B := by
  obtain ⟨e⟩ := classify A B hA hB ξ hunit
  exact hasFiniteAmalgam_of_equiv presentation e

end Suzuki.ConditionalClassification

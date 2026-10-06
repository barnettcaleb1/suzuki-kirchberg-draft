import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Completion of an actual normed complex star algebra

The input need not be complete. Its C⋆-identity, algebra operations and star
extend to the metric completion. This is analytic infrastructure for constructing
the inductive limits, not an assumed colimit or a proof of the main theorem.
-/

noncomputable section

namespace Suzuki.CStarCompletion

open UniformSpace
open scoped CStarAlgebra

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

instance completionStar : Star (Completion A) := ⟨Completion.map (star : A → A)⟩

@[simp] theorem star_coe (a : A) : star (a : Completion A) = (star a : A) :=
  Completion.map_coe (star_isometry : Isometry (star : A → A)).uniformContinuous a

instance completionContinuousStar : ContinuousStar (Completion A) where
  continuous_star := Completion.continuous_map

instance completionStarRing : StarRing (Completion A) where
  star_involutive a := by
    induction a using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih a => simp
  star_mul a b := by
    induction a, b using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih a b => simp only [← Completion.coe_mul, star_coe, star_mul]
  star_add a b := by
    induction a, b using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih a b => simp only [← Completion.coe_add, star_coe, star_add]

variable [NormedAlgebra ℂ A] [StarModule ℂ A]

instance completionStarModule : StarModule ℂ (Completion A) where
  star_smul z a := by
    induction a using Completion.induction_on with
    | hp =>
      apply isClosed_eq
      · exact (continuous_star : Continuous (star : Completion A → Completion A)).comp
          (continuous_const_smul z)
      · exact (continuous_const_smul (star z)).comp
          (continuous_star : Continuous (star : Completion A → Completion A))
    | ih a => simp only [← Completion.coe_smul, star_coe, star_smul]

instance completionNormedAlgebra : NormedAlgebra ℂ (Completion A) where
  norm_smul_le := norm_smul_le

instance completionCStarRing : CStarRing (Completion A) where
  norm_mul_self_le a := by
    induction a using Completion.induction_on with
    | hp => apply isClosed_le <;> fun_prop
    | ih a => simpa only [star_coe, ← Completion.coe_mul, Completion.norm_coe]
        using CStarRing.norm_mul_self_le a

/-- The metric completion has the genuine complete complex C⋆-algebra structure. -/
instance completionCStarAlgebra : CStarAlgebra (Completion A) where

/-- The original algebra embeds by a unital complex star homomorphism. -/
def inclusion : A →⋆ₐ[ℂ] Completion A where
  __ := Completion.coeRingHom
  commutes' := fun _ => rfl
  map_star' := fun a => (star_coe a).symm

omit [StarModule ℂ A] in
theorem inclusion_isometry : Isometry (inclusion : A → Completion A) :=
  Completion.coe_isometry

omit [StarModule ℂ A] in
theorem inclusion_denseRange : DenseRange (inclusion : A → Completion A) :=
  Completion.denseRange_coe

variable {B : Type*} [CStarAlgebra B]

omit [CStarRing A] [StarModule ℂ A] in
/-- Contractivity is explicitly supplied for maps from the possibly incomplete
input algebra; it is not assumed to follow from an incomplete-domain star map. -/
theorem uniformContinuous_of_contractive (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ a, ‖f a‖ ≤ ‖a‖) : UniformContinuous f := by
  let g : A →L[ℂ] B := (f : A →ₗ[ℂ] B).mkContinuous 1 (fun a => by simpa using hf a)
  exact g.uniformContinuous

omit [CStarRing A] [StarModule ℂ A] in
theorem extension_coe (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (a : A) :
    Completion.extension f (a : Completion A) = f a :=
  Completion.extension_coe (uniformContinuous_of_contractive f hf) a

/-- A contractive unital complex star homomorphism extends to the actual
completion as a unital complex star homomorphism. -/
def lift (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) : Completion A →⋆ₐ[ℂ] B where
  toFun := Completion.extension f
  map_one' := by rw [← Completion.coe_one, extension_coe f hf, map_one]
  map_zero' := by rw [← Completion.coe_zero, extension_coe f hf, map_zero]
  map_add' a b := by
    induction a, b using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih a b => simp only [← Completion.coe_add, extension_coe f hf, map_add]
  map_mul' a b := by
    induction a, b using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih a b => simp only [← Completion.coe_mul, extension_coe f hf, map_mul]
  commutes' z := by
    rw [Completion.algebraMap_def, extension_coe f hf]
    exact f.commutes z
  map_star' a := by
    induction a using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih a => simp only [star_coe, extension_coe f hf, map_star]

omit [StarModule ℂ A] in
@[simp] theorem lift_coe (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (a : A) :
    lift f hf (a : Completion A) = f a := extension_coe f hf a

/-- Agreement on the original dense algebra determines a completion map. -/
theorem hom_ext {f g : Completion A →⋆ₐ[ℂ] B}
    (h : ∀ a : A, f (a : Completion A) = g (a : Completion A)) : f = g := by
  apply StarAlgHom.ext
  exact Completion.ext' (map_continuous f) (map_continuous g) h

theorem lift_unique (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    (g : Completion A →⋆ₐ[ℂ] B) (hg : ∀ a : A, g (a : Completion A) = f a) :
    g = lift f hf := by
  apply hom_ext
  intro a
  rw [hg, lift_coe]

end Suzuki.CStarCompletion

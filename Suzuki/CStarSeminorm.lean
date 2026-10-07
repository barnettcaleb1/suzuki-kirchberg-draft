import Suzuki.CStarCompletion
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Group.SeparationQuotient

/-!
# Completing a complex C⋆-seminorm

The zero-seminorm ideal is removed by the actual metric separation quotient.
Its star structure and C⋆-identity are proved, and contractive representations
extend uniquely to the completion. No universal algebra or graph theorem is
assumed in this analytic construction.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Suzuki.CStarSeminorm

open UniformSpace

variable {A : Type*} [SeminormedRing A] [StarRing A] [NormedStarGroup A]

instance quotientStar : Star (SeparationQuotient A) where
  star := SeparationQuotient.lift (fun a : A => SeparationQuotient.mk (star a))
    (fun _ _ h => SeparationQuotient.mk_eq_mk.mpr (h.map continuous_star))

@[simp] theorem star_mk (a : A) :
    star (SeparationQuotient.mk a) = SeparationQuotient.mk (star a) := rfl

instance quotientStarRing : StarRing (SeparationQuotient A) where
  star_involutive q := by
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk q
    simp only [star_mk, star_star]
  star_mul q r := by
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk q
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk r
    simp only [← SeparationQuotient.mk_mul, star_mk, star_mul]
  star_add q r := by
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk q
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk r
    simp only [← SeparationQuotient.mk_add, star_mk, star_add]

instance quotientNormedStarGroup : NormedStarGroup (SeparationQuotient A) where
  norm_star_le q := by
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk q
    simp only [star_mk, SeparationQuotient.norm_mk, norm_star, le_refl]

variable [NormedAlgebra ℂ A] [StarModule ℂ A]

instance quotientStarModule : StarModule ℂ (SeparationQuotient A) where
  star_smul z q := by
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk q
    simp only [← SeparationQuotient.mk_smul, star_mk, star_smul]

/-- The norm-separating quotient map, preserving all complex star operations. -/
def quotientMap : A →⋆ₐ[ℂ] SeparationQuotient A where
  __ := SeparationQuotient.mkRingHom
  commutes' z := SeparationQuotient.mk_algebraMap z
  map_star' a := (star_mk a).symm

omit [StarModule ℂ A] in
@[simp] theorem norm_quotientMap (a : A) : ‖quotientMap a‖ = ‖a‖ := rfl

variable [Fact (∀ a : A, ‖a‖ * ‖a‖ ≤ ‖star a * a‖)]

instance quotientCStarRing : CStarRing (SeparationQuotient A) where
  norm_mul_self_le q := by
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk q
    simpa only [star_mk, ← SeparationQuotient.mk_mul, SeparationQuotient.norm_mk]
      using (Fact.out : ∀ a : A, ‖a‖ * ‖a‖ ≤ ‖star a * a‖) a

/-- The actual completion after dividing out zero seminorm. -/
abbrev Envelope (A : Type*) [SeminormedRing A] := Completion (SeparationQuotient A)

instance envelopeCStarAlgebra : CStarAlgebra (Envelope A) := inferInstance

def inclusion : A →⋆ₐ[ℂ] Envelope A := CStarCompletion.inclusion.comp quotientMap

omit [StarModule ℂ A] in
@[simp] theorem norm_inclusion (a : A) : ‖inclusion a‖ = ‖a‖ :=
  Completion.norm_coe _

omit [StarModule ℂ A] in
theorem inclusion_denseRange : DenseRange (inclusion : A → Envelope A) := by
  exact (Completion.denseRange_coe (α := SeparationQuotient A)).comp
    ((SeparationQuotient.surjective_mk (X := A)).denseRange) (Completion.continuous_coe _)

variable {B : Type*} [CStarAlgebra B]

omit [NormedStarGroup A] [StarModule ℂ A]
  [Fact (∀ a : A, ‖a‖ * ‖a‖ ≤ ‖star a * a‖)] in
theorem continuous_of_contractive (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ a, ‖f a‖ ≤ ‖a‖) : Continuous f := by
  let g : A →L[ℂ] B := (f : A →ₗ[ℂ] B).mkContinuous 1 (fun a => by simpa using hf a)
  exact g.continuous

omit [Fact (∀ a : A, ‖a‖ * ‖a‖ ≤ ‖star a * a‖)] in
/-- A contractive representation kills zero seminorm and descends to the
separated quotient; this is a proved descent, not a kernel hypothesis. -/
def descend (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) :
    SeparationQuotient A →⋆ₐ[ℂ] B where
  toFun := SeparationQuotient.lift f
    (fun _ _ h => (h.map (continuous_of_contractive f hf)).eq)
  map_zero' := map_zero f
  map_one' := map_one f
  map_add' := Quotient.ind₂ (map_add f)
  map_mul' := Quotient.ind₂ (map_mul f)
  commutes' := f.commutes
  map_star' := Quotient.ind (map_star f)

omit [StarModule ℂ A] [Fact (∀ a : A, ‖a‖ * ‖a‖ ≤ ‖star a * a‖)] in
@[simp] theorem descend_mk (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (a : A) :
    descend f hf (SeparationQuotient.mk a) = f a := rfl

omit [StarModule ℂ A] [Fact (∀ a : A, ‖a‖ * ‖a‖ ≤ ‖star a * a‖)] in
theorem descend_contractive (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    (a : SeparationQuotient A) : ‖descend f hf a‖ ≤ ‖a‖ := by
  obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk a
  exact hf a

/-- Every contractive star representation extends to the actual C⋆-completion. -/
def lift (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) : Envelope A →⋆ₐ[ℂ] B :=
  CStarCompletion.lift (descend f hf) (descend_contractive f hf)

omit [StarModule ℂ A] in
@[simp] theorem lift_inclusion (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (a : A) :
    lift f hf (inclusion a) = f a := CStarCompletion.lift_coe _ _ _

theorem hom_ext {f g : Envelope A →⋆ₐ[ℂ] B}
    (h : ∀ a : A, f (inclusion a) = g (inclusion a)) : f = g := by
  apply CStarCompletion.hom_ext
  intro q
  obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk q
  exact h a

theorem lift_unique (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    (g : Envelope A →⋆ₐ[ℂ] B) (hg : ∀ a, g (inclusion a) = f a) : g = lift f hf := by
  apply hom_ext
  intro a
  rw [hg, lift_inclusion]

end Suzuki.CStarSeminorm

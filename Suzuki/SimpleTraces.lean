import Suzuki.Target
import Suzuki.TracialFunctional
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Tracial states on simple C⋆-algebras

The null space of a positive trace is a closed two-sided ideal. Simplicity
therefore makes a normalized trace faithful, and the matrix trace argument
gives stable finiteness. Existence of a trace is an explicit hypothesis.
-/

namespace Suzuki.SimpleTraces

open scoped CStarAlgebra ComplexOrder

section General

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ : A →ₚ[ℂ] ℂ)

theorem null_iff_norm (a : A) :
    φ (star a * a) = 0 ↔ ‖φ.toPreGNS a‖ = 0 := by
  constructor
  · intro ha
    simp [PositiveLinearMap.preGNS_norm_def, ha]
  · intro ha
    have h := φ.preGNS_norm_sq (φ.toPreGNS a)
    simpa [ha] using h.symm

theorem null_add (a b : A) (ha : φ (star a * a) = 0)
    (hb : φ (star b * b) = 0) : φ (star (a + b) * (a + b)) = 0 := by
  apply (null_iff_norm φ _).mpr
  apply le_antisymm _ (norm_nonneg _)
  rw [map_add]
  calc
    ‖φ.toPreGNS a + φ.toPreGNS b‖ ≤ ‖φ.toPreGNS a‖ + ‖φ.toPreGNS b‖ := norm_add_le _ _
    _ = 0 := by rw [(null_iff_norm φ a).mp ha, (null_iff_norm φ b).mp hb, add_zero]

theorem null_left (a b : A) (hb : φ (star b * b) = 0) :
    φ (star (a * b) * (a * b)) = 0 := by
  apply (null_iff_norm φ _).mpr
  apply le_antisymm _ (norm_nonneg _)
  have h := (φ.leftMulMapPreGNS a).le_opNorm (φ.toPreGNS b)
  simpa [PositiveLinearMap.leftMulMapPreGNS_apply, (null_iff_norm φ b).mp hb] using h

variable (hcyc : ∀ a b, φ (a * b) = φ (b * a))

include hcyc

omit [StarOrderedRing A] in
theorem null_star (a : A) (ha : φ (star a * a) = 0) :
    φ (star (star a) * star a) = 0 := by
  rw [star_star, hcyc]
  exact ha

theorem null_right (a b : A) (ha : φ (star a * a) = 0) :
    φ (star (a * b) * (a * b)) = 0 := by
  have h := null_star φ hcyc (star b * star a)
    (null_left φ (star b) (star a) (null_star φ hcyc a ha))
  simpa only [star_mul, star_star] using h

/-- The trace null space as an actual two-sided ideal. -/
def nullIdeal : TwoSidedIdeal A := TwoSidedIdeal.mk'
  {a | φ (star a * a) = 0}
  (by simp)
  (fun {a b} ha hb => null_add φ a b ha hb)
  (fun {a} ha => by simpa using ha)
  (fun {a b} hb => null_left φ a b hb)
  (fun {a b} ha => null_right φ hcyc a b ha)

theorem mem_nullIdeal (a : A) : a ∈ nullIdeal φ hcyc ↔ φ (star a * a) = 0 := by
  simp [nullIdeal]

theorem nullIdeal_isClosed : IsClosed (nullIdeal φ hcyc : Set A) := by
  simp only [nullIdeal, TwoSidedIdeal.coe_mk']
  apply isClosed_eq _ continuous_const
  fun_prop

/-- Simplicity forces a normalized positive trace to be faithful. -/
theorem faithful_of_simple
    (hsimple : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤)
    (hunit : φ 1 = 1) : ∀ a, φ (star a * a) = 0 → a = 0 := by
  rcases hsimple (nullIdeal φ hcyc) (nullIdeal_isClosed φ hcyc) with hbot | htop
  · intro a ha
    have hm : a ∈ nullIdeal φ hcyc := (mem_nullIdeal φ hcyc a).mpr ha
    simpa [hbot] using hm
  · have hm : (1 : A) ∈ nullIdeal φ hcyc := by simp [htop]
    have hz := (mem_nullIdeal φ hcyc 1).mp hm
    simp [hunit] at hz

end General

/-- The exact stable-finiteness conclusion for a simple bundled target algebra. -/
theorem stablyFinite (A : Target.UnitalAlgebra) (hsimple : Target.IsSimple A)
    (φ : A →ₚ[ℂ] ℂ) (hcyc : ∀ a b, φ (a * b) = φ (b * a)) (hunit : φ 1 = 1) :
    StableFiniteness.IsStablyFinite A :=
  TracialFunctional.stablyFinite φ hcyc (faithful_of_simple φ hcyc hsimple.2 hunit)

end Suzuki.SimpleTraces

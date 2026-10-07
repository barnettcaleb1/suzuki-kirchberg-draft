import Suzuki.UniversalCStar

/-! Relations holding in every member of a bounded family hold in its actual
completed envelope. This identifies the kernel and transfers equations; it does
not assume that the supplied family separates the input algebra. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Suzuki.UniversalCStar

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
  (R : BoundedFamily A)

theorem inclusion_eq_zero_iff (a : A) :
    inclusion R a = 0 ↔ ∀ i, R.hom i a = 0 := by
  constructor
  · intro h i
    rw [← representation_inclusion, h, map_zero]
  · intro h
    apply norm_eq_zero.mp
    rw [norm_inclusion]
    simp only [supNorm, h, norm_zero, ciSup_const]

theorem inclusion_eq_iff (a b : A) :
    inclusion R a = inclusion R b ↔ ∀ i, R.hom i a = R.hom i b := by
  rw [← sub_eq_zero, ← map_sub, inclusion_eq_zero_iff]
  simp only [map_sub, sub_eq_zero]

theorem inclusion_injective_iff :
    Function.Injective (inclusion R) ↔
      ∀ a b : A, (∀ i, R.hom i a = R.hom i b) → a = b := by
  constructor
  · intro h a b hab
    exact h ((inclusion_eq_iff R a b).mpr hab)
  · intro h a b hab
    exact h a b ((inclusion_eq_iff R a b).mp hab)

theorem nonzero_of_representation (a : A) (i : R.Index) (ha : R.hom i a ≠ 0) :
    inclusion R a ≠ 0 := fun h => ha ((inclusion_eq_zero_iff R a).mp h i)

end Suzuki.UniversalCStar

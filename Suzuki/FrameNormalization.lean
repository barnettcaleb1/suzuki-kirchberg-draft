import Suzuki.CommonCorner
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Normalizing an approximate finite frame

A finite family supported on `p` whose positive square sum is within distance
one of the identity can be normalized to an exact frame by functional calculus.
The approximation hypothesis is explicit. Deriving it from ideal fullness is
still a separate obligation.
-/

noncomputable section

namespace Suzuki.CommonCorner

open scoped CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {p : A} (hp : IsStarProjection p) {n : ℕ}

/-- Normalize an invertible positive square sum by its inverse square root. -/
def Frame.ofStrictlyPositive (x : Fin n → A) (support : ∀ i, x i * p = x i)
    (h : IsStrictlyPositive (∑ i, x i * star (x i))) : Frame hp n where
  x i := (∑ j, x j * star (x j)) ^ (-(1 / 2) : ℝ) * x i
  support i := by rw [mul_assoc, support]
  total := by
    have hs : star ((∑ j, x j * star (x j)) ^ (-(1 / 2) : ℝ)) =
        (∑ j, x j * star (x j)) ^ (-(1 / 2) : ℝ) :=
      (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
    simp only [star_mul, hs, mul_assoc]
    rw [← Finset.mul_sum]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    simpa only [mul_assoc] using CFC.conjugate_rpow_neg_one_half _ h

/-- A norm approximation to the identity gives an exact finite frame.
Both the C⋆-norm and the inverse square root are the actual analytic ones. -/
def Frame.ofApproximation (x : Fin n → A) (support : ∀ i, x i * p = x i)
    (h : ‖1 - ∑ i, x i * star (x i)‖ < 1) : Frame hp n := by
  have hu : IsUnit (∑ i, x i * star (x i)) := by
    simpa only [Units.val_oneSub, sub_sub_cancel] using
      (Units.oneSub (1 - ∑ i, x i * star (x i)) h).isUnit
  exact Frame.ofStrictlyPositive hp x support
    (hu.isStrictlyPositive (Finset.sum_nonneg fun _ _ => mul_star_self_nonneg _))

end Suzuki.CommonCorner

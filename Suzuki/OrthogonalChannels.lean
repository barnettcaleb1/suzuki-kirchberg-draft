import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Orthogonal channels as actual star homomorphisms

The finite-channel sum in Section 5 is a unital star homomorphism when its
channel units are orthogonal and sum to one. A single faithful channel makes
the sum faithful. This does not construct the specific graph/coefficient maps.
-/

namespace Suzuki.OrthogonalChannels

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable {ι : Type*}
variable (f : ι → A →⋆ₙₐ[ℂ] B)
variable (orthogonal : ∀ i j, i ≠ j → f i 1 * f j 1 = 0)

include orthogonal

/-- Orthogonal channel units force all mixed products to vanish. -/
theorem cross_mul (i j : ι) (hij : i ≠ j) (a b : A) : f i a * f j b = 0 := by
  calc
    f i a * f j b = (f i a * f i 1) * (f j 1 * f j b) := by
      simp only [← map_mul, mul_one, one_mul]
    _ = f i a * (f i 1 * f j 1) * f j b := by simp only [mul_assoc]
    _ = 0 := by rw [orthogonal i j hij]; simp

variable [Fintype ι]

/-- The pointwise sum is multiplicative, with no commutativity assumption. -/
theorem sum_mul (a b : A) :
    (∑ i, f i a) * (∑ i, f i b) = ∑ i, f i (a * b) := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · exact (map_mul (f i) a b).symm
  · intro j _ hji
    exact cross_mul f orthogonal i j hji.symm a b
  · simp

/-- The actual unital complex star homomorphism defined by orthogonal channels. -/
noncomputable def sumHom (unit_sum : ∑ i, f i 1 = 1) : A →⋆ₐ[ℂ] B where
  toFun a := ∑ i, f i a
  map_one' := unit_sum
  map_mul' := fun a b => (sum_mul f orthogonal a b).symm
  map_zero' := by simp
  map_add' := by intro a b; simp only [map_add, Finset.sum_add_distrib]
  commutes' := by
    intro z
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, ← Finset.smul_sum, unit_sum]
  map_star' := by intro a; simp only [map_star, star_sum]

/-- Compression by the unit of a channel recovers that channel exactly. -/
theorem compression (i : ι) (a : A) :
    f i 1 * (∑ j, f j a) = f i a := by
  classical
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [← map_mul, one_mul]
  · intro j _ hji
    exact cross_mul f orthogonal i j hji.symm 1 a
  · simp

/-- If one channel is injective then their sum is injective. -/
theorem sumHom_injective (unit_sum : ∑ i, f i 1 = 1)
    (i : ι) (hi : Function.Injective (f i)) :
    Function.Injective (sumHom f orthogonal unit_sum) := by
  intro a b hab
  apply hi
  have h := congrArg (fun x : B => f i 1 * x) hab
  change f i 1 * (∑ j, f j a) = f i 1 * (∑ j, f j b) at h
  simpa only [compression f orthogonal] using h

end Suzuki.OrthogonalChannels

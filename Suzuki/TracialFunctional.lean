import Suzuki.StableFiniteness
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# Actual positive tracial functionals and stable finiteness

This bridge uses a complex-linear positive map on a C*-algebra. It connects
such a faithful tracial functional to the matrix argument; existence of a
functional on the constructed limit is a separate, unproved obligation.
-/

namespace Suzuki
namespace TracialFunctional

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The real part of an actual positive faithful complex-linear trace supplies
all the algebraic trace data used by the stable-finiteness proof. -/
noncomputable def toFaithfulTrace (φ : A →ₚ[ℂ] ℂ)
    (hcyc : ∀ a b, φ (a * b) = φ (b * a))
    (hfaith : ∀ a, φ (star a * a) = 0 → a = 0) :
    StableFiniteness.FaithfulTrace A where
  toAddMonoidHom := {
    toFun := fun a => (φ a).re
    map_zero' := by simp
    map_add' := by intro a b; simp }
  cyclic := fun a b => congrArg Complex.re (hcyc a b)
  nonnegative := fun a => (Complex.nonneg_iff.mp
    (map_nonneg φ (star_mul_self_nonneg a))).1
  faithful := by
    intro a ha
    apply hfaith a
    apply Complex.ext
    · exact ha
    · exact (Complex.nonneg_iff.mp
        (map_nonneg φ (star_mul_self_nonneg a))).2.symm

/-- An actual positive faithful tracial functional on a C*-algebra implies
stable finiteness in every matrix size. Normalization at one is not needed. -/
theorem stablyFinite (φ : A →ₚ[ℂ] ℂ)
    (hcyc : ∀ a b, φ (a * b) = φ (b * a))
    (hfaith : ∀ a, φ (star a * a) = 0 → a = 0) :
    StableFiniteness.IsStablyFinite A :=
  StableFiniteness.faithful_trace_stablyFinite (toFaithfulTrace φ hcyc hfaith)

end TracialFunctional
end Suzuki

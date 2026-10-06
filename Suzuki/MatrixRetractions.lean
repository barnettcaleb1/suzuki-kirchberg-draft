import Suzuki.CornerCPApproximation
import Mathlib.Data.Matrix.Basis

/-!
# Concrete matrix-coordinate completely positive retractions

A diagonal coordinate is obtained by projection compression and the explicit
star equivalence of its one-coordinate corner with the coefficient algebra.
The diagonal coefficient embedding therefore has an actual CPC left inverse.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Suzuki.MatrixRetractions

open CommonCorner FiniteCPApproximation CornerCPApproximation
open scoped CStarAlgebra ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {n : Type} [Fintype n] [DecidableEq n] (i : n)

/-- Place a coefficient at one diagonal coordinate; the map is nonunital. -/
def singleHom : A →⋆ₙₐ[ℂ] CStarMatrix n n A where
  toFun a := CStarMatrix.ofMatrix (Matrix.single i i a)
  map_zero' := Matrix.single_zero _ _
  map_add' a b := Matrix.single_add _ _ a b
  map_smul' z a := (Matrix.smul_single z i i a).symm
  map_mul' a b := (Matrix.single_mul_single_same a i i i b).symm
  map_star' a := (Matrix.conjTranspose_single i i a).symm

omit [PartialOrder A] [StarOrderedRing A] in
theorem singleHom_injective : Function.Injective (singleHom (A := A) i) := by
  intro a b h
  have h' := congrArg (fun M : CStarMatrix n n A => M i i) h
  change Matrix.single i i a i i = Matrix.single i i b i i at h'
  simpa only [Matrix.single_apply_same] using h'

/-- The actual coordinate projection. -/
def coordinateProjection : CStarMatrix n n A := singleHom i (1 : A)

theorem coordinateProjection_isProjection : IsStarProjection (coordinateProjection (A := A) i) :=
  image_one_projection (singleHom (A := A) i)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Compression by the coordinate projection keeps exactly one coefficient. -/
theorem coordinate_sandwich (M : CStarMatrix n n A) :
    coordinateProjection i * M * coordinateProjection i = singleHom i (M i i) := by
  change Matrix.single i i (1 : A) * CStarMatrix.ofMatrix.symm M * Matrix.single i i 1 =
    Matrix.single i i (CStarMatrix.ofMatrix.symm M i i)
  simpa only [one_mul, mul_one] using Matrix.single_mul_mul_single i i i i 1
    (CStarMatrix.ofMatrix.symm M) 1

/-- The coefficient algebra is exactly the corner at one matrix coordinate. -/
def coordinateEquiv : A ≃⋆ₐ[ℂ] Corner (coordinateProjection_isProjection (A := A) i) :=
  StarAlgEquiv.ofBijective
    (toCornerHom (singleHom i) (coordinateProjection_isProjection i) rfl) ⟨by
      intro a b h
      exact singleHom_injective i (congrArg Subtype.val h), by
      intro M
      refine ⟨(M : CStarMatrix n n A) i i, ?_⟩
      apply Subtype.ext
      change singleHom i ((M : CStarMatrix n n A) i i) = (M : CStarMatrix n n A)
      rw [← coordinate_sandwich, left_support, right_support]⟩

/-- Matrix diagonal entry as an actual completely positive map. -/
def entryCP : CStarMatrix n n A →CP A :=
  cpComp (homCP (coordinateEquiv (A := A) i).symm.toStarAlgHom)
    (compressionCP (coordinateProjection_isProjection i))

@[simp] theorem entryCP_apply (M : CStarMatrix n n A) : entryCP i M = M i i := by
  apply (coordinateEquiv (A := A) i).injective
  change coordinateEquiv i ((coordinateEquiv i).symm
    (compress (coordinateProjection_isProjection i) M)) = coordinateEquiv i (M i i)
  rw [StarAlgEquiv.apply_symm_apply]
  apply Subtype.ext
  exact coordinate_sandwich i M

theorem entryCP_contractive (M : CStarMatrix n n A) : ‖entryCP i M‖ ≤ ‖M‖ := by
  change ‖(coordinateEquiv i).symm (compress (coordinateProjection_isProjection i) M)‖ ≤ ‖M‖
  rw [NonUnitalStarAlgHom.norm_map (coordinateEquiv i).symm (coordinateEquiv i).symm.injective]
  exact compression_contractive (coordinateProjection_isProjection i) M

/-- Repeat a coefficient down the whole diagonal. -/
def diagonalHom : A →⋆ₐ[ℂ] CStarMatrix n n A where
  toFun a := CStarMatrix.ofMatrix (Matrix.diagonal fun _ => a)
  map_zero' := Matrix.diagonal_zero
  map_one' := rfl
  map_add' _ _ := (Matrix.diagonal_add _ _).symm
  map_mul' _ _ := (Matrix.diagonal_mul_diagonal _ _).symm
  commutes' _ := rfl
  map_star' _ := (Matrix.diagonal_conjTranspose _).symm

@[simp] theorem entryCP_diagonal (a : A) : entryCP i (diagonalHom (n := n) a) = a := by
  rw [entryCP_apply]
  exact Matrix.diagonal_apply_eq _ _

include i in
/-- A nonempty diagonal amplification has an explicit completely positive
contractive left inverse, rather than an assumed conditional expectation. -/
theorem diagonal_has_cpc_retraction :
    ∃ r : CStarMatrix n n A →CP A,
      (∀ M, ‖r M‖ ≤ ‖M‖) ∧ ∀ a, r (diagonalHom a) = a :=
  ⟨entryCP i, entryCP_contractive i, entryCP_diagonal i⟩

end Suzuki.MatrixRetractions

import Suzuki.ActualAmalgamCorner
import Suzuki.PrescribedUnitCoordinate

/-! The exact common-stage projection and its image in the constructed limit.
This is an equality of actual elements under actual maps; it supplies the
manuscript correspondence between the projection used by K0 and the projection
used to form the full-amalgam corner. There are no KK or unit-class premises. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Suzuki.ActualInitialProjection
open TensorCoefficientChannels PrescribedUnitCoordinate ActualGraphCoefficientSystem
open ActualAmalgamCorner MultiplicityEmbeddings SequentialCStarLimit
open scoped CStarAlgebra ComplexOrder
universe u
variable (T : Spatial.{u}) (Ft : FiniteTensorCoordinates T)
variable (H : GraphCoefficientLimit.GraphInput.{u}) (S : GraphCoefficientLimit.SupportInput T)
variable (F : CoefficientModelFromExtension.Algebra.{u}) (R : CoefficientSchedule.Schedule F)
variable {n : ℕ}

def common (p q : coefficientMatrices (CoefficientSchedule.E F) n) :
    (finiteSystem T F R n .common).obj 0 :=
  commonTensorProjection T Ft p q

def scalarCommon (n : ℕ) : scalarBlocks (CommonUnitProjection.commonSize n) →⋆ₐ[ℂ]
    graphStage ((R.recursive n).stage 0) :=
  (graphFirst ((R.recursive n).stage 0).A ((R.recursive n).stage 0).k
    ((R.recursive n).stage 0).l).comp
      (UniverseLift.map (firstInclusion ((R.recursive n).stage 0).k ((R.recursive n).stage 0).l))

def product (p q : coefficientMatrices (CoefficientSchedule.E F) n) :
    (productSystem T H S F R n).obj 0 :=
  tensorProjection T Ft (scalarCommon F R n) p q

theorem common_projection {p q : coefficientMatrices (CoefficientSchedule.E F) n}
    (hp : IsStarProjection p) (hq : IsStarProjection q) : IsStarProjection (common T Ft F R p q) :=
  commonTensorProjection_projection T Ft hp hq

theorem common_nonzero (p q : coefficientMatrices (CoefficientSchedule.E F) n) :
    common T Ft F R p q ≠ 0 := by
  let : Nontrivial (CoefficientSchedule.E F) :=
    (inferInstance : Nontrivial (Unitization ℂ F))
  exact commonTensorProjection_nonzero T Ft p q

theorem product_projection {p q : coefficientMatrices (CoefficientSchedule.E F) n}
    (hp : IsStarProjection p) (hq : IsStarProjection q) : IsStarProjection (product T Ft H S F R p q) :=
  tensorProjection_projection T Ft _ hp hq

/-- The projection forming the actual full-amalgam corner is precisely the
image of the tensor projection whose KK class is calculated at stage zero. -/
theorem limit_projection (ME : MaximalOn T (CoefficientSchedule.E F))
    (p q : coefficientMatrices (CoefficientSchedule.E F) n) :
    productProjection T H S F R n ME (common T Ft F R p q) =
      stage (productSystem T H S F R n) 0 (product T Ft H S F R p q) := by
  rw [productProjection_stage]
  congr 1
  let P := (R.recursive n).stage 0
  have hm : (T.unitalMap (graphFirst P.A P.k P.l) (StarAlgHom.id ℂ (CoefficientSchedule.E F))).comp
      (T.unitalMap (UniverseLift.map (firstInclusion P.k P.l)) (StarAlgHom.id ℂ (CoefficientSchedule.E F))) =
      T.unitalMap (scalarCommon F R n) (StarAlgHom.id ℂ (CoefficientSchedule.E F)) := by
    apply StarAlgHom.ext
    intro x
    exact DFunLike.congr_fun (T.map_comp
      (UniverseLift.map (firstInclusion P.k P.l)).toNonUnitalStarAlgHom
      (graphFirst P.A P.k P.l).toNonUnitalStarAlgHom
      (StarAlgHom.id ℂ (CoefficientSchedule.E F)).toNonUnitalStarAlgHom
      (StarAlgHom.id ℂ (CoefficientSchedule.E F)).toNonUnitalStarAlgHom) x
  exact DFunLike.congr_fun hm (common T Ft F R p q)

end Suzuki.ActualInitialProjection

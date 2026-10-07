import Suzuki.ActualInitialProjection
import Suzuki.ActualKKCornerClassification

/-! Conditional verification of the exact main claim.
All analytic inputs below are universal standard interfaces. Their intended
realization in actual KK theory and their published-source correspondence are
external obligations. The graph/coefficient construction, bond calculation,
limits, common projection and prescribed unit are derived in this library.
There is no UCT premise on a target or a coefficient algebra. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 4000000
set_option linter.checkUnivs false
namespace Suzuki
open CategoryTheory CoefficientModelFromExtension TensorCoefficientChannels
open ActualCoefficientKK ActualUnitKK PrescribedUnitCoordinate GraphChannelKKCalculation
open scoped CStarAlgebra ComplexOrder
universe u v w t
variable {K : Type v} [Category.{w} K] [Preadditive K]

/-- The published analytic inputs and their literal actual-map interpretation.
Each field is generic; no field asserts any manuscript construction conclusion. -/
structure PublishedInputs where
  kk : KKInterpretation.{u,v,w} (K := K)
  extension : ConditionalMainConstruction.ExtensionInputs kk
  spatial : Spatial.{u}
  analytic : ConditionalMainConstruction.AnalyticInputs spatial
  finiteNuclear : ActualFiniteCoefficientLimits.FiniteNuclearInput.{u}
  tensorKK : SpatialKKInput kk spatial
  scalarTensor : ScalarTensorInput kk tensorKK.exterior
  matrix : MatrixInput kk
  kGroups : KTheory.{u,v,w,t} kk
  finiteK0 : FiniteK0Input
  graphUCT : FreeUCTInput kk kGroups
  finiteCone : UniverseCone.Input kk kGroups finiteK0 graphUCT
  reference : ReferenceInput kk kGroups graphUCT
  finiteTensor : FiniteTensorCoordinates spatial
  projection : ProjectionK0.{u,w} spatial finiteTensor
  projectionInterpretation : ProjectionInterpretation kk spatial finiteTensor projection
  representable : RepresentableInput kk kGroups
  projectionExterior : ProjectionExteriorInput kk projectionInterpretation tensorKK scalarTensor
  ranks : FiniteProjectionRanks finiteK0
  coneProjection : ProjectionConeInput kk spatial finiteTensor projection projectionInterpretation
    kGroups representable finiteK0 graphUCT finiteCone ranks
  referenceGenerator : ReferenceGeneratorInput kk kGroups representable graphUCT reference
  projectionRepresentatives : ProjectionRepresentatives spatial finiteTensor projection
  milnor : ConditionalMainConstruction.MilnorInputs kk
  morita : ActualKKCornerClassification.FullCornerKKInput kk
  classification : ActualKKCornerClassification.ClassificationInput kk

/-- Exact MainClaim, conditional on the listed published analytic interfaces.
The interfaces must be realized in actual KK theory; that external obligation
is separate from this kernel proof and its axiom audit. -/
theorem fullTheoremConditional (P : PublishedInputs.{u,v,w,t} (K := K)) :
    Target.MainClaim.{u} := by
  intro B hB
  let J := P.kk
  let T := P.spatial
  let A := P.analytic
  let F := ConditionalMainConstruction.coefficient J P.extension B hB
  let R := ConditionalMainConstruction.schedule J P.extension B hB
  have hF : Nuclear F := ConditionalMainConstruction.coefficient_nuclear J P.extension B hB
  have hE := ConditionalMainConstruction.unitization_nuclear J P.extension B hB
  let ξ := ConditionalMainConstruction.coefficientIso J P.extension B hB
  let unitB := ActualKKCornerClassification.unitClass J B hB.1
  obtain ⟨n,p,q,hp,hq,hrep,_hscalar,_hreduced⟩ :=
    ActualUnitKK.prescribedRepresentatives J T P.finiteTensor P.projection
      P.projectionInterpretation P.projectionRepresentatives P.extension.unitizationSplit
      hF ξ unitB
  let S := ConditionalMainConstruction.graphSystem J P.extension B hB T A n
  let sep := ConditionalMainConstruction.graph_stage_separable J P.extension B hB T A n
  let co := fun h => ActualBond.coordinate J P.kGroups P.finiteK0 P.graphUCT
    P.finiteCone P.reference T A.graph P.tensorKK ((R.recursive n).stage h)
    (CoefficientSchedule.E F) (ActualBond.coefficientSeparable F)
  let rs := P.scalarTensor.splitting J P.tensorKK.exterior P.extension.unitizationSplit F hF
  let bond := ConditionalMainConstruction.stageClass J S sep
  let stage := ConditionalMainConstruction.inclusionClass J S sep
  have hb : ∀ h, bond h ≫ (co (h+1)).hom = (co h).hom ≫ rs.f := by
    intro h
    have hc := ActualBond.system_bond J P.kGroups P.finiteK0 P.graphUCT P.finiteCone
      P.reference T A.graph A.support P.matrix P.tensorKK (R.recursive n) h F hF
      P.extension.unitizationSplit P.scalarTensor (R.sigma h)
    dsimp only [bond, ConditionalMainConstruction.stageClass]
    rw [TensorEvaluationPaths.step_eq_phi]
    apply (cancel_epi (co h).inv).mp
    simpa only [← Category.assoc, Iso.inv_hom_id,Category.id_comp] using hc
  have hs : ∀ h, bond h ≫ stage (h+1) = stage h :=
    ConditionalMainConstruction.inclusionClass_compatible J S sep
  let M := ConditionalMainConstruction.graphMilnor J P.extension B hB T A n P.milnor
  let li := ConditionalKKTransport.limitIso co bond stage P.milnor.suspension M rs hb hs
  let L := ConditionalMainConstruction.graphLimit J P.extension B hB T A n
  have hL : Target.IsKirchberg L :=
    ConditionalMainConstruction.graphLimit_kirchberg J P.extension B hB T A n
  let ME := ConditionalMainConstruction.coefficientMaximal J P.extension B hB T A
  let p₀ := ActualInitialProjection.common T P.finiteTensor F R p q
  have hp₀ : IsStarProjection p₀ := ActualInitialProjection.common_projection T P.finiteTensor F R hp hq
  have hn₀ : p₀ ≠ 0 := ActualInitialProjection.common_nonzero T P.finiteTensor F R p q
  let pp := ActualAmalgamCorner.productProjection T A.graph A.support F R n ME p₀
  have hpp : IsStarProjection pp :=
    ActualAmalgamCorner.productProjection_projection T A.graph A.support F R n ME hp₀
  have hnpp : pp ≠ 0 := ActualAmalgamCorner.productProjection_nonzero
    T A.graph A.support F R n P.finiteNuclear A.tensorFaithfulness hE ME A.comparison hn₀
  have presentation : Target.HasFiniteAmalgam (ActualKKCornerClassification.cornerTarget L hpp) :=
    ActualAmalgamCorner.corner_hasFiniteAmalgam T A.graph A.support F R n
      P.finiteNuclear A.tensorFaithfulness hE ME hp₀ hn₀
  have hzero := ActualUnitKK.stageZero_projection_prescribed J T P.finiteTensor P.projection
    P.projectionInterpretation P.kGroups P.representable P.finiteK0 P.graphUCT P.finiteCone
    P.ranks P.coneProjection A.graph P.tensorKK P.scalarTensor P.projectionExterior n
    P.reference P.referenceGenerator P.extension.unitizationSplit hF ξ unitB hp hq hrep
  let ps := ActualInitialProjection.product T P.finiteTensor A.graph A.support F R p q
  have hps : IsStarProjection ps := ActualInitialProjection.product_projection
    T P.finiteTensor A.graph A.support F R hp hq
  have ha : J.map (projectionMap (ConditionalMainConstruction.stageAlgebra S sep 0) ps hps)
      ≫ (co 0).hom = (unitB ≫ ξ.inv) ≫ rs.j := by
    exact hzero
  have himage : pp = SequentialCStarLimit.stage S 0 ps :=
    ActualInitialProjection.limit_projection T P.finiteTensor A.graph A.support F R ME p q
  have hmap : J.map (projectionMap (ofUnital L hL.1) pp hpp) =
      J.map (projectionMap (ConditionalMainConstruction.stageAlgebra S sep 0) ps hps) ≫ stage 0 := by
    dsimp only [stage, ConditionalMainConstruction.inclusionClass]
    rw [← J.map_comp]
    apply congrArg (fun f => J.map (A := ActualUnitKK.scalar) (B := ofUnital L hL.1) f)
    ext z
    change z.down • pp = (SequentialCStarLimit.stage S 0) (z.down • ps)
    rw [map_smul,himage]
  have hunit : J.map (projectionMap (ofUnital L hL.1) pp hpp) ≫
      (li.symm.trans ξ).hom = unitB := by
    change J.map (projectionMap (ofUnital L hL.1) pp hpp) ≫ li.inv ≫ ξ.hom = _
    rw [← Category.assoc,hmap,
      ConditionalKKTransport.prescribed_class co bond stage P.milnor.suspension M rs hb hs 0
        (J.map (projectionMap (ConditionalMainConstruction.stageAlgebra S sep 0) ps hps))
        (unitB ≫ ξ.inv) ha]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact ActualKKCornerClassification.classifyCorner J P.morita P.classification
    L B hL hB hpp hnpp presentation (li.symm.trans ξ) hunit

end Suzuki

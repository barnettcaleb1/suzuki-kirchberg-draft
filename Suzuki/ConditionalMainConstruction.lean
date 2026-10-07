import Suzuki.GraphCoefficientLimit
import Suzuki.ConditionalKKTransport

/-! The actual starting objects of the conditional main construction.
The published extension, nuclearity/lifting/cone/Bott laws are explicit inputs.
The coefficient model, its separating schedule and the actual Kirchberg limit
are derived. No target/coefficient UCT occurs. The final main theorem still
requires the actual finite-amalgam corner and KK/unit calculation.

Sources and exact correspondence obligations are inherited field by field from
CoefficientModelFromExtension and GraphCoefficientLimit; this module adds no
new analytic assertion as a premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Suzuki.ConditionalMainConstruction
open CategoryTheory CoefficientModelFromExtension
open TensorCoefficientChannels GraphCoefficientLimit
open scoped CStarAlgebra ComplexOrder
universe u v w
variable {K : Type v} [Category.{w} K] [Preadditive K]

/-- Established extension theory, with the same actual-KK interpretation. -/
structure ExtensionInputs (J : KKInterpretation.{u,v,w} (K := K)) where
  nuclearity : NuclearityInput.{u}
  lifting : LiftingInput.{u}
  dadarlat : DadarlatInput.{u}
  coneBott : ConeBottInput J
  unitizationSplit : SplitUnitizationInput J

/-- Generic graph, tensor and comparison inputs for the actual analytic limit. -/
structure AnalyticInputs (T : Spatial.{u}) where
  graph : GraphInput.{u}
  support : SupportInput T
  comparison : EvaluationLimitPureInfiniteness.ComparisonInput.{u}
  tensorFaithfulness : TensorEvaluationPaths.JointFaithfulnessInput T
  /-- P1: minimal equals maximal for a nuclear second factor; Blackadar
  8 February 2017, II.9 and IV.3.1. The quantifier is over every factor. -/
  maximalNuclear : ∀ E : TensorCoefficientChannels.Algebra.{u},
    Target.HasCPApproximation ⟨E, inferInstance⟩ → MaximalOn T E

variable (J : KKInterpretation.{u,v,w} (K := K)) (P : ExtensionInputs J)
variable (B : Target.UnitalAlgebra.{u}) (hB : Target.IsKirchberg B)

/-- The target is put into KK using its proved separability alone. -/
def target : CoefficientModelFromExtension.Algebra.{u} := ofUnital B hB.1

theorem target_nuclear : Nuclear (target B hB) := hB.2.1

/-- Only the original published extension is chosen here. -/
def original : OriginalExtension (target B hB) :=
  Classical.choice (P.dadarlat.original_extension (target B hB) (target_nuclear B hB))

def coefficient : CoefficientModelFromExtension.Algebra.{u} :=
  (original J P B hB).coefficient

theorem coefficient_nuclear : Nuclear (coefficient J P B hB) :=
  (original J P B hB).coefficient_nuclear P.nuclearity (target_nuclear B hB)

theorem coefficient_rfd : UnitizationRFD.IsRFD (coefficient J P B hB) :=
  (original J P B hB).coefficient_rfd

/-- The forward class is the actual quotient-induced cone map followed by Bott. -/
def coefficientIso : J.object (coefficient J P B hB) ≅ J.object (target B hB) :=
  (original J P B hB).equivalence J P.coneBott P.nuclearity P.lifting (target_nuclear B hB)

def schedule : CoefficientSchedule.Schedule (coefficient J P B hB) :=
  CoefficientSchedule.schedule _ (coefficient_rfd J P B hB)

theorem unitization_nuclear : Target.HasCPApproximation
    (unitalUnitization (coefficient J P B hB)) :=
  (original J P B hB).unitization_target_nuclear P.nuclearity (target_nuclear B hB)

def reducedSplitting : ConditionalKK.Splitting
    (J.object (coefficient J P B hB))
    (J.object (unitization (coefficient J P B hB))) :=
  unitizationSplitting J P.unitizationSplit _ (coefficient_nuclear J P B hB)

theorem reducedSplitting_formula :
    (reducedSplitting J P B hB).f =
      𝟙 (J.object (unitization (coefficient J P B hB))) -
        J.map (scalarRetraction (coefficient J P B hB)) :=
  unitizationSplitting_f J P.unitizationSplit _ (coefficient_nuclear J P B hB)

variable (T : Spatial.{u}) (A : AnalyticInputs T) (n : ℕ)

def coefficientMaximal : MaximalOn T (CoefficientSchedule.E (coefficient J P B hB)) :=
  A.maximalNuclear _ (unitization_nuclear J P B hB)

/-- The dimension n will be fixed by the derived projection representatives. -/
def graphLimit : Target.UnitalAlgebra.{u} :=
  GraphCoefficientLimit.limitAlgebra T A.graph A.support (coefficient J P B hB)
    (schedule J P B hB) n

/-- The exact constructed completed limit is Kirchberg. Its simplicity and
pure infiniteness are proved by the evaluation paths, not interface fields. -/
theorem graphLimit_kirchberg : Target.IsKirchberg (graphLimit J P B hB T A n) :=
  GraphCoefficientLimit.limit_kirchberg T A.graph A.support (coefficient J P B hB)
    (schedule J P B hB) n A.comparison A.tensorFaithfulness (unitization_nuclear J P B hB)

abbrev graphSystem : InductiveAmalgam.System.{u} :=
  (GraphCoefficientLimit.coefficientChannels T A.graph A.support (coefficient J P B hB)
    (schedule J P B hB) n).system

theorem graph_stage_separable (h : ℕ) :
    TopologicalSpace.SeparableSpace ((graphSystem J P B hB T A n).obj h) := by
  let : TopologicalSpace.SeparableSpace (CoefficientSchedule.E (coefficient J P B hB)) :=
    (inferInstance : TopologicalSpace.SeparableSpace (Unitization ℂ (coefficient J P B hB)))
  exact A.support.tensor_separable _ _
    (GraphCoefficientLimit.stage_kirchberg A.graph
      (((schedule J P B hB).recursive n).stage h)).1 inferInstance

theorem graph_stage_nuclear (h : ℕ) : Target.HasCPApproximation
    ⟨(graphSystem J P B hB T A n).obj h, inferInstance⟩ :=
  A.support.tensor_nuclear _ _
    (GraphCoefficientLimit.stage_kirchberg A.graph
      (((schedule J P B hB).recursive n).stage h)).2.1
    (unitization_nuclear J P B hB)

section Milnor
variable (J : KKInterpretation.{u,v,w} (K := K))
variable (S : InductiveAmalgam.System.{u})
variable (separable : ∀ h, TopologicalSpace.SeparableSpace (S.obj h))

def stageAlgebra (h : ℕ) : CoefficientModelFromExtension.Algebra.{u} :=
  ⟨S.obj h, inferInstance, separable h⟩

def stageClass (h : ℕ) : J.object (stageAlgebra S separable h) ⟶
    J.object (stageAlgebra S separable (h+1)) :=
  J.map ((S.step h).toNonUnitalStarAlgHom)

variable [Fact (∀ h, Function.Injective (S.step h))]

def limitKKAlgebra : CoefficientModelFromExtension.Algebra.{u} := by
  letI : ∀ h, TopologicalSpace.SeparableSpace (S.obj h) := separable
  exact ⟨SequentialCStarLimit.Limit S, inferInstance, inferInstance⟩

def inclusionClass (h : ℕ) : J.object (stageAlgebra S separable h) ⟶
    J.object (limitKKAlgebra S separable) :=
  J.map ((SequentialCStarLimit.stage S h).toNonUnitalStarAlgHom)

omit [Preadditive K] in
/-- Compatibility is proved for the classes of the actual connecting maps. -/
theorem inclusionClass_compatible (h : ℕ) :
    stageClass J S separable h ≫ inclusionClass J S separable (h+1) =
      inclusionClass J S separable h := by
  have hc := congrArg StarAlgHom.toNonUnitalStarAlgHom
    (SequentialCStarLimit.stage_commutes S h)
  have hmap := J.map_comp (A := stageAlgebra S separable h)
    (B := stageAlgebra S separable (h+1)) (C := limitKKAlgebra S separable)
    ((S.step h).toNonUnitalStarAlgHom)
    ((SequentialCStarLimit.stage S (h+1)).toNonUnitalStarAlgHom)
  exact hmap.symm.trans (congrArg (fun f => J.map (A := stageAlgebra S separable h)
    (B := limitKKAlgebra S separable) f) hc)

end Milnor

/-- EXTERNAL P7: the analytic Milnor sequence for every actual injective
sequential system of separable nuclear algebras. The stage/limit objects and
maps above are fixed actual objects/maps. Rosenberg--Schochet Duke 55 (1987),
Theorems 1.12 and 1.14(b), with the previously recorded excerpt-access limits.
The suspension and all-Z quantifier must correspond to actual KK on the
designated separable category; there is no UCT restriction on any coefficient.
Neither a limit equivalence nor a channel equation is an input field. -/
structure MilnorInputs (J : KKInterpretation.{u,v,w} (K := K)) where
  suspension : K → K
  sequence : ∀ (S : InductiveAmalgam.System.{u})
    (separable : ∀ h, TopologicalSpace.SeparableSpace (S.obj h))
    [Fact (∀ h, Function.Injective (S.step h))],
    (∀ h, Target.HasCPApproximation ⟨S.obj h, inferInstance⟩) →
      ConditionalKKTransport.AnalyticMilnorInput suspension
        (fun h => J.object (stageAlgebra S separable h))
        (stageClass J S separable) (inclusionClass J S separable)

/-- All analytic eligibility hypotheses are supplied by the constructed
graph/coefficient system. The limit KK isomorphism remains to be assembled
from its calculated bond class. -/
def graphMilnor (M : MilnorInputs J) :
    ConditionalKKTransport.AnalyticMilnorInput M.suspension
      (fun h => J.object (stageAlgebra (graphSystem J P B hB T A n)
        (graph_stage_separable J P B hB T A n) h))
      (stageClass J (graphSystem J P B hB T A n)
        (graph_stage_separable J P B hB T A n))
      (inclusionClass J (graphSystem J P B hB T A n)
        (graph_stage_separable J P B hB T A n)) :=
  M.sequence (graphSystem J P B hB T A n)
    (graph_stage_separable J P B hB T A n) (graph_stage_nuclear J P B hB T A n)

end Suzuki.ConditionalMainConstruction

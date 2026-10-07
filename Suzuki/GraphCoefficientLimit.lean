import Suzuki.ActualGraphCoefficientSystem
import Suzuki.CoefficientSchedule

/-! The actual coefficient graph limit, including its exact Kirchberg
properties. Standard graph, matrix, tensor, quotient, and nuclear permanence
facts are explicit universal inputs. The coefficient channels, their detection
paths, and limit simplicity/pure infiniteness are derived.

GraphInput is the ordinary finite positive-graph/full-corner corollary:
Kumjian--Pask--Raeburn (February1998 author version), Corollary3.11;
Ara--Goodearl 1102.4296v2, Remark3.10 for nuclearity; standard matrix/full-corner
permanence. Its graph has M(v,w) edges w→v. Strict positivity gives a direct
edge between every pair; two loops at every vertex give exits to every cycle.
Its exact correspondence to GraphUniversal and the weighted corner remains an
EXTERNAL interpretation obligation. It does not assert an amalgam identity.
-/
noncomputable section
namespace Suzuki.GraphCoefficientLimit
open TensorCoefficientChannels ActualGraphCoefficientSystem RecursiveGraphSequence
open TensorEvaluationPaths SequentialCStarLimit
open scoped CStarAlgebra ComplexOrder
universe u

/-- EXTERNAL standard ordinary-graph properties for arbitrary positive
rank-two adjacency and arbitrary positive corner weights. These are scalar
graphs, with no coefficient algebra, recursive sequence or channel in the input. -/
structure GraphInput : Prop where
  corners : ∀ (M : Matrix Vertex Vertex ℕ) (k l : Vertex → ℕ),
    (∀ v w, 0 < M v w) → (∀ v, 2 ≤ M v v) →
    (∀ v, 0 < k v) → (∀ v, 0 < l v) →
    Target.IsKirchberg ⟨graphProduct.{u} M k l, inferInstance⟩

/-- EXTERNAL generic support. Nuclearity uses exactly CPC finite-matrix
approximation. Blackadar author revision8Feb2017 IV.3.1 (injective limits),
IV.3.1.1 (spatial tensors), IV.3.1.5--6 (CPC characterization), II.8.2 (limits),
II.9 (spatial/maximal tensors), and ordinary matrix ideal Morita correspondence.
No manuscript-specific simplicity or pure-infiniteness assertion occurs. -/
structure SupportInput (T : Spatial.{u}) where
  matrix_maximal : ∀ q, 0 < q → MaximalOn T (matrixAlgebra q)
  matrix_simple : ∀ (A : Algebra.{u}) q, 0 < q →
    Target.IsSimple ⟨A, inferInstance⟩ → Target.IsSimple ⟨amplification A q, inferInstance⟩
  tensor_separable : ∀ (A E : Algebra.{u}), TopologicalSpace.SeparableSpace A →
    TopologicalSpace.SeparableSpace E → TopologicalSpace.SeparableSpace (T.tensor A E)
  tensor_nuclear : ∀ (A E : Algebra.{u}), Target.HasCPApproximation ⟨A, inferInstance⟩ →
    Target.HasCPApproximation ⟨E, inferInstance⟩ → Target.HasCPApproximation ⟨T.tensor A E, inferInstance⟩
  limit_nuclear : ∀ (S : InductiveAmalgam.System.{u})
    [Fact (∀ n, Function.Injective (S.step n))],
    (∀ n, Target.HasCPApproximation ⟨S.obj n, inferInstance⟩) →
      Target.HasCPApproximation ⟨Limit S, inferInstance⟩
  quotients : ∀ A : Target.UnitalAlgebra.{u}, EvaluationLimitSimplicity.ClosedIdealKernelRealization A

/-- The diagonal entries of I+B have at least two loops. -/
theorem stage_two_loops (P : Stage) (v : Vertex) : 2 ≤ P.A v v := by
  have hp := P.positive v v
  change (0 : ℤ) < P.B v v at hp
  change 2 ≤ Int.toNat ((1 : Matrix Vertex Vertex ℤ) v v + P.B v v)
  simp only [Matrix.one_apply_eq]
  omega

theorem stage_kirchberg (H : GraphInput.{u}) (P : Stage) :
    Target.IsKirchberg ⟨graphStage.{u} P, inferInstance⟩ :=
  H.corners P.A P.k P.l (stage_adjacency_positive P) (stage_two_loops P) P.k_pos P.l_pos

variable (T : Spatial.{u}) (H : GraphInput.{u}) (S : SupportInput T)
variable (F : CoefficientModelFromExtension.Algebra.{u}) (R : CoefficientSchedule.Schedule F)
variable (n : ℕ)

abbrev scalarStages : ℕ → Algebra.{u} := fun h => graphStage ((R.recursive n).stage h)

abbrev scalarChannels : ∀ h, ScalarChannels (scalarStages F R n h)
    (scalarStages F R n (h+1)) (R.dimension h) :=
  systemGraphChannels T (R.recursive n)
    (fun h => S.matrix_maximal (R.dimension h) (R.dimension_pos h))
    (fun h => (stage_kirchberg H ((R.recursive n).stage h)).2.2.1)

abbrev coefficientChannels : EvaluationLimitSimplicity.Channels.{u} :=
  channels T (scalarStages F R n) (CoefficientSchedule.E F) R.dimension
    (scalarChannels T H S F R n) (CoefficientSchedule.quotient F)
    (CoefficientSchedule.sectionMap F) R.sigma

/-- The positive channel is part of the actual constructed system, so its
injectivity supplies the normed limit's injectivity instance. -/
instance stepFact : Fact (∀ h, Function.Injective ((coefficientChannels T H S F R n).system.step h)) :=
  TensorEvaluationPaths.stepFact T (scalarStages F R n) (CoefficientSchedule.E F) R.dimension
    (scalarChannels T H S F R n) (CoefficientSchedule.quotient F)
    (CoefficientSchedule.sectionMap F) R.sigma

/-- This property concerns the exact completed system just defined, not an
opaque existential algebra with matching invariants. -/
def limitAlgebra : Target.UnitalAlgebra.{u} :=
  ⟨Limit (coefficientChannels T H S F R n).system, inferInstance⟩

/-- The separately constructed amplified noise maps are faithful. -/
theorem noise_injective : ∀ h, Function.Injective (scalarChannels T H S F R n h).noise :=
  systemGraphChannels_noise_injective T (R.recursive n)
    (fun h => S.matrix_maximal (R.dimension h) (R.dimension_pos h))
    (fun h => (stage_kirchberg H ((R.recursive n).stage h)).2.2.1)
    (fun h => S.matrix_simple (scalarStages F R n h) (R.dimension h) (R.dimension_pos h)
      (stage_kirchberg H ((R.recursive n).stage h)).2.2.1)

/-- End-to-end analytic Kirchberg conclusion for this actual graph/coefficient
system. The input hE is supplied by the derived nuclear RFD coefficient model;
no target or coefficient UCT is used. The graph-stage properties alone are
external; no tensor-stage simplicity or pure infiniteness is assumed. -/
theorem limit_kirchberg
    (I : EvaluationLimitPureInfiniteness.ComparisonInput.{u})
    (faithful : JointFaithfulnessInput T)
    (hE : Target.HasCPApproximation (CoefficientModelFromExtension.unitalUnitization F)) :
    Target.IsKirchberg (limitAlgebra T H S F R n) := by
  let A := scalarStages F R n
  let E := CoefficientSchedule.E F
  let G := scalarChannels T H S F R n
  let ε := CoefficientSchedule.quotient F
  let η := CoefficientSchedule.sectionMap F
  have hA : ∀ h, Target.IsKirchberg ⟨A h, inferInstance⟩ :=
    fun h => stage_kirchberg H ((R.recursive n).stage h)
  let : Nontrivial (A 0) := (hA 0).2.2.1.1
  let : Nontrivial E := (inferInstance : Nontrivial (Unitization ℂ F))
  let : TopologicalSpace.SeparableSpace E := (inferInstance : TopologicalSpace.SeparableSpace (Unitization ℂ F))
  let : ∀ h, TopologicalSpace.SeparableSpace ((channels T A E R.dimension G ε η R.sigma).obj h) :=
    fun h => S.tensor_separable (A h) E (hA h).1 inferInstance
  have hN : ∀ h, Target.HasCPApproximation
      ⟨(channels T A E R.dimension G ε η R.sigma).obj h, inferInstance⟩ :=
    fun h => S.tensor_nuclear (A h) E (hA h).2.1 hE
  change Target.IsKirchberg ⟨Limit (channels T A E R.dimension G ε η R.sigma).system, inferInstance⟩
  refine ⟨SequentialCStarLimit.limitSeparable _, S.limit_nuclear _ hN, ?_, ?_⟩
  · exact TensorEvaluationPaths.limit_simple T A E R.dimension G ε η R.sigma
      faithful R.sigma_tails (noise_injective T H S F R n)
      (fun h => (hA h).2.2.1) (S.quotients (limitAlgebra T H S F R n))
  · exact TensorEvaluationPaths.limit_purelyInfinite T A E R.dimension G ε η R.sigma
      I faithful R.sigma_tails (noise_injective T H S F R n)
      (fun h => (hA h).2.2.1) (fun h => (hA h).2.2.2)

end Suzuki.GraphCoefficientLimit

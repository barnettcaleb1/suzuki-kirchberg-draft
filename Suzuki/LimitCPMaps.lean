import Suzuki.MatrixLimits
import Suzuki.FiniteCPApproximation
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Extending compatible completely positive contractions to concrete limits

The source is the constructed norm-completed injective sequential limit.
Compatibility and norm bounds are hypotheses on actual stage maps.
-/

noncomputable section

namespace Suzuki.LimitCPMaps

open InductiveAmalgam SequentialCStarLimit
open scoped CStarAlgebra ComplexOrder

universe u

variable (S : System.{u}) [Fact (∀ n, Function.Injective (S.step n))]

local instance stageOrder (n : ℕ) : PartialOrder (S.obj n) := CStarAlgebra.spectralOrder _
local instance stageOrderedRing (n : ℕ) : StarOrderedRing (S.obj n) :=
  CStarAlgebra.spectralOrderedRing _
local instance limitOrder : PartialOrder (Limit S) := CStarAlgebra.spectralOrder _
local instance limitOrderedRing : StarOrderedRing (Limit S) := CStarAlgebra.spectralOrderedRing _

local instance algebraicTopology :
    TopologicalSpace (DirectedCStarLimit.Algebraic S.obj (transition S)) :=
  (inferInstance : MetricSpace (DirectedCStarLimit.Algebraic S.obj (transition S))).toUniformSpace.toTopologicalSpace

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable (φ : ∀ n, S.obj n →CP B)
variable (hφ : ∀ n a, ‖φ n a‖ ≤ ‖a‖)
variable (hc : ∀ n m h a, φ m (transition S n m h a) = φ n a)

/-- Compatible CP maps induce an actual complex linear map on the algebraic
direct limit. No continuity is inferred from algebraic linearity alone. -/
def algebraicMap : DirectedCStarLimit.Algebraic S.obj (transition S) →ₗ[ℂ] B where
  toFun := DirectLimit.lift (transition S) (fun n => φ n)
    (fun n m h a => (hc n m h a).symm)
  map_add' := DirectLimit.induction₂ (transition S) fun n a b => by
    rw [DirectLimit.add_def]
    exact map_add (φ n) a b
  map_smul' z := DirectLimit.induction (transition S) fun n a => by
    rw [DirectLimit.smul_def]
    exact map_smul (φ n) z a

omit [Fact (∀ n, Function.Injective (S.step n))] in
@[simp] theorem algebraicMap_stage (n : ℕ) (a : S.obj n) :
    algebraicMap S φ hc (DirectedCStarLimit.algebraicStage S.obj (transition S) n a) = φ n a := rfl

include hφ in
theorem algebraicMap_contractive (a : DirectedCStarLimit.Algebraic S.obj (transition S)) :
    ‖algebraicMap S φ hc a‖ ≤ ‖a‖ := by
  induction a using DirectLimit.induction with
  | _ n a => exact hφ n a

/-- The stage contraction bound makes the algebraic map continuous. -/
def algebraicContinuousMap : DirectedCStarLimit.Algebraic S.obj (transition S) →L[ℂ] B :=
  (algebraicMap S φ hc).mkContinuous 1 (by
    intro a
    simpa only [one_mul] using algebraicMap_contractive S φ hφ hc a)

/-- The genuine continuous extension to the C⋆-completion. -/
def continuousMap : Limit S →L[ℂ] B :=
  (algebraicContinuousMap S φ hφ hc).extend UniformSpace.Completion.toComplL

@[simp] theorem continuousMap_coe
    (a : DirectedCStarLimit.Algebraic S.obj (transition S)) :
    continuousMap S φ hφ hc a = algebraicMap S φ hc a :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) a

@[simp] theorem continuousMap_stage (n : ℕ) (a : S.obj n) :
    continuousMap S φ hφ hc (stage S n a) = φ n a :=
  continuousMap_coe S φ hφ hc (DirectedCStarLimit.algebraicStage S.obj (transition S) n a)

/-- The norm bound survives completion. -/
theorem continuousMap_contractive (a : Limit S) : ‖continuousMap S φ hφ hc a‖ ≤ ‖a‖ := by
  induction a using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (Continuous.norm (continuousMap S φ hφ hc).continuous) continuous_norm
  | ih a =>
    rw [continuousMap_coe, UniformSpace.Completion.norm_coe]
    exact algebraicMap_contractive S φ hφ hc a

/-- Entrywise extension is continuous for the genuine finite C⋆-matrix norm. -/
theorem matrixMap_continuous (k : ℕ) : Continuous
    (fun M : CStarMatrix (Fin k) (Fin k) (Limit S) =>
      M.map (continuousMap S φ hφ hc)) := by
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuousMap S φ hφ hc).continuous.comp
      ((continuous_apply j).comp (continuous_apply i))

/-- Positivity of matrix squares survives the dense stage extension. -/
theorem matrixMap_square_nonneg (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) (Limit S)) :
    0 ≤ (star X * X).map (continuousMap S φ hφ hc) := by
  have hd := MatrixLimits.dense_matrix_stage_pairs (Fin k) S
  apply hd.induction_on (X, (0 : CStarMatrix (Fin k) (Fin k) (Limit S)))
    (p := fun z => 0 ≤ (star z.1 * z.1).map (continuousMap S φ hφ hc))
  · exact isClosed_le continuous_const
      ((matrixMap_continuous S φ hφ hc k).comp (continuous_fst.star.mul continuous_fst))
  · rintro ⟨n, a, b⟩
    have h := (φ n).map_cstarMatrix_nonneg (star a * a) (star_mul_self_nonneg a)
    have he : (MatrixLimits.matrixHom (Fin k) (stage S n) (star a * a)).map
        (continuousMap S φ hφ hc) = (star a * a).map (φ n) := by
      ext i j
      exact continuousMap_stage S φ hφ hc n _
    rw [← he] at h
    simpa only [map_mul, map_star] using h

/-- Complete positivity passes to the completion. Positivity is generated by
finite sums of star-squares, whose images are positive by dense approximation. -/
theorem matrixMap_nonneg (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (Limit S))
    (hM : 0 ≤ M) : 0 ≤ M.map (continuousMap S φ hφ hc) := by
  rw [StarOrderedRing.nonneg_iff] at hM
  induction hM using AddSubmonoid.closure_induction with
  | mem a ha =>
    obtain ⟨x, rfl⟩ := ha
    exact matrixMap_square_nonneg S φ hφ hc k x
  | zero =>
    change 0 ≤ (CStarMatrix.mapₗ
      (continuousMap S φ hφ hc).toLinearMap) (0 : CStarMatrix (Fin k) (Fin k) (Limit S))
    rw [map_zero]
  | add a b ha hb iha ihb =>
    change 0 ≤ (CStarMatrix.mapₗ
      (continuousMap S φ hφ hc).toLinearMap) (a + b)
    rw [map_add]
    exact add_nonneg iha ihb

/-- The actual completely positive contraction extending the compatible
family. Complete positivity and contractivity have both been proved. -/
def cpMap : Limit S →CP B where
  toLinearMap := (continuousMap S φ hφ hc).toLinearMap
  map_cstarMatrix_nonneg' := matrixMap_nonneg S φ hφ hc

@[simp] theorem cpMap_stage (n : ℕ) (a : S.obj n) :
    cpMap S φ hφ hc (stage S n a) = φ n a := continuousMap_stage S φ hφ hc n a

theorem cpMap_contractive (a : Limit S) : ‖cpMap S φ hφ hc a‖ ≤ ‖a‖ :=
  continuousMap_contractive S φ hφ hc a

end Suzuki.LimitCPMaps

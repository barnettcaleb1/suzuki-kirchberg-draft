import Suzuki.ActualGraphCoefficientSystem
import Suzuki.RecursiveNoiseFullness
import Suzuki.FiniteTensorLimit
import Suzuki.GraphCoefficientLimit
import Suzuki.MatrixLimits
import Mathlib.Topology.Instances.Complex

/-! Fullness of the actual amplified finite noise maps is transported through
ULift and the recursive successor equality. The actual three constituent
limits are simple, conditional only on generic tensor faithfulness/quotients
and the coefficient's separating tails. No finite constant algebra is assumed
simple, and no full-image conclusion is an external input. -/
noncomputable section
namespace Suzuki.ActualFiniteCoefficientLimits
open TensorCoefficientChannels ActualGraphCoefficientSystem RecursiveGraphSequence
open MultiplicityEmbeddings SequentialCStarLimit TensorEvaluationPaths
open Matrix
open scoped CStarAlgebra ComplexOrder
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512

/-- Every nonzero noise input has full image in the target constant algebra. -/
def FullNoise {A B : Algebra.{u}} {q : ℕ} (G : ScalarChannels A B q) : Prop :=
  ∀ x : amplification A q, x ≠ 0 → ∀ J : TwoSidedIdeal B, G.noise x ∈ J → J = ⊤

/-- Fullness, not only faithfulness, survives the actual universe/matrix adapter. -/
theorem lifted_full {A B : Type} [CStarAlgebra A] [CStarAlgebra B] (q : ℕ)
    (f : CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A →⋆ₙₐ[ℂ] B)
    (hf : ∀ x, x ≠ 0 → ∀ J : TwoSidedIdeal B, f x ∈ J → J = ⊤)
    (x : amplification (UniverseLift.algebra.{u} A) q) (hx : x ≠ 0)
    (J : TwoSidedIdeal (UniverseLift.algebra.{u} B)) (hm : liftMatrixHom q f x ∈ J) : J = ⊤ := by
  let up := (UniverseLift.equiv.{u} B).symm.toStarAlgHom
  let I := J.comap up.toRingHom
  have hd : matrixDown q x ≠ 0 := fun hz =>
    hx (matrixDown_injective q (hz.trans (map_zero _).symm))
  have hI : I = ⊤ := hf (matrixDown q x) hd I ((TwoSidedIdeal.mem_comap up.toRingHom).mpr hm)
  have hone : (1 : B) ∈ I := hI ▸ TwoSidedIdeal.mem_top _
  have hu : up 1 ∈ J := (TwoSidedIdeal.mem_comap up.toRingHom).mp hone
  exact J.eq_top (by simpa only [map_one] using hu)

inductive Constituent | common | left | right

def scalarStage (c : Constituent) (P : Stage) : Algebra.{u} :=
  match c with
  | .common => commonStage P
  | .left => leftStage P
  | .right => rightStage P

def localChannels (c : Constituent) {P : Stage} {q : ℕ} (D : Lift P q) :
    ScalarChannels (scalarStage.{u} c P) (scalarStage.{u} c D.next) q :=
  match c with
  | .common => commonScalarChannels D
  | .left => leftScalarChannels D
  | .right => rightScalarChannels D

theorem local_full (c : Constituent) {P : Stage} {q : ℕ} (D : Lift P q) :
    FullNoise (localChannels.{u} c D) := by
  cases c with
  | common =>
    exact lifted_full q (D.noiseCommon Equiv.ulift)
      (RecursiveNoiseFullness.Lift.noiseCommon_full D Equiv.ulift)
  | left =>
    exact lifted_full q (D.noiseLeft Equiv.ulift)
      (RecursiveNoiseFullness.Lift.noiseLeft_full D Equiv.ulift)
  | right =>
    exact lifted_full q (D.noiseRight Equiv.ulift)
      (RecursiveNoiseFullness.Lift.noiseRight_full D Equiv.ulift)

variable {q : ℕ → ℕ} {k l : Vertex → ℕ}

def scalarChannels (c : Constituent) (S : System q k l) (n : ℕ) :
    ScalarChannels (scalarStage.{u} c (S.stage n)) (scalarStage.{u} c (S.stage (n+1))) (q n) :=
  S.successor n ▸ localChannels c (S.step n)

private theorem transport_full (c : Constituent) {A : Algebra.{u}} {q : ℕ}
    {P Q : Stage} (e : P = Q) (G : ScalarChannels A (scalarStage c P) q)
    (hG : FullNoise G) : FullNoise (e ▸ G) := by
  cases e
  exact hG

theorem system_full (c : Constituent) (S : System q k l) (n : ℕ) :
    FullNoise (scalarChannels.{u} c S n) :=
  transport_full c (S.successor n) _ (local_full c (S.step n))

theorem blocks_nontrivial {V : Type} [Fintype V] (w : V → ℕ) (v : V) (hv : 0 < w v) :
    Nontrivial (UniverseLift.algebra.{u} (Blocks w)) := by
  refine ⟨⟨1,0,?_⟩⟩
  intro hz
  have he := congrArg (fun x : UniverseLift.algebra.{u} (Blocks w) =>
    x.down v ⟨0,hv⟩ ⟨0,hv⟩) hz
  simp at he

theorem stage_nontrivial (c : Constituent) (P : Stage) : Nontrivial (scalarStage.{u} c P) := by
  cases c with
  | common => exact blocks_nontrivial (Sum.elim P.k P.l) (Sum.inl 0) (P.k_pos 0)
  | left => exact blocks_nontrivial (P.k+P.l) 0 (lt_of_lt_of_le (P.k_pos 0) (Nat.le_add_right _ _))
  | right => exact blocks_nontrivial (P.k+P.A*ᵥP.l) 0 (lt_of_lt_of_le (P.k_pos 0) (Nat.le_add_right _ _))

variable (T : Spatial.{u}) (c : Constituent) (S : System q k l) (E : Algebra.{u})
variable (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E) (σ : ∀ n, E →⋆ₐ[ℂ] matrixAlgebra.{u} (q n))

abbrev coefficientChannels : EvaluationLimitSimplicity.Channels.{u} :=
  TensorEvaluationPaths.channels T (fun n => scalarStage c (S.stage n)) E q
    (scalarChannels c S) ε η σ

/-- Each exact finite constituent completed limit is simple. -/
theorem limit_simple [Nontrivial E] (F : JointFaithfulnessInput T)
    (hσ : ∀ N (e : E), e ≠ 0 → ∃ j, N ≤ j ∧ σ j e ≠ 0)
    (quotients : EvaluationLimitSimplicity.ClosedIdealKernelRealization
      (Limit (coefficientChannels T c S E ε η σ).system)) :
    Target.IsSimple ⟨Limit (coefficientChannels T c S E ε η σ).system, inferInstance⟩ := by
  let : Nontrivial (scalarStage.{u} c (S.stage 0)) := stage_nontrivial c (S.stage 0)
  exact FiniteTensorLimit.limit_simple T (fun n => scalarStage c (S.stage n)) E q
    (scalarChannels c S) ε η σ F hσ (system_full c S) quotients

/-- Jointly faithful matrix evaluations reflect one-sided inverse identities.
This universal lemma needs no trace and no tensor-stage finiteness input. -/
theorem tensor_stablyFiniteRing (A E : Algebra.{u}) [IsStablyFiniteRing A]
    (F : JointFaithfulnessInput T) (q : ℕ → ℕ)
    (σ : ∀ j, E →⋆ₐ[ℂ] matrixAlgebra.{u} (q j))
    (hσ : ∀ e : E, e ≠ 0 → ∃ j, σ j e ≠ 0) :
    IsStablyFiniteRing (T.tensor A E) where
  isDedekindFiniteMonoid k := ⟨fun {x y} hxy => by
    ext i j
    by_contra hne
    obtain ⟨r, hr⟩ := F.separates A E q σ hσ
      ((y*x) i j - (1 : Matrix (Fin k) (Fin k) (T.tensor A E)) i j)
      (sub_ne_zero.mpr hne)
    let : IsStablyFiniteRing (amplification A (q r)) :=
      (RingEquiv.isStablyFiniteRing_iff CStarMatrix.ofMatrixRingEquiv).mp inferInstance
    let φ : Matrix (Fin k) (Fin k) (T.tensor A E) →+*
        Matrix (Fin k) (Fin k) (amplification A (q r)) :=
      (evaluation T A E (q r) (σ r)).toAlgHom.toRingHom.mapMatrix
    have hp : φ x * φ y = 1 := by rw [← map_mul, hxy, map_one]
    have hp' : φ (y*x) = φ 1 := by
      rw [map_mul, map_one]
      exact mul_eq_one_symm hp
    have heq : evaluation T A E (q r) (σ r) ((y*x) i j) =
        evaluation T A E (q r) (σ r) ((1 : Matrix (Fin k) (Fin k) (T.tensor A E)) i j) :=
      congrFun (congrFun hp' i) j
    exact hr (by rw [map_sub, heq, sub_self])⟩

theorem blocks_stablyFiniteRing {V : Type} [Fintype V] (w : V → ℕ) :
    IsStablyFiniteRing (UniverseLift.algebra.{u} (Blocks w)) := by
  let : ∀ v, IsStablyFiniteRing (CStarMatrix (Fin (w v)) (Fin (w v)) ℂ) := fun v =>
    (RingEquiv.isStablyFiniteRing_iff CStarMatrix.ofMatrixRingEquiv).mp inferInstance
  let : ∀ n, IsDedekindFiniteMonoid
      (∀ v, Matrix (Fin n) (Fin n) (CStarMatrix (Fin (w v)) (Fin (w v)) ℂ)) :=
    fun n => ⟨fun {x y} h => funext fun v => mul_eq_one_symm (congrFun h v)⟩
  let : IsStablyFiniteRing (Blocks w) := ⟨fun n =>
    IsDedekindFiniteMonoid.of_injective
      (Matrix.piRingEquiv (β := fun v => CStarMatrix (Fin (w v)) (Fin (w v)) ℂ)
        (n := Fin n)) Matrix.piRingEquiv.injective⟩
  exact IsStablyFiniteRing.of_injective (UniverseLift.equiv (Blocks w))
    (UniverseLift.equiv (Blocks w)).injective

theorem scalar_stablyFiniteRing (c : Constituent) (P : Stage) :
    IsStablyFiniteRing (scalarStage.{u} c P) := by
  cases c <;> exact blocks_stablyFiniteRing _

theorem scalar_separable (c : Constituent) (P : Stage) :
    TopologicalSpace.SeparableSpace (scalarStage.{u} c P) := by
  have h {V : Type} [Fintype V] (w : V → ℕ) :
      TopologicalSpace.SeparableSpace (UniverseLift.algebra.{u} (Blocks w)) := by
    let : ∀ v, TopologicalSpace.SeparableSpace (CStarMatrix (Fin (w v)) (Fin (w v)) ℂ) :=
      fun v => inferInstanceAs (TopologicalSpace.SeparableSpace (Fin (w v) → Fin (w v) → ℂ))
    exact (UniverseLift.equiv.{u} (Blocks w)).symm.surjective.denseRange.separableSpace
      (map_continuous (UniverseLift.equiv.{u} (Blocks w)).symm)
  cases c <;> exact h _

/-- EXTERNAL universal finite-dimensional CPAP support; no recursive stage or
limit appears in this premise. -/
structure FiniteNuclearInput : Prop where
  blocks : ∀ {V : Type} [Fintype V] (w : V → ℕ),
    Target.HasCPApproximation ⟨UniverseLift.algebra.{u} (Blocks w), inferInstance⟩

theorem scalar_nuclear (N : FiniteNuclearInput.{u}) (c : Constituent) (P : Stage) :
    Target.HasCPApproximation ⟨scalarStage.{u} c P, inferInstance⟩ := by
  cases c <;> exact N.blocks _

def limitAlgebra : Target.UnitalAlgebra.{u} :=
  ⟨Limit (coefficientChannels T c S E ε η σ).system, inferInstance⟩

/-- All exact finite-constituent properties of this constructed completed
system, including stable finiteness proved by matrix evaluation and density. -/
theorem limit_finiteConstituent [Nontrivial E] [TopologicalSpace.SeparableSpace E]
    (P : GraphCoefficientLimit.SupportInput T) (N : FiniteNuclearInput.{u})
    (F : JointFaithfulnessInput T)
    (hσ : ∀ N (e : E), e ≠ 0 → ∃ j, N ≤ j ∧ σ j e ≠ 0)
    (hE : Target.HasCPApproximation ⟨E, inferInstance⟩) :
    Target.IsFiniteConstituent (limitAlgebra T c S E ε η σ) := by
  let A := fun n => scalarStage.{u} c (S.stage n)
  let D := (coefficientChannels T c S E ε η σ).system
  let : ∀ n, TopologicalSpace.SeparableSpace (D.obj n) := fun n =>
    P.tensor_separable (A n) E (scalar_separable c (S.stage n)) inferInstance
  let : ∀ n, IsStablyFiniteRing (D.obj n) := fun n => by
    let := scalar_stablyFiniteRing c (S.stage n)
    exact tensor_stablyFiniteRing T (A n) E F q σ (fun e he => by
      obtain ⟨j, _, hj⟩ := hσ 0 e he
      exact ⟨j,hj⟩)
  refine ⟨SequentialCStarLimit.limitSeparable D, ?_, ?_, ?_⟩
  · exact P.limit_nuclear D (fun n =>
      P.tensor_nuclear (A n) E (scalar_nuclear N c (S.stage n)) hE)
  · exact limit_simple T c S E ε η σ F hσ
      (P.quotients (limitAlgebra T c S E ε η σ))
  · let : IsStablyFiniteRing (limitAlgebra T c S E ε η σ) := MatrixLimits.isStablyFiniteRing D
    intro n v hv
    exact mul_eq_one_symm hv
end Suzuki.ActualFiniteCoefficientLimits

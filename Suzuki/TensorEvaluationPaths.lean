import Suzuki.TensorCoefficientChannels
import Suzuki.EvaluationLimitPureInfiniteness

/-!
# Actual tensor evaluations, paths, and product-limit witnesses

The joint-faithfulness input is a universal property of the minimal tensor
product, not a detection assertion about the manuscript's channels. All maps
below are the actual tensor maps and matrix identifications. The scalar channel
family is local construction data, to be instantiated by the recursive graph
construction; it is not a final published input.
-/
noncomputable section
namespace Suzuki.TensorEvaluationPaths
open TensorCoefficientChannels
open scoped CStarAlgebra ComplexOrder
universe u

variable (T : Spatial.{u})

/-- The actual coefficient evaluation into the usual matrix amplification. -/
def evaluation (A E : Algebra.{u}) (q : ℕ)
    (σ : E →⋆ₐ[ℂ] matrixAlgebra.{u} q) :
    T.tensor A E →⋆ₐ[ℂ] amplification A q :=
  (T.matrixEquiv A q).toStarAlgHom.comp (T.unitalMap (StarAlgHom.id ℂ A) σ)

@[simp] theorem evaluation_pure (A E : Algebra.{u}) (q : ℕ)
    (σ : E →⋆ₐ[ℂ] matrixAlgebra.{u} q) (a : A) (e : E)
    (i j : ULift.{u} (Fin q)) :
    evaluation T A E q σ (T.pure a e) i j = σ e i j • a := by
  simp [evaluation, Spatial.unitalMap, Spatial.map_pure, Spatial.pure,
    T.matrixEquiv_pure]

/-- EXTERNAL standard spatial-tensor fact: a jointly faithful family of
finite-dimensional representations stays jointly faithful after tensoring
with any Cstar algebra. Intended proof: their direct-sum representation is
faithful and the spatial tensor representation is faithful. No nuclearity,
UCT, graph, channel, inductive system, or limit occurs in this input. -/
structure JointFaithfulnessInput : Prop where
  separates : ∀ (A E : Algebra.{u}) (q : ℕ → ℕ)
    (σ : ∀ j, E →⋆ₐ[ℂ] matrixAlgebra.{u} (q j)),
    (∀ e : E, e ≠ 0 → ∃ j, σ j e ≠ 0) →
    ∀ x : T.tensor A E, x ≠ 0 → ∃ j, evaluation T A E (q j) (σ j) x ≠ 0

/-- Tail separation is deduced by reindexing the generic faithful family. -/
theorem evaluation_tails (F : JointFaithfulnessInput T) (A E : Algebra.{u})
    (q : ℕ → ℕ) (σ : ∀ j, E →⋆ₐ[ℂ] matrixAlgebra.{u} (q j))
    (hσ : ∀ N (e : E), e ≠ 0 → ∃ j, N ≤ j ∧ σ j e ≠ 0)
    (N : ℕ) (x : T.tensor A E) (hx : x ≠ 0) :
    ∃ j, N ≤ j ∧ evaluation T A E (q j) (σ j) x ≠ 0 := by
  have hs : ∀ e : E, e ≠ 0 → ∃ k, σ (N + k) e ≠ 0 := by
    intro e he
    obtain ⟨j, hj, hd⟩ := hσ N e he
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact ⟨k, hd⟩
  obtain ⟨k, hk⟩ := F.separates A E (fun k => q (N+k)) (fun k => σ (N+k)) hs x hx
  exact ⟨N+k, Nat.le_add_right N k, hk⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual evaluation commutes with every nonunital scalar map, entry by entry. -/
theorem evaluation_naturality {A B E : Algebra.{u}} (q : ℕ)
    (σ : E →⋆ₐ[ℂ] matrixAlgebra.{u} q) (f : A →⋆ₙₐ[ℂ] B) :
    (evaluation T B E q σ).toNonUnitalStarAlgHom.comp
        (T.map f (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom) =
      (CStarMatrix.mapₙₐ f).comp (evaluation T A E q σ).toNonUnitalStarAlgHom := by
  apply T.hom_ext
  intro a e
  apply CStarMatrix.ext
  intro i j
  change evaluation T B E q σ (T.map f (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom (T.pure a e)) i j = f (evaluation T A E q σ (T.pure a e) i j)
  have hm : T.map f (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom (T.pure a e) = T.pure (f a) e := T.map_pure f (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom a e
  rw [hm, evaluation_pure, evaluation_pure, map_smul]

theorem matrix_map_injective {A B : Algebra.{u}} (q : ℕ)
    (f : A →⋆ₙₐ[ℂ] B) (hf : Function.Injective f) :
    Function.Injective (CStarMatrix.mapₙₐ (n := ULift.{u} (Fin q)) f) := by
  intro x y h
  apply CStarMatrix.ext
  intro i j
  exact hf (congrArg (fun z => z i j) h)

/-- The constant inclusion is faithful when the coefficient algebra is nonzero. -/
theorem constant_injective (A E : Algebra.{u}) [Nontrivial E] :
    Function.Injective (T.left A E) := by
  apply (injective_iff_map_eq_zero (T.left A E)).mpr
  intro a ha
  have h := T.norm_pure A E a 1
  rw [map_one, mul_one, ha, norm_zero, norm_one, mul_one] at h
  exact norm_eq_zero.mp h.symm

variable (A : ℕ → Algebra.{u}) (E : Algebra.{u}) (q : ℕ → ℕ)
variable (G : ∀ n, ScalarChannels (A n) (A (n+1)) (q n))
variable (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E)
variable (σ : ∀ n, E →⋆ₐ[ℂ] matrixAlgebra.{u} (q n))

def indexEquiv : Channel ≃ Fin (Fintype.card Channel) := Fintype.equivFin Channel

/-- The genuine three-channel system, reindexed only to the existing Fin API. -/
def channels : EvaluationLimitSimplicity.Channels.{u} where
  obj n := T.tensor (A n) E
  algebra _ := inferInstance
  count _ := Fintype.card Channel
  map n i := (G n).coefficient T ε η (σ n) (indexEquiv.symm i)
  orthogonal n i j h := (G n).coefficient_orthogonal T ε η (σ n) _ _
    (fun he => h (indexEquiv.symm.injective he))
  unit_sum n := by
    exact (indexEquiv.symm.sum_comp (fun c => (G n).coefficient T ε η (σ n) c 1)).trans ((G n).coefficient_unit_sum T ε η (σ n))

def positiveIndex (n : ℕ) : Fin ((channels T A E q G ε η σ).count n) :=
  indexEquiv .plus

def noiseIndex (n : ℕ) : Fin ((channels T A E q G ε η σ).count n) :=
  indexEquiv .noise

@[simp] theorem positive_channel (n : ℕ) :
    (channels T A E q G ε η σ).map n (positiveIndex T A E q G ε η σ n) =
      T.map (G n).plus (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom := by
  dsimp [channels, positiveIndex]
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem noise_channel (n : ℕ) :
    (channels T A E q G ε η σ).map n (noiseIndex T A E q G ε η σ n) =
      (T.left (A (n+1)) E).toNonUnitalStarAlgHom.comp
        ((G n).noise.comp (evaluation T (A n) E (q n) (σ n)).toNonUnitalStarAlgHom) := by
  dsimp [channels, noiseIndex]
  rw [Equiv.symm_apply_apply]
  rfl

/-- The Fin-indexed system uses exactly the previously proved coefficient sum. -/
theorem step_eq_phi (n : ℕ) :
    (channels T A E q G ε η σ).system.step n = (G n).phi T ε η (σ n) := by
  apply StarAlgHom.ext
  intro x
  change (∑ i, (G n).coefficient T ε η (σ n) (indexEquiv.symm i) x) = _
  exact indexEquiv.symm.sum_comp (fun c => (G n).coefficient T ε η (σ n) c x)

theorem step_injective : ∀ n,
    Function.Injective ((channels T A E q G ε η σ).system.step n) := by
  intro n
  rw [step_eq_phi]
  exact (G n).phi_injective T ε η (σ n)

instance stepFact : Fact (∀ n, Function.Injective ((channels T A E q G ε η σ).system.step n)) :=
  ⟨step_injective T A E q G ε η σ⟩

/-- Evaluate along the positive channel at a fixed, possibly later, representation. -/
theorem positive_evaluation (j n : ℕ)
    (a : (channels T A E q G ε η σ).obj n) :
    evaluation T (A (n+1)) E (q j) (σ j)
        ((channels T A E q G ε η σ).map n (positiveIndex T A E q G ε η σ n) a) =
      CStarMatrix.mapₙₐ (G n).plus (evaluation T (A n) E (q j) (σ j) a) := by
  rw [positive_channel]
  exact DFunLike.congr_fun (evaluation_naturality T (q j) (σ j) (G n).plus) a

/-- The witness is built from an actual later evaluation and the intervening
positive channels. Its noise and constant maps are the constructed maps. -/
def witnessAt (hnoise : ∀ n, Function.Injective (G n).noise)
    (hsimple : ∀ n, Target.IsSimple ⟨A n, inferInstance⟩)
    (m k : ℕ) (a : (channels T A E q G ε η σ).obj m)
    (ha : evaluation T (A m) E (q (m+k)) (σ (m+k)) a ≠ 0) :
    (channels T A E q G ε η σ).NoiseWitness
      (positiveIndex T A E q G ε η σ) m a :=
  EvaluationLimitSimplicity.Channels.NoiseWitness.ofEvaluatedPath
    (channels T A E q G ε η σ) (positiveIndex T A E q G ε η σ)
    (fun n => amplification (A n) (q (m+k)))
    (fun n => (evaluation T (A n) E (q (m+k)) (σ (m+k))).toNonUnitalStarAlgHom)
    (fun n => CStarMatrix.mapₙₐ (G n).plus)
    (fun n => matrix_map_injective (q (m+k)) (G n).plus (G n).plus_injective)
    (fun n x => positive_evaluation T A E q G ε η σ (m+k) n x)
    m k a ha (noiseIndex T A E q G ε η σ (m+k))
    ⟨A (m+k+1), inferInstance⟩ (hsimple (m+k+1))
    (G (m+k)).noise (hnoise (m+k)) (T.left (A (m+k+1)) E)
    (fun x => DFunLike.congr_fun (noise_channel T A E q G ε η σ (m+k)) x)

/-- Joint faithfulness and separating tails produce all actual noise witnesses. -/
theorem noise_witnesses (F : JointFaithfulnessInput T)
    (hσ : ∀ N (e : E), e ≠ 0 → ∃ j, N ≤ j ∧ σ j e ≠ 0)
    (hnoise : ∀ n, Function.Injective (G n).noise)
    (hsimple : ∀ n, Target.IsSimple ⟨A n, inferInstance⟩)
    (m : ℕ) (a : (channels T A E q G ε η σ).obj m) (ha : a ≠ 0) :
    Nonempty ((channels T A E q G ε η σ).NoiseWitness
      (positiveIndex T A E q G ε η σ) m a) := by
  obtain ⟨j, hj, hd⟩ := evaluation_tails T F (A m) E q σ hσ m a ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact ⟨witnessAt T A E q G ε η σ hnoise hsimple m k a hd⟩

/-- The same actual witnesses retain the infinite-projection and faithful
constant-inclusion data used in the analytic limit proof. -/
theorem pure_noise_witnesses [Nontrivial E] (F : JointFaithfulnessInput T)
    (hσ : ∀ N (e : E), e ≠ 0 → ∃ j, N ≤ j ∧ σ j e ≠ 0)
    (hnoise : ∀ n, Function.Injective (G n).noise)
    (hsimple : ∀ n, Target.IsSimple ⟨A n, inferInstance⟩)
    (hpure : ∀ n, Target.IsPurelyInfinite ⟨A n, inferInstance⟩)
    (m : ℕ) (a : (channels T A E q G ε η σ).obj m) (ha : a ≠ 0) :
    ∃ w : (channels T A E q G ε η σ).NoiseWitness
      (positiveIndex T A E q G ε η σ) m a,
      Target.IsPurelyInfinite w.K ∧ Function.Injective w.constant := by
  obtain ⟨j, hj, hd⟩ := evaluation_tails T F (A m) E q σ hσ m a ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  refine ⟨witnessAt T A E q G ε η σ hnoise hsimple m k a hd, hpure (m+k+1), ?_⟩
  exact constant_injective T (A (m+k+1)) E

/-- Kernel simplicity of the actual completed tensor system. -/
theorem limit_simple [Nontrivial E] [Nontrivial (A 0)]
    (F : JointFaithfulnessInput T)
    (hσ : ∀ N (e : E), e ≠ 0 → ∃ j, N ≤ j ∧ σ j e ≠ 0)
    (hnoise : ∀ n, Function.Injective (G n).noise)
    (hsimple : ∀ n, Target.IsSimple ⟨A n, inferInstance⟩)
    (quotients : EvaluationLimitSimplicity.ClosedIdealKernelRealization
      (SequentialCStarLimit.Limit (channels T A E q G ε η σ).system)) :
    Target.IsSimple ⟨SequentialCStarLimit.Limit (channels T A E q G ε η σ).system,
      inferInstance⟩ := by
  let : Nontrivial ((channels T A E q G ε η σ).obj 0) :=
    (constant_injective T (A 0) E).nontrivial
  exact EvaluationLimitSimplicity.Channels.limit_isSimple
    (channels T A E q G ε η σ) (positiveIndex T A E q G ε η σ)
    (noise_witnesses T A E q G ε η σ F hσ hnoise hsimple) quotients

/-- Pure infiniteness of the actual completed tensor system, with only generic
Cuntz-comparison theory left external to this analytic argument. -/
theorem limit_purelyInfinite [Nontrivial E]
    (I : EvaluationLimitPureInfiniteness.ComparisonInput.{u})
    (F : JointFaithfulnessInput T)
    (hσ : ∀ N (e : E), e ≠ 0 → ∃ j, N ≤ j ∧ σ j e ≠ 0)
    (hnoise : ∀ n, Function.Injective (G n).noise)
    (hsimple : ∀ n, Target.IsSimple ⟨A n, inferInstance⟩)
    (hpure : ∀ n, Target.IsPurelyInfinite ⟨A n, inferInstance⟩) :
    Target.IsPurelyInfinite ⟨SequentialCStarLimit.Limit (channels T A E q G ε η σ).system,
      inferInstance⟩ := by
  exact EvaluationLimitPureInfiniteness.Channels.limit_isPurelyInfinite
    (channels T A E q G ε η σ) I (positiveIndex T A E q G ε η σ)
    (fun m a _ ha => pure_noise_witnesses T A E q G ε η σ F hσ hnoise hsimple hpure m a ha)

end Suzuki.TensorEvaluationPaths

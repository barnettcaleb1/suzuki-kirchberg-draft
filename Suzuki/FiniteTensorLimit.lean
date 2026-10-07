import Suzuki.TensorEvaluationPaths

/-! Simplicity of the three finite constituent limits is proved by full noise
images. The finite constant algebra is not incorrectly assumed simple. The
full-image premise is local construction data, to be discharged by the actual
recursive positive multiplicities, not a published theorem input. -/
noncomputable section
namespace Suzuki.FiniteTensorLimit
open TensorCoefficientChannels TensorEvaluationPaths
open EvaluationLimitSimplicity SequentialCStarLimit
open scoped CStarAlgebra
universe u v
variable (T : Spatial.{u}) (A : ℕ → Algebra.{u}) (E : Algebra.{u}) (q : ℕ → ℕ)
variable (G : ∀ n, ScalarChannels (A n) (A (n+1)) (q n))
variable (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E)
variable (σ : ∀ n, E →⋆ₐ[ℂ] matrixAlgebra.{u} (q n))
variable (F : JointFaithfulnessInput T)
variable (hσ : ∀ N (e : E), e ≠ 0 → ∃ j, N ≤ j ∧ σ j e ≠ 0)
variable (hfull : ∀ n (x : amplification (A n) (q n)), x ≠ 0 →
  ∀ J : TwoSidedIdeal (A (n+1)), (G n).noise x ∈ J → J = ⊤)

include F hσ hfull

/-- A full constant noise image extracted from any nonzero stage element
forces the containing ideal to be the whole actual normed limit. -/
theorem stage_ideal_eq_top (m : ℕ) (a : (channels T A E q G ε η σ).obj m)
    (ha : a ≠ 0) (I : TwoSidedIdeal (Limit (channels T A E q G ε η σ).system))
    (hI : stage (channels T A E q G ε η σ).system m a ∈ I) : I = ⊤ := by
  let D := channels T A E q G ε η σ
  obtain ⟨j, hj, hd⟩ := evaluation_tails T F (A m) E q σ hσ m a ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hdet := D.evaluated_path_ne_zero (positiveIndex T A E q G ε η σ)
    (fun n => amplification (A n) (q (m+k)))
    (fun n => (evaluation T (A n) E (q (m+k)) (σ (m+k))).toNonUnitalStarAlgHom)
    (fun n => CStarMatrix.mapₙₐ (G n).plus)
    (fun n => matrix_map_injective (q (m+k)) (G n).plus (G n).plus_injective)
    (fun n x => positive_evaluation T A E q G ε η σ (m+k) n x) m k a hd
  let x := evaluation T (A (m+k)) E (q (m+k)) (σ (m+k))
    (D.path (positiveIndex T A E q G ε η σ) m k a)
  let c := (stage D.system (m+(k+1))).comp (T.left (A (m+k+1)) E)
  let J := I.comap c.toRingHom
  have hm := D.final_mem_ideal (positiveIndex T A E q G ε η σ) m k
    (noiseIndex T A E q G ε η σ (m+k)) a I hI
  have hmem : (G (m+k)).noise x ∈ J := by
    apply (TwoSidedIdeal.mem_comap c.toRingHom).mpr
    change stage D.system (m+(k+1)) (T.left (A (m+k+1)) E ((G (m+k)).noise x)) ∈ I
    rw [noise_channel T A E q G ε η σ] at hm
    exact hm
  have ht : J = ⊤ := hfull (m+k) x hdet J hmem
  have hone : (1 : A (m+k+1)) ∈ J := ht ▸ TwoSidedIdeal.mem_top _
  have hc : c 1 ∈ I := (TwoSidedIdeal.mem_comap c.toRingHom).mp hone
  exact I.eq_top (by simpa only [map_one] using hc)

/-- Actual maps out of the completed constituent limit are faithful whenever
the codomain is nonzero. -/
theorem hom_injective {B : Type v} [CStarAlgebra B] [Nontrivial B]
    (φ : Limit (channels T A E q G ε η σ).system →⋆ₐ[ℂ] B) : Function.Injective φ := by
  by_contra hf
  obtain ⟨m, a, ha, hz⟩ := exists_stage_kernel (channels T A E q G ε η σ).system φ hf
  let I : TwoSidedIdeal (Limit (channels T A E q G ε η σ).system) := TwoSidedIdeal.ker φ
  have ht := stage_ideal_eq_top T A E q G ε η σ F hσ hfull m a ha I
    ((TwoSidedIdeal.mem_ker φ).mpr hz)
  have hone : (1 : Limit (channels T A E q G ε η σ).system) ∈ I :=
    ht ▸ TwoSidedIdeal.mem_top _
  have hc := (TwoSidedIdeal.mem_ker φ).mp hone
  exact one_ne_zero (by simpa only [map_one] using hc)

/-- Closed-ideal simplicity of the actual finite-constituent limit. -/
theorem limit_simple [Nontrivial E] [Nontrivial (A 0)]
    (quotients : ClosedIdealKernelRealization (Limit (channels T A E q G ε η σ).system)) :
    Target.IsSimple ⟨Limit (channels T A E q G ε η σ).system, inferInstance⟩ := by
  let : Nontrivial ((channels T A E q G ε η σ).obj 0) :=
    (constant_injective T (A 0) E).nontrivial
  let : Nontrivial (Limit (channels T A E q G ε η σ).system) :=
    (stage_injective (channels T A E q G ε η σ).system 0).nontrivial
  exact isSimple_of_hom_injective quotients
    (fun B _ φ => hom_injective T A E q G ε η σ F hσ hfull φ)
end Suzuki.FiniteTensorLimit

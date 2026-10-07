import Suzuki.SequentialCStarLimit
import Suzuki.OrthogonalChannels
import Suzuki.Target
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Evaluation paths and normed sequential limits

Selected orthogonal channel paths are recovered by their actual support
projections. Injective evaluated identity channels preserve detection, and a
constant noise branch propagates ideal membership into a simple constant
algebra. The normed limit argument detects every nonzero kernel at a stage.
No closed-ideal quotient construction or final limit simplicity is assumed.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Suzuki.EvaluationLimitSimplicity

open InductiveAmalgam SequentialCStarLimit
open scoped CStarAlgebra

universe u v

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

/-- Compression identities compose, with the composite's actual unit as support. -/
theorem compose_compression (F : A →⋆ₐ[ℂ] B) (G : B →⋆ₐ[ℂ] C)
    (f : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] C)
    (hf : ∀ a, f 1 * F a = f a) (hg : ∀ b, g 1 * G b = g b) (a : A) :
    g (f 1) * G (F a) = g (f a) := by
  calc
    g (f 1) * G (F a) = (g (f 1) * g 1) * G (F a) := by rw [← map_mul, mul_one]
    _ = g (f 1) * (g 1 * G (F a)) := mul_assoc _ _ _
    _ = g (f 1) * g (F a) := by rw [hg]
    _ = g (f 1 * F a) := (map_mul g _ _).symm
    _ = g (f a) := by rw [hf]

/-- An orthogonal channel decomposition constructs its own unital connecting maps. -/
structure Channels where
  obj : ℕ → Type u
  algebra : ∀ n, CStarAlgebra (obj n)
  count : ℕ → ℕ
  map : ∀ n, Fin (count n) → obj n →⋆ₙₐ[ℂ] obj (n + 1)
  orthogonal : ∀ n i j, i ≠ j → map n i 1 * map n j 1 = 0
  unit_sum : ∀ n, ∑ i, map n i 1 = 1

attribute [instance] Channels.algebra

namespace Channels

variable (D : Channels.{u})

/-- The actual system formed by summing the supplied orthogonal channels. -/
abbrev system : System.{u} where
  obj := D.obj
  algebra := D.algebra
  step n := OrthogonalChannels.sumHom (D.map n) (D.orthogonal n) (D.unit_sum n)

@[simp] theorem step_apply (n : ℕ) (a : D.obj n) :
    D.system.step n a = ∑ i, D.map n i a := rfl

/-- One channel is recovered by multiplying by its support projection. -/
theorem channel_compression (n : ℕ) (i : Fin (D.count n)) (a : D.obj n) :
    D.map n i 1 * D.system.step n a = D.map n i a :=
  OrthogonalChannels.compression (D.map n) (D.orthogonal n) i a

/-- A faithful channel at every step proves injectivity of the constructed system. -/
theorem step_injective_of_channel (choose : ∀ n, Fin (D.count n))
    (h : ∀ n, Function.Injective (D.map n (choose n))) :
    ∀ n, Function.Injective (D.system.step n) := by
  intro n
  exact OrthogonalChannels.sumHom_injective (D.map n) (D.orthogonal n)
    (D.unit_sum n) (choose n) (h n)

/-- A chosen channel at each level defines the genuine composite path map. -/
def path (choose : ∀ n, Fin (D.count n)) (m k : ℕ) :
    D.obj m →⋆ₙₐ[ℂ] D.obj (m + k) :=
  Nat.rec (motive := fun k => D.obj m →⋆ₙₐ[ℂ] D.obj (m + k))
    (NonUnitalStarAlgHom.id ℂ (D.obj m))
    (fun k f => (D.map (m + k) (choose (m + k))).comp f) k

@[simp] theorem path_zero (choose : ∀ n, Fin (D.count n)) (m : ℕ) (a : D.obj m) :
    D.path choose m 0 a = a := rfl

@[simp] theorem path_succ (choose : ∀ n, Fin (D.count n)) (m k : ℕ) (a : D.obj m) :
    D.path choose m (k + 1) a = D.map (m + k) (choose (m + k)) (D.path choose m k a) := rfl

/-- The concrete transition map has the expected successor formula. -/
theorem transition_succ_apply (m k : ℕ) (a : D.obj m) :
    transition D.system m (m + (k + 1)) (Nat.le_add_right m (k + 1)) a =
      D.system.step (m + k) (transition D.system m (m + k) (Nat.le_add_right m k) a) := by
  rw [transition, Nat.leRecOn_succ (Nat.le_add_right m k)]
  rfl

/-- Compression by a path's actual unit recovers that entire iterated path. -/
theorem path_compression (choose : ∀ n, Fin (D.count n)) (m k : ℕ) (a : D.obj m) :
    D.path choose m k 1 * transition D.system m (m + k) (Nat.le_add_right m k) a =
      D.path choose m k a := by
  induction k generalizing a with
  | zero => simp [path]
  | succ k ih =>
    rw [path_succ, path_succ, transition_succ_apply]
    exact compose_compression
      (transition D.system m (m + k) (Nat.le_add_right m k)) (D.system.step (m + k))
      (D.path choose m k) (D.map (m + k) (choose (m + k)))
      ih (D.channel_compression _ _) a

/-- A final, independently selected noise channel is isolated after any path. -/
theorem final_compression (choose : ∀ n, Fin (D.count n)) (m k : ℕ)
    (i : Fin (D.count (m + k))) (a : D.obj m) :
    D.map (m + k) i (D.path choose m k 1) *
        transition D.system m (m + (k + 1)) (Nat.le_add_right m (k + 1)) a =
      D.map (m + k) i (D.path choose m k a) := by
  rw [transition_succ_apply]
  exact compose_compression
    (transition D.system m (m + k) (Nat.le_add_right m k)) (D.system.step (m + k))
    (D.path choose m k) (D.map (m + k) i)
    (D.path_compression choose m k) (D.channel_compression _ _) a

/-- All path support elements are actual self-adjoint projections. -/
theorem path_support_projection (choose : ∀ n, Fin (D.count n)) (m k : ℕ) :
    IsStarProjection (D.path choose m k 1) := by
  constructor
  · change D.path choose m k 1 * D.path choose m k 1 = D.path choose m k 1
    rw [← map_mul, one_mul]
  · change star (D.path choose m k 1) = D.path choose m k 1
    rw [← map_star, star_one]

/-- Preservation of a concrete constant subalgebra keeps every path support constant. -/
theorem path_support_constant (choose : ∀ n, Fin (D.count n))
    (K : ∀ n, StarSubalgebra ℂ (D.obj n))
    (preserves : ∀ n i a, a ∈ K n → D.map n i a ∈ K (n + 1)) (m k : ℕ) :
    D.path choose m k 1 ∈ K (m + k) := by
  induction k with
  | zero => exact (K m).one_mem
  | succ k ih => exact preserves (m + k) (choose (m + k)) _ ih

/-- Evaluation along an identity path stays nonzero through actual injective maps. -/
theorem evaluated_path_ne_zero (choose : ∀ n, Fin (D.count n))
    (E : ℕ → Type v) [∀ n, CStarAlgebra (E n)]
    (eval : ∀ n, D.obj n →⋆ₙₐ[ℂ] E n)
    (next : ∀ n, E n →⋆ₙₐ[ℂ] E (n + 1))
    (hinj : ∀ n, Function.Injective (next n))
    (commutes : ∀ n a, eval (n + 1) (D.map n (choose n) a) = next n (eval n a))
    (m k : ℕ) (a : D.obj m) (ha : eval m a ≠ 0) :
    eval (m + k) (D.path choose m k a) ≠ 0 := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    rw [path_succ]
    change eval ((m + k) + 1) (D.map (m + k) (choose (m + k)) (D.path choose m k a)) ≠ 0
    rw [commutes]
    intro hz
    exact ih ((hinj (m + k)) (hz.trans (map_zero (next (m + k))).symm))

variable [Fact (∀ n, Function.Injective (D.system.step n))]

/-- Compressing inside the actual limit propagates membership in any two-sided ideal. -/
theorem final_mem_ideal (choose : ∀ n, Fin (D.count n)) (m k : ℕ)
    (i : Fin (D.count (m + k))) (a : D.obj m)
    (I : TwoSidedIdeal (Limit D.system)) (ha : stage D.system m a ∈ I) :
    stage D.system (m + (k + 1)) (D.map (m + k) i (D.path choose m k a)) ∈ I := by
  rw [← D.final_compression choose m k i a, map_mul]
  have hc := compatible_transition D.system (stage D.system) (stage_commutes D.system)
    m (m + (k + 1)) (Nat.le_add_right m (k + 1)) a
  rw [hc]
  exact I.mul_mem_left _ _ ha

/-- A constant noise branch gives a nonzero element of the constant algebra
whose limit image belongs to the ideal. No injectivity of the constant inclusion
is needed for this statement or for the subsequent simple-algebra argument. -/
theorem extract_constant (choose : ∀ n, Fin (D.count n)) (m k : ℕ)
    (i : Fin (D.count (m + k))) {E K : Type*} [CStarAlgebra E] [CStarAlgebra K]
    (eval : D.obj (m + k) →⋆ₙₐ[ℂ] E) (noise : E →⋆ₙₐ[ℂ] K)
    (hn : Function.Injective noise) (constant : K →⋆ₐ[ℂ] D.obj (m + (k + 1)))
    (factor : ∀ x, D.map (m + k) i x = constant (noise (eval x)))
    (a : D.obj m) (ha : eval (D.path choose m k a) ≠ 0)
    (I : TwoSidedIdeal (Limit D.system)) (hI : stage D.system m a ∈ I) :
    ∃ d : K, d ≠ 0 ∧ stage D.system (m + (k + 1)) (constant d) ∈ I := by
  refine ⟨noise (eval (D.path choose m k a)), ?_, ?_⟩
  · intro hz
    exact ha (hn (hz.trans (map_zero noise).symm))
  · rw [← factor]
    exact D.final_mem_ideal choose m k i a I hI

end Channels

/-- A nonzero element from a simple unital constant algebra forces the whole ideal. -/
theorem ideal_eq_top_of_simple_constant {K B : Type*} [CStarAlgebra K] [CStarAlgebra B]
    (simple : ∀ J : TwoSidedIdeal K, IsClosed (J : Set K) → J = ⊥ ∨ J = ⊤)
    (j : K →⋆ₐ[ℂ] B) (I : TwoSidedIdeal B) (hI : IsClosed (I : Set B))
    (d : K) (hd : d ≠ 0) (hmem : j d ∈ I) : I = ⊤ := by
  let J : TwoSidedIdeal K := I.comap j.toRingHom
  have hJ : IsClosed (J : Set K) := by
    have hs : (J : Set K) = j ⁻¹' (I : Set B) := by
      ext x
      exact TwoSidedIdeal.mem_comap j.toRingHom
    rw [hs]
    exact hI.preimage (map_continuous j)
  rcases simple J hJ with hbot | htop
  · have hm : d ∈ J := (TwoSidedIdeal.mem_comap j.toRingHom).mpr hmem
    rw [hbot, TwoSidedIdeal.mem_bot] at hm
    exact False.elim (hd hm)
  · apply I.eq_top
    have hm : (1 : K) ∈ J := htop ▸ TwoSidedIdeal.mem_top K
    have hm' : j 1 ∈ I := (TwoSidedIdeal.mem_comap j.toRingHom).mp hm
    simpa only [map_one] using hm'

section NormedLimit

variable (S : System.{u}) [Fact (∀ n, Function.Injective (S.step n))]
variable {B : Type v} [CStarAlgebra B]

/-- Isometry on all stages implies isometry on the actual completed limit. -/
theorem isometry_of_stage_injective (φ : Limit S →⋆ₐ[ℂ] B)
    (hφ : ∀ n, Function.Injective (φ.comp (stage S n))) : Isometry φ := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (map_continuous φ)) continuous_norm
  | ih a =>
    obtain ⟨n, b, rfl⟩ := DirectLimit.exists_eq_mk (transition S) a
    change ‖φ (stage S n b)‖ = ‖stage S n b‖
    rw [norm_stage]
    exact NonUnitalStarAlgHom.norm_map (φ.comp (stage S n)) (hφ n) b

/-- Any noninjective actual star homomorphism has a nonzero kernel element already at a stage. -/
theorem exists_stage_kernel (φ : Limit S →⋆ₐ[ℂ] B) (hφ : ¬ Function.Injective φ) :
    ∃ n, ∃ a : S.obj n, a ≠ 0 ∧ φ (stage S n a) = 0 := by
  by_contra h
  apply hφ
  apply (isometry_of_stage_injective S φ ?_).injective
  intro n
  apply (injective_iff_map_eq_zero (φ.comp (stage S n))).mpr
  intro a ha
  by_contra hne
  exact h ⟨n, a, hne, ha⟩

end NormedLimit

namespace Channels

variable (D : Channels.{u})

/-- Concrete finite evaluation data. The final channel factors through evaluation
and an injective map into a simple constant algebra; no ideal fullness conclusion
is included. `detects` can be obtained from `evaluated_path_ne_zero`. -/
structure NoiseWitness (choose : ∀ n, Fin (D.count n)) (m : ℕ) (a : D.obj m) where
  length : ℕ
  index : Fin (D.count (m + length))
  Eval : Type u
  evalAlgebra : CStarAlgebra Eval
  K : Target.UnitalAlgebra.{u}
  simple : Target.IsSimple K
  evaluation : D.obj (m + length) →⋆ₙₐ[ℂ] Eval
  noise : Eval →⋆ₙₐ[ℂ] K
  noise_injective : Function.Injective noise
  constant : K →⋆ₐ[ℂ] D.obj (m + (length + 1))
  factor : ∀ x, D.map (m + length) index x = constant (noise (evaluation x))
  detects : evaluation (D.path choose m length a) ≠ 0

attribute [instance] NoiseWitness.evalAlgebra

/-- Initial evaluation detection and commuting injective identity maps supply
the detection field, including arbitrarily many intervening identity channels. -/
def NoiseWitness.ofEvaluatedPath (choose : ∀ n, Fin (D.count n))
    (E : ℕ → Type u) [∀ n, CStarAlgebra (E n)]
    (eval : ∀ n, D.obj n →⋆ₙₐ[ℂ] E n)
    (next : ∀ n, E n →⋆ₙₐ[ℂ] E (n + 1))
    (hinj : ∀ n, Function.Injective (next n))
    (commutes : ∀ n a, eval (n + 1) (D.map n (choose n) a) = next n (eval n a))
    (m k : ℕ) (a : D.obj m) (ha : eval m a ≠ 0)
    (i : Fin (D.count (m + k))) (K : Target.UnitalAlgebra.{u}) (hK : Target.IsSimple K)
    (noise : E (m + k) →⋆ₙₐ[ℂ] K) (hn : Function.Injective noise)
    (constant : K →⋆ₐ[ℂ] D.obj (m + (k + 1)))
    (factor : ∀ x, D.map (m + k) i x = constant (noise (eval (m + k) x))) :
    D.NoiseWitness choose m a where
  length := k
  index := i
  Eval := E (m + k)
  evalAlgebra := inferInstance
  K := K
  simple := hK
  evaluation := eval (m + k)
  noise := noise
  noise_injective := hn
  constant := constant
  factor := factor
  detects := D.evaluated_path_ne_zero choose E eval next hinj commutes m k a ha

variable [Fact (∀ n, Function.Injective (D.system.step n))]

/-- The explicit noise witness forces a containing closed ideal to be all of the limit. -/
theorem ideal_eq_top_of_witness (choose : ∀ n, Fin (D.count n)) (m : ℕ) (a : D.obj m)
    (w : D.NoiseWitness choose m a) (I : TwoSidedIdeal (Limit D.system))
    (hI : IsClosed (I : Set (Limit D.system))) (ha : stage D.system m a ∈ I) : I = ⊤ := by
  obtain ⟨d, hd, hm⟩ := D.extract_constant choose m w.length w.index
    w.evaluation w.noise w.noise_injective w.constant w.factor a w.detects I ha
  exact ideal_eq_top_of_simple_constant w.simple.2
    ((stage D.system (m + (w.length + 1))).comp w.constant) I hI d hd hm

/-- Finite evaluation witnesses imply every unital map to a nonzero C*-algebra
is injective. The passage from stages to the completed limit is proved by norms. -/
theorem hom_injective_of_noise_witnesses (choose : ∀ n, Fin (D.count n))
    (detect : ∀ m (a : D.obj m), a ≠ 0 → Nonempty (D.NoiseWitness choose m a))
    {B : Type v} [CStarAlgebra B] [Nontrivial B]
    (φ : Limit D.system →⋆ₐ[ℂ] B) : Function.Injective φ := by
  by_contra hf
  obtain ⟨m, a, ha, hz⟩ := exists_stage_kernel D.system φ hf
  obtain ⟨w⟩ := detect m a ha
  let I : TwoSidedIdeal (Limit D.system) := TwoSidedIdeal.ker φ
  have hI : IsClosed (I : Set (Limit D.system)) := by
    have hs : (I : Set (Limit D.system)) = φ ⁻¹' {0} := by
      ext x
      exact TwoSidedIdeal.mem_ker φ
    rw [hs]
    exact isClosed_singleton.preimage (map_continuous φ)
  have ht : I = ⊤ := D.ideal_eq_top_of_witness choose m a w I hI
    ((TwoSidedIdeal.mem_ker φ).mpr hz)
  have hm : (1 : Limit D.system) ∈ I := ht ▸ TwoSidedIdeal.mem_top _
  have hc : φ 1 = 0 := (TwoSidedIdeal.mem_ker φ).mp hm
  exact one_ne_zero (by simpa only [map_one] using hc)

end Channels

/-- Explicit remaining foundational obligation: every proper closed two-sided
ideal is the kernel of a unital map into a nonzero C*-algebra. This file does
not prove it, assert it globally, or license it as a published input. -/
def ClosedIdealKernelRealization (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I ≠ ⊤ →
    ∃ B : Target.UnitalAlgebra.{u}, Nontrivial B ∧
      ∃ φ : A →⋆ₐ[ℂ] B, I = TwoSidedIdeal.ker φ

/-- Conversion to exactly the target's closed-ideal simplicity predicate, with
the missing general quotient construction exposed as a separate hypothesis. -/
theorem isSimple_of_hom_injective {A : Type u} [CStarAlgebra A] [Nontrivial A]
    (quotients : ClosedIdealKernelRealization A)
    (faithful : ∀ (B : Target.UnitalAlgebra.{u}) [Nontrivial B]
      (φ : A →⋆ₐ[ℂ] B), Function.Injective φ) :
    Target.IsSimple ⟨A, inferInstance⟩ := by
  refine ⟨inferInstance, ?_⟩
  intro I hI
  by_cases ht : I = ⊤
  · exact Or.inr ht
  · obtain ⟨B, hB, φ, hφ⟩ := quotients I hI ht
    let : Nontrivial B := hB
    exact Or.inl (hφ.trans ((TwoSidedIdeal.ker_eq_bot φ).mpr (faithful B φ)))

/-- End-to-end conditional simplicity of the constructed normed limit. The
remaining inputs are concrete finite noise data and the separately identified
closed-ideal quotient foundation; limit simplicity itself is never an input. -/
theorem Channels.limit_isSimple (D : Channels.{u})
    [Fact (∀ n, Function.Injective (D.system.step n))] [Nontrivial (D.obj 0)]
    (choose : ∀ n, Fin (D.count n))
    (detect : ∀ m (a : D.obj m), a ≠ 0 → Nonempty (D.NoiseWitness choose m a))
    (quotients : ClosedIdealKernelRealization (Limit D.system)) :
    Target.IsSimple ⟨Limit D.system, inferInstance⟩ := by
  let : Nontrivial (Limit D.system) := (stage_injective D.system 0).nontrivial
  exact isSimple_of_hom_injective quotients
    (fun B _ φ => D.hom_injective_of_noise_witnesses choose detect φ)

end Suzuki.EvaluationLimitSimplicity

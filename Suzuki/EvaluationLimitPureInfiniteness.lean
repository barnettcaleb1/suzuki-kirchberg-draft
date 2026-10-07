import Suzuki.EvaluationLimitSimplicity
import Suzuki.CornerPureInfiniteness
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
# Pure infiniteness from actual evaluation channels

The only analytic inputs below are generic cut-down and Cuntz-comparison
facts. They are explicit parameters, not global axioms. The application to
the constructed limit, its chosen paths, and its noise supports is proved.
The existence of the manuscript's recursive noise witnesses is still a local
construction obligation; it is not part of the published input interface.
-/

set_option maxHeartbeats 200000
noncomputable section
namespace Suzuki.EvaluationLimitPureInfiniteness
open InductiveAmalgam SequentialCStarLimit EvaluationLimitSimplicity
open scoped CStarAlgebra ComplexOrder
universe u

/-- Unstabilized Cuntz subequivalence, with its actual norm convention. -/
def Subequivalent (A : Target.UnitalAlgebra.{u}) (a b : A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x : A, ‖star x * b * x - a‖ < ε

/-- The actual positive cut defined by continuous functional calculus. -/
def cut (A : Target.UnitalAlgebra.{u}) (a : A) (ε : ℝ) : A :=
  (a - ε • (1 : A))⁺

/-- Standard supporting facts, independent of the manuscript's systems.
Source correspondence is recorded in the accompanying comparison-input ledger.
No simplicity, pure infiniteness, graph, channel, or limit conclusion is a field.
-/
structure ComparisonInput : Prop where
  cut_nonzero : ∀ (A : Target.UnitalAlgebra.{u}) (a : A) (ε : ℝ),
    0 ≤ a → 0 < ε → ε < ‖a‖ → cut A a ε ≠ 0
  cut_map : ∀ (A B : Target.UnitalAlgebra.{u}) (φ : A →⋆ₐ[ℂ] B)
    (a : A) (ε : ℝ), 0 ≤ a → φ (cut A a ε) = cut B (φ a) ε
  cut_compare : ∀ (A : Target.UnitalAlgebra.{u}) (a b : A) (ε : ℝ),
    0 ≤ a → 0 ≤ b → 0 < ε → ‖a - b‖ < ε → Subequivalent A (cut A a ε) b
  trans : ∀ (A : Target.UnitalAlgebra.{u}) (a b c : A),
    0 ≤ a → 0 ≤ b → 0 ≤ c → Subequivalent A a b → Subequivalent A b c → Subequivalent A a c
  hereditary_compare : ∀ (A : Target.UnitalAlgebra.{u}) (a b : A),
    0 ≤ a → 0 ≤ b → a ∈ Target.hereditarySet A b → Subequivalent A a b
  projection_transfer : ∀ (A : Target.UnitalAlgebra.{u}) (p b : A),
    IsStarProjection p → 0 ≤ b → Subequivalent A p b →
      ∃ w : A, star w * w = p ∧
        IsStarProjection (w * star w) ∧ w * star w ∈ Target.hereditarySet A b
  infinite_equivalent : ∀ (A : Target.UnitalAlgebra.{u}) (p w : A),
    Target.IsInfiniteProjection A p → star w * w = p →
      Target.IsInfiniteProjection A (w * star w)

theorem cut_nonneg (A : Target.UnitalAlgebra.{u}) (a : A) (ε : ℝ) :
    0 ≤ cut A a ε := CFC.posPart_nonneg _

/-- An exact sandwich is already a witness at every error tolerance. -/
theorem subequivalent_of_sandwich (A : Target.UnitalAlgebra.{u}) (a b x : A)
    (h : star x * b * x = a) : Subequivalent A a b := by
  intro ε hε
  exact ⟨x, by simpa only [h, sub_self, norm_zero] using hε⟩

/-- Hereditary membership is preserved by the actual continuous star map. -/
theorem map_mem_hereditary (A B : Target.UnitalAlgebra.{u})
    (φ : A →⋆ₐ[ℂ] B) (a p : A) (h : p ∈ Target.hereditarySet A a) :
    φ p ∈ Target.hereditarySet B (φ a) := by
  have hm : Set.MapsTo φ (Set.range fun x : A => a * x * a)
      (Set.range fun x : B => φ a * x * φ a) := by
    rintro x ⟨y, rfl⟩
    exact ⟨φ y, by simp only [map_mul]⟩
  exact hm.closure (map_continuous φ) h

/-- Faithful maps preserve the proper-isometry witness, including its defect. -/
theorem map_infinite (A B : Target.UnitalAlgebra.{u})
    (φ : A →⋆ₐ[ℂ] B) (hi : Function.Injective φ) (p : A)
    (hp : Target.IsInfiniteProjection A p) : Target.IsInfiniteProjection B (φ p) := by
  rcases hp with ⟨hp, v, hv, hvp, hle, hne⟩
  refine ⟨?_, φ v, ?_, ?_, ?_, ?_⟩
  · exact hp.map φ
  · simpa only [map_mul, map_star] using congrArg φ hv
  · simpa only [map_mul, map_star] using hvp.map φ
  · have h := map_nonneg φ (sub_nonneg.mpr hle)
    rw [map_sub, map_mul, map_star] at h
    exact sub_nonneg.mp h
  · intro h
    exact hne (hi (by simpa only [map_mul, map_star] using h))

local instance stageOrder (S : System.{u}) (n : ℕ) : PartialOrder (S.obj n) :=
  CStarAlgebra.spectralOrder _
local instance stageOrderedRing (S : System.{u}) (n : ℕ) : StarOrderedRing (S.obj n) :=
  CStarAlgebra.spectralOrderedRing _
local instance limitOrder (S : System.{u}) [Fact (∀ n, Function.Injective (S.step n))] :
    PartialOrder (Limit S) := CStarAlgebra.spectralOrder _
local instance limitOrderedRing (S : System.{u}) [Fact (∀ n, Function.Injective (S.step n))] :
    StarOrderedRing (Limit S) := CStarAlgebra.spectralOrderedRing _

/-- Positivity of stage approximants is obtained from square roots and density,
not assumed as an extra property of the inductive system. -/
theorem positive_stage_approx (S : System.{u})
    [Fact (∀ n, Function.Injective (S.step n))]
    (b : Limit S) (hb : 0 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ m, ∃ a : S.obj m, 0 ≤ a ∧ ‖stage S m a - b‖ < ε := by
  let U : Set (Limit S) := {x | ‖star x * x - b‖ < ε}
  have ho : IsOpen U := isOpen_lt
    (((continuous_star.mul continuous_id).sub continuous_const).norm) continuous_const
  have hn : U.Nonempty := by
    refine ⟨CFC.sqrt b, ?_⟩
    change ‖star (CFC.sqrt b) * CFC.sqrt b - b‖ < ε
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq,
      CFC.sqrt_mul_sqrt_self b hb, sub_self, norm_zero]
    exact hε
  obtain ⟨y, hy, hU⟩ := (dense_stage_union S).exists_mem_open ho hn
  rcases Set.mem_iUnion.mp hy with ⟨m, x, rfl⟩
  refine ⟨m, star x * x, star_mul_self_nonneg x, ?_⟩
  simpa only [U, Set.mem_ofPred_eq, map_mul, map_star] using hU

/-- A nonzero positive limit element dominates a nonzero positive stage cut. -/
theorem nonzero_stage_cut (I : ComparisonInput.{u}) (S : System.{u})
    [Fact (∀ n, Function.Injective (S.step n))]
    (b : Limit S) (hb : 0 ≤ b) (hne : b ≠ 0) :
    ∃ m, ∃ c : S.obj m, 0 ≤ c ∧ c ≠ 0 ∧
      Subequivalent ⟨Limit S, inferInstance⟩ (stage S m c) b := by
  have hnorm : 0 < ‖b‖ := norm_pos_iff.mpr hne
  obtain ⟨m, a, ha, hab⟩ := positive_stage_approx S b hb (‖b‖ / 4) (by positivity)
  have hsize : ‖b‖ / 2 < ‖a‖ := by
    have htri := norm_le_norm_add_norm_sub (stage S m a) b
    rw [norm_stage] at htri
    linarith
  refine ⟨m, cut ⟨S.obj m, inferInstance⟩ a (‖b‖ / 2), cut_nonneg _ _ _,
    I.cut_nonzero _ _ _ ha (by positivity) hsize, ?_⟩
  rw [I.cut_map ⟨S.obj m, inferInstance⟩ ⟨Limit S, inferInstance⟩ (stage S m) a (‖b‖ / 2) ha]
  exact I.cut_compare _ _ _ _ (map_nonneg (stage S m) ha) hb (by positivity) (by linarith)

namespace Channels
variable (D : EvaluationLimitSimplicity.Channels.{u})
variable [Fact (∀ n, Function.Injective (D.system.step n))]
local instance channelLimitOrder : PartialOrder (Limit D.system) := CStarAlgebra.spectralOrder _
local instance channelLimitOrderedRing : StarOrderedRing (Limit D.system) := CStarAlgebra.spectralOrderedRing _
local instance channelOrder (n : ℕ) : PartialOrder (D.obj n) := CStarAlgebra.spectralOrder _
local instance channelOrderedRing (n : ℕ) : StarOrderedRing (D.obj n) := CStarAlgebra.spectralOrderedRing _

/-- The selected path followed by the noise channel is an actual sandwich of
the original stage element in the limit. -/
theorem noise_sandwich (choose : ∀ n, Fin (D.count n)) (m : ℕ) (a : D.obj m)
    (w : D.NoiseWitness choose m a) :
    ∃ r : Limit D.system,
      star r * stage D.system m a * r =
        stage D.system (m + (w.length + 1))
          (w.constant (w.noise (w.evaluation (D.path choose m w.length a)))) := by
  let f := (D.map (m + w.length) w.index).comp (D.path choose m w.length)
  let j := stage D.system (m + (w.length + 1))
  have hs : star (f 1) = f 1 := by rw [← map_star, star_one]
  have hc := D.final_compression choose m w.length w.index a
  have ht := compatible_transition D.system (stage D.system) (stage_commutes D.system)
    m (m + (w.length + 1)) (Nat.le_add_right m (w.length + 1)) a
  refine ⟨j (f 1), ?_⟩
  rw [← map_star, hs, ← ht, ← map_mul, ← map_mul]
  change j ((f 1 * transition D.system m (m + (w.length + 1))
    (Nat.le_add_right m (w.length + 1)) a) * f 1) = _
  change f 1 *
    transition D.system m (m + (w.length + 1))
      (Nat.le_add_right m (w.length + 1)) a = f a at hc
  rw [hc, ← map_mul, mul_one]
  exact congrArg j (w.factor (D.path choose m w.length a))

/-- A purely infinite constant algebra in a faithful noise branch supplies an
infinite projection below the source element in actual Cuntz comparison. -/
theorem infinite_below_stage (I : ComparisonInput.{u})
    (choose : ∀ n, Fin (D.count n)) (m : ℕ) (a : D.obj m) (ha : 0 ≤ a)
    (w : D.NoiseWitness choose m a) (hK : Target.IsPurelyInfinite w.K)
    (hconst : Function.Injective w.constant) :
    ∃ p : Limit D.system, Target.IsInfiniteProjection ⟨Limit D.system, inferInstance⟩ p ∧
      Subequivalent ⟨Limit D.system, inferInstance⟩ p (stage D.system m a) := by
  let : PartialOrder w.Eval := CStarAlgebra.spectralOrder _
  let : StarOrderedRing w.Eval := CStarAlgebra.spectralOrderedRing _
  let d := w.noise (w.evaluation (D.path choose m w.length a))
  have hd : 0 ≤ d := map_nonneg w.noise
    (map_nonneg w.evaluation (map_nonneg (D.path choose m w.length) ha))
  have hdne : d ≠ 0 := by
    intro h
    exact w.detects (w.noise_injective (h.trans (map_zero w.noise).symm))
  obtain ⟨p, hpHer, hpInf⟩ := hK d hd hdne
  let j := (stage D.system (m + (w.length + 1))).comp w.constant
  have hj : Function.Injective j :=
    (stage_injective D.system (m + (w.length + 1))).comp hconst
  obtain ⟨r, hr⟩ := noise_sandwich D choose m a w
  refine ⟨j p, map_infinite w.K ⟨Limit D.system, inferInstance⟩ j hj p hpInf, ?_⟩
  apply I.trans ⟨Limit D.system, inferInstance⟩ (j p) (j d) (stage D.system m a)
    (map_nonneg j hpInf.1.nonneg) (map_nonneg j hd) (map_nonneg (stage D.system m) ha)
  · exact I.hereditary_compare ⟨Limit D.system, inferInstance⟩ (j p) (j d) (map_nonneg j hpInf.1.nonneg) (map_nonneg j hd)
      (map_mem_hereditary w.K ⟨Limit D.system, inferInstance⟩ j d p hpHer)
  · exact subequivalent_of_sandwich ⟨Limit D.system, inferInstance⟩ (j d) (stage D.system m a) r hr

/-- Pure infiniteness of the actual completed limit is derived from its
noise witnesses and the generic comparison inputs. In particular no tensor
stage is assumed purely infinite. -/
theorem limit_isPurelyInfinite (I : ComparisonInput.{u})
    (choose : ∀ n, Fin (D.count n))
    (detect : ∀ m (a : D.obj m), 0 ≤ a → a ≠ 0 →
      ∃ w : D.NoiseWitness choose m a,
        Target.IsPurelyInfinite w.K ∧ Function.Injective w.constant) :
    Target.IsPurelyInfinite ⟨Limit D.system, inferInstance⟩ := by
  intro b hb hne
  obtain ⟨m, c, hc, hcne, hcb⟩ := nonzero_stage_cut I D.system b hb hne
  obtain ⟨w, hK, hconst⟩ := detect m c hc hcne
  obtain ⟨p, hpInf, hpc⟩ := infinite_below_stage D I choose m c hc w hK hconst
  have hpb := I.trans ⟨Limit D.system, inferInstance⟩ p (stage D.system m c) b
    hpInf.1.nonneg (map_nonneg (stage D.system m) hc) hb hpc hcb
  obtain ⟨v, hv, _, hher⟩ := I.projection_transfer ⟨Limit D.system, inferInstance⟩ p b hpInf.1 hb hpb
  exact ⟨v * star v, hher, I.infinite_equivalent ⟨Limit D.system, inferInstance⟩ p v hpInf hv⟩

end Channels
end Suzuki.EvaluationLimitPureInfiniteness

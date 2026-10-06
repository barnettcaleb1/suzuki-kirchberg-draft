import Suzuki.LimitCPMaps

/-!
# CP approximation for split injective sequential limits

The limit is the actual norm-completed C⋆-algebra constructed in
`SequentialCStarLimit`. The additional hypothesis consists of genuine completely
positive contractive left inverses of the connecting star homomorphisms.
Coherent stage retractions and their extensions are constructed, and their
approximation properties are proved from stage density. No limit CPAP,
convergence, or nuclearity statement is assumed. Existence of these splittings
for the manuscript's diagrams remains a separate obligation.
-/

noncomputable section

namespace Suzuki.CPApproximationLimits

open InductiveAmalgam SequentialCStarLimit FiniteCPApproximation
open scoped CStarAlgebra ComplexOrder

universe u

variable (S : System.{u})

local instance stageOrder (n : ℕ) : PartialOrder (S.obj n) := CStarAlgebra.spectralOrder _
local instance stageOrderedRing (n : ℕ) : StarOrderedRing (S.obj n) :=
  CStarAlgebra.spectralOrderedRing _

/-- Actual CP contractive left inverses for the adjacent connecting maps. -/
structure CPCSplitting where
  retract : ∀ n, S.obj (n + 1) →CP S.obj n
  contractive : ∀ n a, ‖retract n a‖ ≤ ‖a‖
  leftInverse : ∀ n a, retract n (S.step n a) = a

namespace CPCSplitting

variable {S} (R : CPCSplitting S)

include R in
/-- Such actual splittings force the connecting maps to be injective. -/
theorem step_injective (n : ℕ) : Function.Injective (S.step n) :=
  Function.LeftInverse.injective (R.leftInverse n)

/-- Retraction to a fixed stage: forward transition below that stage, and
successive CP left inverses above it. -/
def stageMap (k : ℕ) : ∀ m, S.obj m →CP S.obj k
  | 0 => homCP (transition S 0 k (Nat.zero_le k))
  | m + 1 => if h : m + 1 ≤ k then homCP (transition S (m + 1) k h)
      else cpComp (stageMap k m) (R.retract m)

theorem stageMap_of_le (k m : ℕ) (h : m ≤ k) :
    R.stageMap k m = homCP (transition S m k h) := by
  cases m with
  | zero => rfl
  | succ m => simp only [stageMap, dif_pos h]

theorem stageMap_contractive (k m : ℕ) (a : S.obj m) :
    ‖R.stageMap k m a‖ ≤ ‖a‖ := by
  induction m with
  | zero => exact NonUnitalStarAlgHom.norm_apply_le (transition S 0 k (Nat.zero_le k)) a
  | succ m ih =>
    simp only [stageMap]
    split_ifs with h
    · exact NonUnitalStarAlgHom.norm_apply_le (transition S (m + 1) k h) a
    · exact (ih (R.retract m a)).trans (R.contractive m a)

theorem stageMap_step (k m : ℕ) (a : S.obj m) :
    R.stageMap k (m + 1) (S.step m a) = R.stageMap k m a := by
  by_cases h : m + 1 ≤ k
  · rw [stageMap_of_le R k (m + 1) h,
      stageMap_of_le R k m ((Nat.le_succ m).trans h)]
    simpa only [homCP_apply, transition_succ] using
      DirectedSystem.map_map' (transition S) (Nat.le_succ m) h a
  · simp only [stageMap, dif_neg h, cpComp_apply, R.leftInverse]

/-- Compatibility holds for every finite transition, not only adjacent stages. -/
theorem stageMap_transition (k m n : ℕ) (h : m ≤ n) (a : S.obj m) :
    R.stageMap k n (transition S m n h a) = R.stageMap k m a := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => simp only [Nat.add_zero, transition_self]; rfl
  | succ j ih =>
    rw [transition, Nat.leRecOn_succ le_self_add]
    change R.stageMap k (m + j + 1)
      (S.step (m + j) (transition S m (m + j) le_self_add a)) = _
    rw [stageMap_step]
    exact ih _

variable [Fact (∀ n, Function.Injective (S.step n))]

local instance limitOrder : PartialOrder (Limit S) := CStarAlgebra.spectralOrder _
local instance limitOrderedRing : StarOrderedRing (Limit S) :=
  CStarAlgebra.spectralOrderedRing _

/-- A genuine CPC retraction from the completed limit to each fixed stage. -/
def limitRetraction (k : ℕ) : Limit S →CP S.obj k :=
  LimitCPMaps.cpMap S (R.stageMap k) (R.stageMap_contractive k) (R.stageMap_transition k)

theorem limitRetraction_contractive (k : ℕ) (x : Limit S) :
    ‖R.limitRetraction k x‖ ≤ ‖x‖ :=
  LimitCPMaps.cpMap_contractive S (R.stageMap k)
    (R.stageMap_contractive k) (R.stageMap_transition k) x

@[simp] theorem limitRetraction_stage (k m : ℕ) (a : S.obj m) :
    R.limitRetraction k (stage S m a) = R.stageMap k m a :=
  LimitCPMaps.cpMap_stage S (R.stageMap k)
    (R.stageMap_contractive k) (R.stageMap_transition k) m a

/-- Retraction followed by stage inclusion fixes every earlier stage exactly. -/
theorem stage_limitRetraction_of_le (k m : ℕ) (h : m ≤ k) (a : S.obj m) :
    stage S k (R.limitRetraction k (stage S m a)) = stage S m a := by
  rw [limitRetraction_stage, stageMap_of_le R k m h, homCP_apply]
  exact compatible_transition S (stage S) (stage_commutes S) m k h a

@[simp] theorem limitRetraction_same_stage (k : ℕ) (a : S.obj k) :
    R.limitRetraction k (stage S k a) = a := by
  rw [limitRetraction_stage, stageMap_of_le R k k le_rfl, transition_self]
  rfl

/-- A quantitative estimate reducing retraction error to a stage approximation. -/
theorem retraction_error_le (k m : ℕ) (h : m ≤ k) (a : S.obj m) (x : Limit S) :
    ‖stage S k (R.limitRetraction k x) - x‖ ≤ 2 * ‖x - stage S m a‖ := by
  have hfix := R.stage_limitRetraction_of_le k m h a
  calc
    ‖stage S k (R.limitRetraction k x) - x‖ ≤
        ‖stage S k (R.limitRetraction k x) - stage S m a‖ + ‖stage S m a - x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖stage S k (R.limitRetraction k (x - stage S m a))‖ + ‖x - stage S m a‖ := by
      rw [map_sub, map_sub, hfix, norm_sub_rev (stage S m a) x]
    _ ≤ ‖x - stage S m a‖ + ‖x - stage S m a‖ := by
      rw [norm_stage]
      exact add_le_add (R.limitRetraction_contractive k _) le_rfl
    _ = 2 * ‖x - stage S m a‖ := by ring


/-- Retraction to late stages approximates the identity uniformly on each
finite set. The index and error bound are derived from the dense stage union. -/
theorem finite_retraction_approx (s : Finset (Limit S)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ k, N ≤ k → ∀ x ∈ s, ‖stage S k (R.limitRetraction k x) - x‖ < ε := by
  classical
  have hex (x : s) : ∃ m, ∃ a : S.obj m,
      ‖(x : Limit S) - stage S m a‖ < ε / 2 := by
    obtain ⟨y, hy, hxy⟩ := (dense_stage_union S).exists_dist_lt (x : Limit S) (half_pos hε)
    rcases Set.mem_iUnion.mp hy with ⟨m, a, rfl⟩
    exact ⟨m, a, by simpa only [dist_eq_norm] using hxy⟩
  choose m a ha using hex
  let N := Finset.univ.sup m
  refine ⟨N, ?_⟩
  intro k hk x hx
  let z : s := ⟨x, hx⟩
  have hm : m z ≤ k := (Finset.le_sup (Finset.mem_univ z)).trans hk
  calc
    ‖stage S k (R.limitRetraction k x) - x‖ ≤ 2 * ‖x - stage S (m z) (a z)‖ :=
      R.retraction_error_le k (m z) hm (a z) x
    _ < ε := by have h := ha z; linarith

/-- The constructed CPC retractions converge pointwise to the identity after
inclusion in the limit. -/
theorem tendsto_stage_limitRetraction (x : Limit S) :
    Filter.Tendsto (fun k => stage S k (R.limitRetraction k x)) Filter.atTop (nhds x) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := R.finite_retraction_approx {x} ε hε
  refine ⟨N, ?_⟩
  intro k hk
  simpa only [dist_eq_norm] using hN k hk x (Finset.mem_singleton_self x)

include R in
/-- Exact target CPAP passes to the constructed injective limit when the actual
adjacent connecting maps have the specified CPC left inverses. -/
theorem hasCPApproximation
    (hstage : ∀ n, Target.HasCPApproximation ⟨S.obj n, inferInstance⟩) :
    Target.HasCPApproximation ⟨Limit S, inferInstance⟩ := by
  classical
  intro s ε hε
  obtain ⟨k, hk⟩ := R.finite_retraction_approx s (ε / 2) (half_pos hε)
  obtain ⟨n, hn, φ, ψ, hφ, hψ, happ⟩ :=
    hstage k (s.image (R.limitRetraction k)) (ε / 2) (half_pos hε)
  refine ⟨n, hn, cpComp φ (R.limitRetraction k),
    cpComp (homCP (stage S k)) ψ, ?_, ?_, ?_⟩
  · intro x
    exact (hφ (R.limitRetraction k x)).trans (R.limitRetraction_contractive k x)
  · intro M
    change ‖stage S k (ψ M)‖ ≤ ‖M‖
    rw [norm_stage]
    exact hψ M
  · intro x hx
    have hfirst := happ (R.limitRetraction k x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hsecond := hk k le_rfl x hx
    change ‖stage S k (ψ (φ (R.limitRetraction k x))) - x‖ < ε
    calc
      _ ≤ ‖stage S k (ψ (φ (R.limitRetraction k x))) - stage S k (R.limitRetraction k x)‖ +
          ‖stage S k (R.limitRetraction k x) - x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖ψ (φ (R.limitRetraction k x)) - R.limitRetraction k x‖ +
          ‖stage S k (R.limitRetraction k x) - x‖ := by rw [← map_sub, norm_stage]
      _ < ε / 2 + ε / 2 := add_lt_add hfirst hsecond
      _ = ε := by ring


omit [Fact (∀ n, Function.Injective (S.step n))] in
/-- The constructed limit bundled as a target algebra. Injectivity needed by
the construction is derived from the supplied actual left inverses. -/
def splitLimitAlgebra : Target.UnitalAlgebra.{u} := by
  let : Fact (∀ n, Function.Injective (S.step n)) := ⟨R.step_injective⟩
  exact ⟨Limit S, inferInstance⟩

omit [Fact (∀ n, Function.Injective (S.step n))] in
/-- A formulation requiring only stage CPAP and actual adjacent CPC splittings.
There is no separate assumed limit, injectivity, or limit approximation theorem. -/
theorem splitLimit_hasCPApproximation
    (hstage : ∀ n, Target.HasCPApproximation ⟨S.obj n, inferInstance⟩) :
    Target.HasCPApproximation R.splitLimitAlgebra := by
  let : Fact (∀ n, Function.Injective (S.step n)) := ⟨R.step_injective⟩
  exact R.hasCPApproximation hstage

end CPCSplitting

end Suzuki.CPApproximationLimits

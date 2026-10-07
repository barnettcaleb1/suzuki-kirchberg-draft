import Suzuki.OrthogonalFiniteDiagrams
import Suzuki.PositiveMultiplicityFullness
import Suzuki.EvaluationLimitSimplicity

/-!
# Fullness of actual nonunital finite noise channels

Block aggregation preserves every matrix entry of each channel. Thus positive
multiplicity images remain nonzero in every target block after orthogonal
placement. This proves fullness for actual nonunital noise images, not merely
their support projections. The last theorem propagates that finite calculation
through an actual evaluated path into the completed C*-limit.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Suzuki.OrthogonalNoiseFullness
open Matrix MultiplicityEmbeddings FiniteDiagram OrthogonalFiniteDiagrams
open PositiveMultiplicityFullness
open scoped CStarAlgebra ComplexOrder

variable {C s t : Type*} [Fintype C] [Fintype s] [Fintype t]
  [DecidableEq C] [DecidableEq s] [DecidableEq t]

omit [DecidableEq s] in
theorem channel_entry (w : C → s → ℕ) (c : C) (v : s) (a : Blocks (w c))
    (i j : Fin (w c v)) :
    channel (fun c => Blocks (w c)) (stack w) c a v
      (channelEquiv w v ⟨c,i⟩) (channelEquiv w v ⟨c,j⟩) = a v i j := by
  change copyHom (fun c => w c v) id
    (fun d => (Pi.single c a : Family w) d v)
    ((channelEquiv w v).symm (channelEquiv w v ⟨c,i⟩))
    ((channelEquiv w v).symm (channelEquiv w v ⟨c,j⟩)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, copyHom_same]
  simp only [id_eq, Pi.single_eq_same]

omit [DecidableEq s] in
theorem channel_block_injective (w : C → s → ℕ) (c : C) (v : s)
    {a b : Blocks (w c)}
    (h : channel (fun c => Blocks (w c)) (stack w) c a v =
      channel (fun c => Blocks (w c)) (stack w) c b v) : a v = b v := by
  ext i j
  have he := congrArg (fun x : CStarMatrix (Fin (total w v)) (Fin (total w v)) ℂ =>
    x (channelEquiv w v ⟨c,i⟩) (channelEquiv w v ⟨c,j⟩)) h
  simpa only [channel_entry] using he

omit [DecidableEq s] in
theorem channel_block_ne_zero (w : C → s → ℕ) (c : C) (v : s)
    {a : Blocks (w c)} (ha : a v ≠ 0) :
    channel (fun c => Blocks (w c)) (stack w) c a v ≠ 0 := by
  intro hz
  apply ha
  have h := channel_block_injective w c v (a := a) (b := 0)
    (hz.trans (by simp))
  exact h

omit [DecidableEq s] in
theorem stackInto_channel_block_ne_zero (w : C → s → ℕ) (d : s → ℕ)
    (hd : total w = d) (c : C) (v : s) {a : Blocks (w c)} (ha : a v ≠ 0) :
    channel (fun c => Blocks (w c)) (stackInto w d hd) c a v ≠ 0 := by
  subst d
  exact channel_block_ne_zero w c v ha

omit [DecidableEq s] [DecidableEq t] in
theorem factor_channel_entry (w : C → s → ℕ) (H : Matrix t s ℕ) (c : C) (v : t)
    (a : Blocks (targetSize (w c) H)) (i j : Fin (targetSize (w c) H v)) :
    channel (fun c => Blocks (targetSize (w c) H)) (factorStack w H) c a v
      (factorEquiv w H v ⟨c,i⟩) (factorEquiv w H v ⟨c,j⟩) = a v i j := by
  change copyHom (fun c => targetSize (w c) H v) id
    (fun d => (Pi.single c a : Family (fun c => targetSize (w c) H)) d v)
    ((factorEquiv w H v).symm (factorEquiv w H v ⟨c,i⟩))
    ((factorEquiv w H v).symm (factorEquiv w H v ⟨c,j⟩)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, copyHom_same]
  simp only [id_eq, Pi.single_eq_same]

omit [DecidableEq s] [DecidableEq t] in
theorem factor_channel_block_ne_zero (w : C → s → ℕ) (H : Matrix t s ℕ)
    (c : C) (v : t) {a : Blocks (targetSize (w c) H)} (ha : a v ≠ 0) :
    channel (fun c => Blocks (targetSize (w c) H)) (factorStack w H) c a v ≠ 0 := by
  intro hz
  apply ha
  ext i j
  have h := factor_channel_entry w H c v a i j
  rw [hz] at h
  exact h.symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive multiplicities remain full after a genuinely nonunital channel placement. -/
theorem stack_positive_image_full (w : C → t → ℕ) (c : C)
    (k : ι → ℕ) (M : Matrix t ι ℕ) (φ : Blocks k →⋆ₐ[ℂ] Blocks (w c))
    (hφ : HasMultiplicity k M (w c) φ) (hM : ∀ v i, 0 < M v i)
    {a : Blocks k} (ha : a ≠ 0) (I : TwoSidedIdeal (Blocks (total w)))
    (hI : channel (fun c => Blocks (w c)) (stack w) c (φ a) ∈ I) : I = ⊤ := by
  apply ideal_eq_top_of_blocks (total w) I hI
  intro v
  exact channel_block_ne_zero w c v (image_block_ne_zero k M (w c) φ hφ hM ha v)

omit [DecidableEq s] in
/-- The same calculation for the rearranged target factor coordinates. -/
theorem factor_positive_image_full (w : C → s → ℕ) (H : Matrix t s ℕ) (c : C)
    (k : ι → ℕ) (M : Matrix t ι ℕ)
    (φ : Blocks k →⋆ₐ[ℂ] Blocks (targetSize (w c) H))
    (hφ : HasMultiplicity k M (targetSize (w c) H) φ) (hM : ∀ v i, 0 < M v i)
    {a : Blocks k} (ha : a ≠ 0) (I : TwoSidedIdeal (Blocks (targetSize (total w) H)))
    (hI : channel (fun c => Blocks (targetSize (w c) H)) (factorStack w H) c (φ a) ∈ I) :
    I = ⊤ := by
  apply ideal_eq_top_of_blocks (targetSize (total w) H) I hI
  intro v
  exact factor_channel_block_ne_zero w H c v
    (image_block_ne_zero k M (targetSize (w c) H) φ hφ hM ha v)

omit [DecidableEq t] in
/-- Literal aggregate square retaining the rowwise nonzero-element property. -/
theorem aggregate_square_blocks (w : C → s → ℕ) (D : s → ℕ) (hD : total w = D)
    (H : Matrix t s ℕ) (d : C → t → ℕ) (hd : ∀ c, targetSize (w c) H = d c)
    (f : t → ℕ) (hf : targetSize D H = f) :
    ∃ F : Family d →⋆ₐ[ℂ] Blocks f, Isometry F ∧
      (∀ c v (a : Blocks (d c)), a v ≠ 0 →
        channel (fun c => Blocks (d c)) F c a v ≠ 0) ∧
      ∀ c a, channel (fun c => Blocks (d c)) F c
        (intoDimensions (w c) H (d c) (hd c) a) =
      intoDimensions D H f hf
        (channel (fun c => Blocks (w c)) (stackInto w D hD) c a) := by
  subst D
  have hd' : (fun c => targetSize (w c) H) = d := funext hd
  subst d
  subst f
  exact ⟨factorStack w H, NonUnitalStarAlgHom.isometry _ (factorStack_injective w H),
    (fun c v a ha => factor_channel_block_ne_zero w H c v ha), channel_square w H⟩

section Suzuki
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem two_target_squares_blocks (k l : C → m → ℕ) (A : Matrix m m ℕ) :
    ∃ (F₀ : Family (fun c => k c + l c) →⋆ₐ[ℂ] Blocks (total k + total l))
      (F₁ : Family (fun c => k c + A *ᵥ l c) →⋆ₐ[ℂ] Blocks (total k + A *ᵥ total l)),
      Isometry F₀ ∧ Isometry F₁ ∧
      (∀ c v (a : Blocks (k c + l c)), a v ≠ 0 →
        channel (fun c => Blocks (k c + l c)) F₀ c a v ≠ 0) ∧
      (∀ c v (a : Blocks (k c + A *ᵥ l c)), a v ≠ 0 →
        channel (fun c => Blocks (k c + A *ᵥ l c)) F₁ c a v ≠ 0) ∧
      (∀ c a, channel (fun c => Blocks (k c + l c)) F₀ c (firstInclusion (k c) (l c) a) =
        firstInclusion (total k) (total l)
          (channel (fun c => Blocks (commonWeights k l c)) (commonAggregate k l) c a)) ∧
      (∀ c a, channel (fun c => Blocks (k c + A *ᵥ l c)) F₁ c (secondInclusion A (k c) (l c) a) =
        secondInclusion A (total k) (total l)
          (channel (fun c => Blocks (commonWeights k l c)) (commonAggregate k l) c a)) := by
  obtain ⟨F₀, hi₀, hb₀, hs₀⟩ := aggregate_square_blocks (commonWeights k l)
    (Sum.elim (total k) (total l)) (total_commonWeights k l)
    firstMultiplicity (fun c => k c + l c) (fun c => first_targetSize (k c) (l c))
    (total k + total l) (first_targetSize (total k) (total l))
  obtain ⟨F₁, hi₁, hb₁, hs₁⟩ := aggregate_square_blocks (commonWeights k l)
    (Sum.elim (total k) (total l)) (total_commonWeights k l)
    (secondMultiplicity A) (fun c => k c + A *ᵥ l c) (fun c => second_targetSize A (k c) (l c))
    (total k + A *ᵥ total l) (second_targetSize A (total k) (total l))
  exact ⟨F₀, F₁, hi₀, hi₁, hb₀, hb₁, hs₀, hs₁⟩

set_option maxHeartbeats 1000000 in
/-- The actual positive aggregate has full images for every nonzero source
element in each of its three finite constituents. -/
theorem positive_aggregate_realizations (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (k l : C → n → ℕ) (T : C → Matrix (m ⊕ m) (n ⊕ n) ℕ)
    (S R : C → Matrix m n ℕ) (D : ∀ c, Realization A A' (T c) (S c) (R c) (k c) (l c))
    (hT : ∀ c v i, 0 < T c v i) (hS : ∀ c v i, 0 < S c v i)
    (hR : ∀ c v i, 0 < R c v i) :
    ∃ G : Aggregate A A' k l T,
      (∀ c (a : Blocks (Sum.elim (k c) (l c))), a ≠ 0 → ∀ v, G.common c a v ≠ 0) ∧
      (∀ c (a : Blocks (k c + l c)), a ≠ 0 → ∀ v, G.left c a v ≠ 0) ∧
      (∀ c (a : Blocks (k c + A *ᵥ l c)), a ≠ 0 → ∀ v, G.right c a v ≠ 0) := by
  let K := channelLeft k l T
  let L := channelRight k l T
  obtain ⟨F₀,F₁,hi₀,hi₁,hb₀,hb₁,hs₀,hs₁⟩ := two_target_squares_blocks K L A'
  let Q := commonAggregate K L
  let γ := fun c => (channel (fun c => Blocks (commonWeights K L c)) Q c).comp
    (commonMap (k c) (l c) (T c)).toNonUnitalStarAlgHom
  let β₀ := fun c => (channel (fun c => Blocks (K c + L c)) F₀ c).comp
    (D c).left.toNonUnitalStarAlgHom
  let β₁ := fun c => (channel (fun c => Blocks (K c + A' *ᵥ L c)) F₁ c).comp
    (D c).right.toNonUnitalStarAlgHom
  have hγ (c : C) : γ c 1 = channel (fun c => Blocks (commonWeights K L c)) Q c 1 := by
    change channel _ Q c (commonMap (k c) (l c) (T c) 1) = _
    rw [map_one]
  refine ⟨⟨γ,β₀,β₁,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩, ?_, ?_, ?_⟩
  · intro c
    exact NonUnitalStarAlgHom.isometry _ ((channel_injective _ Q
      (stackInto_injective _ _ _) c).comp (D c).common_isometry.injective)
  · intro c
    exact NonUnitalStarAlgHom.isometry _ ((channel_injective _ F₀ hi₀.injective c).comp
      (D c).left_isometry.injective)
  · intro c
    exact NonUnitalStarAlgHom.isometry _ ((channel_injective _ F₁ hi₁.injective c).comp
      (D c).right_isometry.injective)
  · intro c; rw [hγ]; exact channel_unit_projection _ Q c
  · intro c d h; rw [hγ,hγ]; exact channel_orthogonal _ Q c d h
  · change ∑ c, γ c 1 = 1
    calc
      ∑ c, γ c 1 = ∑ c, channel (fun c => Blocks (commonWeights K L c)) Q c 1 :=
        Finset.sum_congr rfl (fun c _ => hγ c)
      _ = 1 := channel_unit_sum _ Q
  · intro c i hi
    rw [hγ]
    exact stackInto_channel_block_nonzero _ _ _ c i hi
  · intro c a
    change channel _ F₀ c ((D c).left (firstInclusion (k c) (l c) a)) = _
    have h := DFunLike.congr_fun (D c).first_square a
    change (D c).left (firstInclusion (k c) (l c) a) = _ at h
    rw [h]
    exact hs₀ c (commonMap (k c) (l c) (T c) a)
  · intro c a
    change channel _ F₁ c ((D c).right (secondInclusion A (k c) (l c) a)) = _
    have h := DFunLike.congr_fun (D c).second_square a
    change (D c).right (secondInclusion A (k c) (l c) a) = _ at h
    rw [h]
    exact hs₁ c (commonMap (k c) (l c) (T c) a)
  · intro c a ha v
    change channel _ Q c (commonMap (k c) (l c) (T c) a) v ≠ 0
    have hn := image_block_ne_zero _ _ _ _ (D c).common_multiplicity (hT c) ha v
    exact stackInto_channel_block_ne_zero (commonWeights K L)
      (Sum.elim (total K) (total L)) (total_commonWeights K L) c v hn
  · intro c a ha v
    exact hb₀ c v ((D c).left a)
      (image_block_ne_zero _ _ _ _ (D c).left_multiplicity (hS c) ha v)
  · intro c a ha v
    exact hb₁ c v ((D c).right a)
      (image_block_ne_zero _ _ _ _ (D c).right_multiplicity (hR c) ha v)

/-- Positive integer diagrams produce actual orthogonal channels whose every
nonzero image is full in each finite target constituent. -/
theorem integer_aggregate_full [Nonempty m]
    (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (hB : PositiveLifting.Positive B) (hB' : PositiveLifting.Positive B')
    (S H Z : C → Matrix m n ℤ)
    (hchain : ∀ c, S c * B = B' * H c)
    (hS : ∀ c, PositiveLifting.Positive (S c))
    (hT : ∀ c, PositiveLifting.Positive (MatrixDiagrams.diagram B (S c) (H c) (Z c)))
    (hR : ∀ c, PositiveLifting.Positive (S c + B' * Z c))
    (k l : C → n → ℕ) :
    ∃ G : Aggregate (natMatrix (1+B)) (natMatrix (1+B')) k l
      (fun c => natMatrix (MatrixDiagrams.diagram B (S c) (H c) (Z c))),
      (∀ c (a : Blocks (Sum.elim (k c) (l c))), a ≠ 0 → ∀ v, G.common c a v ≠ 0) ∧
      (∀ c (a : Blocks (k c + l c)), a ≠ 0 → ∀ v, G.left c a v ≠ 0) ∧
      (∀ c (a : Blocks (k c + natMatrix (1+B) *ᵥ l c)), a ≠ 0 → ∀ v, G.right c a v ≠ 0) := by
  let D c := Classical.choice (integer_realization B B' (S c) (H c) (Z c)
    hB hB' (hchain c) (hS c) (hT c) (hR c) (k c) (l c))
  exact positive_aggregate_realizations _ _ k l _ (fun c => natMatrix (S c))
    (fun c => natMatrix (S c+B'*Z c)) D
    (fun c => natMatrix_positive _ (hT c))
    (fun c => natMatrix_positive _ (hS c))
    (fun c => natMatrix_positive _ (hR c))
/-- Arbitrary maps of the actual integer presentations now yield an
orthogonal aggregate after the same simultaneous positive target change. -/
theorem simultaneous_aggregate_full [Nontrivial m]
    (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (hB : PositiveLifting.Positive B) (hB' : PositiveLifting.Positive B')
    (f₀ : C → PositiveLifting.Cokernel B →ₗ[ℤ] PositiveLifting.Cokernel B')
    (f₁ : C → PositiveLifting.Kernel B →ₗ[ℤ] PositiveLifting.Kernel B')
    (k l : C → n → ℕ) :
    ∃ (U : Matrix m m ℤ) (hU : IsUnit U),
      U.det = 1 ∧ (∀ i j, 0 ≤ U i j) ∧ PositiveLifting.Positive (U*B') ∧
      PositiveLifting.Kernel (U*B') = PositiveLifting.Kernel B' ∧
      ∃ (S H Z : C → Matrix m n ℤ),
        (∀ c, S c * B = (U*B') * H c ∧
          PositiveLifting.Positive (S c) ∧
          PositiveLifting.Positive (MatrixDiagrams.diagram B (S c) (H c) (Z c)) ∧
          PositiveLifting.Positive (S c + (U*B') * Z c) ∧
          (∀ x, PositiveLifting.quotient (U*B') (S c *ᵥ x) =
            PositiveLifting.targetCokernelEquiv B' U hU (f₀ c (PositiveLifting.quotient B x))) ∧
          (∀ x : PositiveLifting.Kernel B, H c *ᵥ x.val = (f₁ c x).val)) ∧
        ∃ G : Aggregate (natMatrix (1+B)) (natMatrix (1+U*B')) k l
          (fun c => natMatrix (MatrixDiagrams.diagram B (S c) (H c) (Z c))),
          (∀ c (a : Blocks (Sum.elim (k c) (l c))), a ≠ 0 → ∀ v, G.common c a v ≠ 0) ∧
          (∀ c (a : Blocks (k c + l c)), a ≠ 0 → ∀ v, G.left c a v ≠ 0) ∧
          (∀ c (a : Blocks (k c + natMatrix (1+B) *ᵥ l c)), a ≠ 0 → ∀ v, G.right c a v ≠ 0) := by
  obtain ⟨U,hU,hdet,hU0,hUB,hker,S,H,Z,h⟩ :=
    PositiveLifting.simultaneous_positive_lifting B B' hB hB' f₀ f₁
  refine ⟨U,hU,hdet,hU0,hUB,hker,S,H,Z,h,?_⟩
  exact integer_aggregate_full B (U*B') hB hUB S H Z
    (fun c => (h c).1) (fun c => (h c).2.1)
    (fun c => (h c).2.2.1) (fun c => (h c).2.2.2.1) k l

end Suzuki

section Limit
open EvaluationLimitSimplicity SequentialCStarLimit

variable (D : Channels) [Fact (∀ n, Function.Injective (D.system.step n))]

/-- A positive finite noise channel forces a containing ideal to be all of the
actual completed limit. Detection, the branch factorization and positive
multiplicity data are explicit; ideal fullness is derived from those data. -/
theorem finite_noise_ideal_eq_top
    (choose : ∀ n, Fin (D.count n)) (m r : ℕ) (index : Fin (D.count (m+r)))
    (w : C → t → ℕ) (c : C) (k : ι → ℕ) (M : Matrix t ι ℕ)
    (evaluation : D.obj (m+r) →⋆ₙₐ[ℂ] Blocks k)
    (φ : Blocks k →⋆ₐ[ℂ] Blocks (w c))
    (hφ : HasMultiplicity k M (w c) φ) (hM : ∀ v i, 0 < M v i)
    (constant : Blocks (total w) →⋆ₐ[ℂ] D.obj (m+(r+1)))
    (factor : ∀ x, D.map (m+r) index x =
      constant (channel (fun c => Blocks (w c)) (stack w) c (φ (evaluation x))))
    (a : D.obj m) (detects : evaluation (D.path choose m r a) ≠ 0)
    (I : TwoSidedIdeal (Limit D.system)) (hI : stage D.system m a ∈ I) : I = ⊤ := by
  have hm := D.final_mem_ideal choose m r index a I hI
  rw [factor] at hm
  apply ambient_ideal_eq_top (total w)
    ((stage D.system (m+(r+1))).comp constant) I hm
  intro v
  exact channel_block_ne_zero w c v
    (image_block_ne_zero k M (w c) φ hφ hM detects v)

end Limit

end Suzuki.OrthogonalNoiseFullness

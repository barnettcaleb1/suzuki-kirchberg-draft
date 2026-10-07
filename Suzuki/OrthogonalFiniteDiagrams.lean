import Suzuki.SuzukiFiniteDiagram
import Suzuki.OrthogonalChannels
/-!
# Orthogonal aggregate finite Suzuki diagrams

Concrete block-diagonal embeddings and a proved rearrangement of channel and
multiplicity coordinates yield literal squares with the standard target
inclusions. Channel source dimensions may vary, including scalar-amplified
weights. Common and factor channel units are orthogonal projections summing
to one; every channel map is isometric. For equal source weights the sums are
actual unital isometric maps and both summed squares commute literally.

`simultaneous_aggregate` connects the construction to the actual integer
kernel/cokernel lifting theorem. `weighted_common_dimensions` proves the
weighted total dimension equation. Positive supports are proved nonzero in
each matrix block; ideal-theoretic fullness, identification with matrix
amplification of full products, graph/K-theory identifications, and the main
manuscript theorem are not claimed here.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Suzuki.OrthogonalFiniteDiagrams
open Matrix MultiplicityEmbeddings FiniteDiagram
open scoped CStarAlgebra ComplexOrder
variable {C s t : Type*} [Fintype C] [Fintype s] [Fintype t]
  [DecidableEq C] [DecidableEq s] [DecidableEq t]

abbrev Family (w : C → s → ℕ) := ∀ c, Blocks (w c)
def total (w : C → s → ℕ) : s → ℕ := fun i => ∑ c, w c i

def channelEquiv (w : C → s → ℕ) (i : s) : (Σ c, Fin (w c i)) ≃ Fin (total w i) :=
  (Fintype.equivFin _).trans (finCongr (by simp [total, Fintype.card_sigma]))

def columnHom (w : C → s → ℕ) (i : s) :
    Family w →⋆ₐ[ℂ] Blocks (fun c => w c i) where
  toFun a c := a c i
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def stackRow (w : C → s → ℕ) (i : s) :
    Family w →⋆ₐ[ℂ] CStarMatrix (Fin (total w i)) (Fin (total w i)) ℂ :=
  ((CStarMatrix.reindexₐ ℂ ℂ (channelEquiv w i)).toStarAlgHom.comp
    (copyHom (fun c => w c i) id)).comp (columnHom w i)

def stack (w : C → s → ℕ) : Family w →⋆ₐ[ℂ] Blocks (total w) where
  toFun a i := stackRow w i a
  map_zero' := by funext i; exact map_zero (stackRow w i)
  map_one' := by funext i; exact map_one (stackRow w i)
  map_add' := by intro a b; funext i; exact map_add (stackRow w i) a b
  map_mul' := by intro a b; funext i; exact map_mul (stackRow w i) a b
  commutes' := by intro z; funext i; exact (stackRow w i).commutes z
  map_star' := by intro a; funext i; exact map_star (stackRow w i) a

omit [DecidableEq s] in
theorem stack_injective (w : C → s → ℕ) : Function.Injective (stack w) := by
  intro a b h
  funext c i
  have hrow := congrArg (fun f : Blocks (total w) => f i) h
  dsimp only [stack, stackRow, StarAlgHom.comp_apply, columnHom] at hrow
  have hc := (CStarMatrix.reindexₐ ℂ ℂ (channelEquiv w i)).injective hrow
  have hd := copyHom_injective (fun c => w c i) id (fun c => ⟨c,rfl⟩) hc
  exact congrFun hd c

def swapCopies (w : C → s → ℕ) (H : Matrix t s ℕ) (i : t) :
    (Σ c, Σ d : Copies H i, Fin (w c d.1)) ≃
      (Σ d : Copies H i, Σ c, Fin (w c d.1)) where
  toFun z := ⟨z.2.1, z.1, z.2.2⟩
  invFun z := ⟨z.2.1, z.1, z.2.2⟩
  left_inv := by rintro ⟨c,d,j⟩; rfl
  right_inv := by rintro ⟨d,c,j⟩; rfl

def factorEquiv (w : C → s → ℕ) (H : Matrix t s ℕ) (i : t) :
    (Σ c, Fin (targetSize (w c) H i)) ≃ Fin (targetSize (total w) H i) :=
  (Equiv.sigmaCongrRight (fun c => (slotEquiv (w c) H i).symm)).trans
    ((swapCopies w H i).trans
      ((Equiv.sigmaCongrRight (fun d : Copies H i => channelEquiv w d.1)).trans
        (slotEquiv (total w) H i)))

def factorRow (w : C → s → ℕ) (H : Matrix t s ℕ) (i : t) :
    Family (fun c => targetSize (w c) H) →⋆ₐ[ℂ]
      CStarMatrix (Fin (targetSize (total w) H i)) (Fin (targetSize (total w) H i)) ℂ :=
  ((CStarMatrix.reindexₐ ℂ ℂ (factorEquiv w H i)).toStarAlgHom.comp
    (copyHom (fun c => targetSize (w c) H i) id)).comp
    (columnHom (fun c => targetSize (w c) H) i)

def factorStack (w : C → s → ℕ) (H : Matrix t s ℕ) :
    Family (fun c => targetSize (w c) H) →⋆ₐ[ℂ] Blocks (targetSize (total w) H) where
  toFun a i := factorRow w H i a
  map_zero' := by funext i; exact map_zero (factorRow w H i)
  map_one' := by funext i; exact map_one (factorRow w H i)
  map_add' := by intro a b; funext i; exact map_add (factorRow w H i) a b
  map_mul' := by intro a b; funext i; exact map_mul (factorRow w H i) a b
  commutes' := by intro z; funext i; exact (factorRow w H i).commutes z
  map_star' := by intro a; funext i; exact map_star (factorRow w H i) a

omit [DecidableEq s] [DecidableEq t] in
theorem factorStack_injective (w : C → s → ℕ) (H : Matrix t s ℕ) :
    Function.Injective (factorStack w H) := by
  intro a b h
  funext c i
  have hrow := congrArg (fun f : Blocks (targetSize (total w) H) => f i) h
  dsimp only [factorStack, factorRow, StarAlgHom.comp_apply, columnHom] at hrow
  have hc := (CStarMatrix.reindexₐ ℂ ℂ (factorEquiv w H i)).injective hrow
  have hd := copyHom_injective (fun c => targetSize (w c) H i) id (fun c => ⟨c,rfl⟩) hc
  exact congrFun hd c

omit [DecidableEq t] in
theorem factorStack_square (w : C → s → ℕ) (H : Matrix t s ℕ) (a : Family w) :
    factorStack w H (fun c => multiplicityHom (w c) H (a c)) =
      multiplicityHom (total w) H (stack w a) := by
  funext v
  apply CStarMatrix.ext
  intro r s
  obtain ⟨⟨c,r⟩,rfl⟩ := (factorEquiv w H v).surjective r
  obtain ⟨⟨d,s⟩,rfl⟩ := (factorEquiv w H v).surjective s
  obtain ⟨⟨u,i⟩,rfl⟩ := (slotEquiv (w c) H v).surjective r
  obtain ⟨⟨z,j⟩,rfl⟩ := (slotEquiv (w d) H v).surjective s
  change copyHom (fun c => targetSize (w c) H v) id
    (fun c => multiplicityHom (w c) H (a c) v)
    ((factorEquiv w H v).symm (factorEquiv w H v ⟨c,slotEquiv (w c) H v ⟨u,i⟩⟩))
    ((factorEquiv w H v).symm (factorEquiv w H v ⟨d,slotEquiv (w d) H v ⟨z,j⟩⟩)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hcoord (c : C) (u : Copies H v) (i : Fin (w c u.1)) :
      factorEquiv w H v ⟨c,slotEquiv (w c) H v ⟨u,i⟩⟩ =
      slotEquiv (total w) H v ⟨u,channelEquiv w u.1 ⟨c,i⟩⟩ := by
    simp [factorEquiv, swapCopies]
  rw [hcoord, hcoord, multiplicityHom_pullback]
  by_cases hcd : c = d
  · subst d
    rw [copyHom_same]
    simp only [id_eq]
    rw [multiplicityHom_pullback]
    by_cases huz : u = z
    · subst z
      rw [copyHom_same, copyHom_same]
      change a c u.1 i j = copyHom (fun c => w c u.1) id (fun c => a c u.1)
        ((channelEquiv w u.1).symm (channelEquiv w u.1 ⟨c,i⟩))
        ((channelEquiv w u.1).symm (channelEquiv w u.1 ⟨c,j⟩))
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, copyHom_same]
      rfl
    · rw [copyHom_different _ _ _ huz, copyHom_different _ _ _ huz]
  · rw [copyHom_different _ _ _ hcd]
    by_cases huz : u = z
    · subst z
      rw [copyHom_same]
      change 0 = copyHom (fun c => w c u.1) id (fun c => a c u.1)
        ((channelEquiv w u.1).symm (channelEquiv w u.1 ⟨c,i⟩))
        ((channelEquiv w u.1).symm (channelEquiv w u.1 ⟨d,j⟩))
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, copyHom_different _ _ _ hcd]
    · rw [copyHom_different _ _ _ huz]


section Channels
variable (A : C → Type*) [∀ c, CStarAlgebra (A c)]

def singleHom (c : C) : A c →⋆ₙₐ[ℂ] (∀ d, A d) where
  toFun := Pi.single c
  map_zero' := by simp
  map_add' := by intro a b; funext d; by_cases h : d=c; subst d; simp; simp [Pi.single_eq_of_ne h]
  map_mul' := by intro a b; funext d; by_cases h : d=c; subst d; simp; simp [Pi.single_eq_of_ne h]
  map_smul' := by intro z a; funext d; by_cases h : d=c; subst d; simp; simp [Pi.single_eq_of_ne h]
  map_star' := by intro a; funext d; by_cases h : d=c; subst d; simp; simp [Pi.single_eq_of_ne h]

variable {B : Type*} [CStarAlgebra B]
def channel (F : (∀ c, A c) →⋆ₐ[ℂ] B) (c : C) : A c →⋆ₙₐ[ℂ] B :=
  F.toNonUnitalStarAlgHom.comp (singleHom A c)

omit [Fintype C] in
theorem channel_injective (F : (∀ c, A c) →⋆ₐ[ℂ] B)
    (hF : Function.Injective F) (c : C) : Function.Injective (channel A F c) := by
  intro a b h
  have he := hF h
  have := congrFun he c
  simpa [singleHom] using this

omit [Fintype C] in
theorem channel_orthogonal (F : (∀ c, A c) →⋆ₐ[ℂ] B) (c d : C) (hcd : c ≠ d) :
    channel A F c 1 * channel A F d 1 = 0 := by
  change F (Pi.single c 1) * F (Pi.single d 1) = 0
  rw [← map_mul]
  have hz : (Pi.single c (1 : A c)) * Pi.single d (1 : A d) = 0 := by
    funext e
    by_cases h : e=c
    · subst e; simp [Pi.single_eq_of_ne hcd]
    · simp [Pi.single_eq_of_ne h]
  rw [hz, map_zero]

theorem channel_unit_sum (F : (∀ c, A c) →⋆ₐ[ℂ] B) : ∑ c, channel A F c 1 = 1 := by
  change ∑ c, F (Pi.single c 1) = 1
  rw [← map_sum]
  have hu : (∑ c, Pi.single c (1 : A c)) = 1 := by
    funext d
    simp [Finset.sum_apply]
  rw [hu, map_one]

omit [Fintype C] in
theorem channel_unit_projection (F : (∀ c, A c) →⋆ₐ[ℂ] B) (c : C) :
    IsStarProjection (channel A F c 1) := by
  constructor
  · change channel A F c 1 * channel A F c 1 = channel A F c 1
    rw [← map_mul, one_mul]
  · change star (channel A F c 1) = channel A F c 1
    rw [← map_star, star_one]
end Channels

omit [DecidableEq t] in
/-- Literal compatibility for each coordinate channel, including its unit. -/
theorem channel_square (w : C → s → ℕ) (H : Matrix t s ℕ) (c : C) (a : Blocks (w c)) :
    channel (fun c => Blocks (targetSize (w c) H)) (factorStack w H) c
      (multiplicityHom (w c) H a) =
    multiplicityHom (total w) H (channel (fun c => Blocks (w c)) (stack w) c a) := by
  have hfamily : (fun d => multiplicityHom (w d) H ((Pi.single c a : Family w) d)) =
      Pi.single c (multiplicityHom (w c) H a) := by
    funext d
    by_cases h : d=c
    · subst d; simp
    · simp [Pi.single_eq_of_ne h]
  change factorStack w H (Pi.single c (multiplicityHom (w c) H a)) =
    multiplicityHom (total w) H (stack w (Pi.single c a))
  rw [← hfamily]
  exact factorStack_square w H (Pi.single c a)


omit [DecidableEq s] in
/-- The channel support is literally one on each of its assigned coordinates. -/
theorem channel_unit_diagonal (w : C → s → ℕ) (c : C) (i : s) (j : Fin (w c i)) :
    channel (fun c => Blocks (w c)) (stack w) c 1 i
      (channelEquiv w i ⟨c,j⟩) (channelEquiv w i ⟨c,j⟩) = 1 := by
  change copyHom (fun c => w c i) id
    (fun d => (Pi.single c (1 : Blocks (w c)) : Family w) d i)
    ((channelEquiv w i).symm (channelEquiv w i ⟨c,j⟩))
    ((channelEquiv w i).symm (channelEquiv w i ⟨c,j⟩)) = 1
  simp only [Equiv.symm_apply_apply]
  rw [copyHom_same]
  simp only [id_eq, Pi.single_eq_same]
  change (1 : Matrix (Fin (w c i)) (Fin (w c i)) ℂ) j j = 1
  simp

omit [DecidableEq s] in
theorem channel_unit_block_nonzero (w : C → s → ℕ) (c : C) (i : s)
    (hi : 0 < w c i) : channel (fun c => Blocks (w c)) (stack w) c 1 i ≠ 0 := by
  intro hz
  let j : Fin (w c i) := ⟨0,hi⟩
  have h := channel_unit_diagonal w c i j
  rw [hz] at h
  norm_num at h

def stackInto (w : C → s → ℕ) (D : s → ℕ) (hD : total w = D) :
    Family w →⋆ₐ[ℂ] Blocks D := hD ▸ stack w

omit [DecidableEq s] in
theorem stackInto_injective (w : C → s → ℕ) (D : s → ℕ) (hD : total w = D) :
    Function.Injective (stackInto w D hD) := by
  subst D
  exact stack_injective w

omit [DecidableEq s] in
theorem stackInto_channel_block_nonzero (w : C → s → ℕ) (D : s → ℕ) (hD : total w = D)
    (c : C) (i : s) (hi : 0 < w c i) :
    channel (fun c => Blocks (w c)) (stackInto w D hD) c 1 i ≠ 0 := by
  subst D
  exact channel_unit_block_nonzero w c i hi

omit [DecidableEq t] in
/-- The block aggregation square with all dimensions transported to specified
weights. The common embedding is fixed; only factor coordinates are rearranged. -/
theorem aggregate_square (w : C → s → ℕ) (D : s → ℕ) (hD : total w = D)
    (H : Matrix t s ℕ) (d : C → t → ℕ) (hd : ∀ c, targetSize (w c) H = d c)
    (f : t → ℕ) (hf : targetSize D H = f) :
    ∃ F : Family d →⋆ₐ[ℂ] Blocks f, Isometry F ∧
      ∀ c a, channel (fun c => Blocks (d c)) F c
        (intoDimensions (w c) H (d c) (hd c) a) =
      intoDimensions D H f hf
        (channel (fun c => Blocks (w c)) (stackInto w D hD) c a) := by
  subst D
  have hd' : (fun c => targetSize (w c) H) = d := funext hd
  subst d
  subst f
  exact ⟨factorStack w H, NonUnitalStarAlgHom.isometry _ (factorStack_injective w H),
    channel_square w H⟩


section Suzuki
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def commonWeights (k l : C → m → ℕ) : C → (m ⊕ m) → ℕ := fun c => Sum.elim (k c) (l c)

omit [Fintype m] [DecidableEq C] [DecidableEq m] in
theorem total_commonWeights (k l : C → m → ℕ) :
    total (commonWeights k l) = Sum.elim (total k) (total l) := by
  funext i
  cases i <;> rfl

def commonAggregate (k l : C → m → ℕ) :
    Family (commonWeights k l) →⋆ₐ[ℂ] Blocks (Sum.elim (total k) (total l)) :=
  stackInto _ _ (total_commonWeights k l)

/-- Both target inclusions admit the same fixed disjoint-block common
embedding. Source weights are allowed to depend on the channel. -/
theorem two_target_squares (k l : C → m → ℕ) (A : Matrix m m ℕ) :
    ∃ (F₀ : Family (fun c => k c + l c) →⋆ₐ[ℂ] Blocks (total k + total l))
      (F₁ : Family (fun c => k c + A *ᵥ l c) →⋆ₐ[ℂ] Blocks (total k + A *ᵥ total l)),
      Isometry F₀ ∧ Isometry F₁ ∧
      (∀ c a, channel (fun c => Blocks (k c + l c)) F₀ c (firstInclusion (k c) (l c) a) =
        firstInclusion (total k) (total l)
          (channel (fun c => Blocks (commonWeights k l c)) (commonAggregate k l) c a)) ∧
      (∀ c a, channel (fun c => Blocks (k c + A *ᵥ l c)) F₁ c (secondInclusion A (k c) (l c) a) =
        secondInclusion A (total k) (total l)
          (channel (fun c => Blocks (commonWeights k l c)) (commonAggregate k l) c a)) := by
  obtain ⟨F₀, hi₀, hs₀⟩ := aggregate_square (commonWeights k l)
    (Sum.elim (total k) (total l)) (total_commonWeights k l)
    firstMultiplicity (fun c => k c + l c) (fun c => first_targetSize (k c) (l c))
    (total k + total l) (first_targetSize (total k) (total l))
  obtain ⟨F₁, hi₁, hs₁⟩ := aggregate_square (commonWeights k l)
    (Sum.elim (total k) (total l)) (total_commonWeights k l)
    (secondMultiplicity A) (fun c => k c + A *ᵥ l c) (fun c => second_targetSize A (k c) (l c))
    (total k + A *ᵥ total l) (second_targetSize A (total k) (total l))
  exact ⟨F₀, F₁, hi₀, hi₁, hs₀, hs₁⟩

abbrev channelLeft (k l : C → n → ℕ) (T : C → Matrix (m ⊕ m) (n ⊕ n) ℕ) : C → m → ℕ :=
  fun c => targetLeft (k c) (l c) (T c)
abbrev channelRight (k l : C → n → ℕ) (T : C → Matrix (m ⊕ m) (n ⊕ n) ℕ) : C → m → ℕ :=
  fun c => targetRight (k c) (l c) (T c)

/-- The concrete nonunital maps of triples into one total finite diagram. -/
structure Aggregate (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (k l : C → n → ℕ) (T : C → Matrix (m ⊕ m) (n ⊕ n) ℕ) where
  common : ∀ c, Blocks (Sum.elim (k c) (l c)) →⋆ₙₐ[ℂ]
    Blocks (Sum.elim (total (channelLeft k l T)) (total (channelRight k l T)))
  left : ∀ c, Blocks (k c + l c) →⋆ₙₐ[ℂ]
    Blocks (total (channelLeft k l T) + total (channelRight k l T))
  right : ∀ c, Blocks (k c + A *ᵥ l c) →⋆ₙₐ[ℂ]
    Blocks (total (channelLeft k l T) + A' *ᵥ total (channelRight k l T))
  common_isometry : ∀ c, Isometry (common c)
  left_isometry : ∀ c, Isometry (left c)
  right_isometry : ∀ c, Isometry (right c)
  common_projection : ∀ c, IsStarProjection (common c 1)
  common_orthogonal : ∀ c d, c ≠ d → common c 1 * common d 1 = 0
  common_unit_sum : ∑ c, common c 1 = 1
  common_block_nonzero : ∀ c i,
    0 < commonWeights (channelLeft k l T) (channelRight k l T) c i → common c 1 i ≠ 0
  first_square : ∀ c a, left c (firstInclusion (k c) (l c) a) =
    firstInclusion (total (channelLeft k l T)) (total (channelRight k l T)) (common c a)
  second_square : ∀ c a, right c (secondInclusion A (k c) (l c) a) =
    secondInclusion A' (total (channelLeft k l T)) (total (channelRight k l T)) (common c a)

/-- Existing actual channelwise diagrams are placed into common total target
sizes. Each factor embedding is explicitly rearranged to the standard target
horizontal inclusion; the common embedding is the same in both squares. -/
theorem aggregate_realizations (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (k l : C → n → ℕ) (T : C → Matrix (m ⊕ m) (n ⊕ n) ℕ)
    (S R : C → Matrix m n ℕ) (D : ∀ c, Realization A A' (T c) (S c) (R c) (k c) (l c)) :
    Nonempty (Aggregate A A' k l T) := by
  let K := channelLeft k l T
  let L := channelRight k l T
  obtain ⟨F₀,F₁,hi₀,hi₁,hs₀,hs₁⟩ := two_target_squares K L A'
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
  refine ⟨⟨γ,β₀,β₁,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
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

namespace Aggregate
variable {A : Matrix n n ℕ} {A' : Matrix m m ℕ}
  {k l : C → n → ℕ} {T : C → Matrix (m ⊕ m) (n ⊕ n) ℕ}
variable (D : Aggregate A A' k l T)

omit [DecidableEq C] in
theorem left_unit (c : C) : D.left c 1 =
    firstInclusion (total (channelLeft k l T)) (total (channelRight k l T)) (D.common c 1) := by
  simpa only [map_one] using D.first_square c 1

omit [DecidableEq C] in
theorem right_unit (c : C) : D.right c 1 =
    secondInclusion A' (total (channelLeft k l T)) (total (channelRight k l T)) (D.common c 1) := by
  simpa only [map_one] using D.second_square c 1

omit [DecidableEq C] in
theorem left_orthogonal (c d : C) (h : c ≠ d) : D.left c 1 * D.left d 1 = 0 := by
  rw [D.left_unit, D.left_unit, ← map_mul, D.common_orthogonal c d h, map_zero]

omit [DecidableEq C] in
theorem right_orthogonal (c d : C) (h : c ≠ d) : D.right c 1 * D.right d 1 = 0 := by
  rw [D.right_unit, D.right_unit, ← map_mul, D.common_orthogonal c d h, map_zero]

omit [DecidableEq C] in
omit [DecidableEq C] in
theorem left_unit_sum : ∑ c, D.left c 1 = 1 := by
  simp_rw [D.left_unit]
  rw [← map_sum, D.common_unit_sum, map_one]

omit [DecidableEq C] in
omit [DecidableEq C] in
theorem right_unit_sum : ∑ c, D.right c 1 = 1 := by
  simp_rw [D.right_unit]
  rw [← map_sum, D.common_unit_sum, map_one]

omit [DecidableEq C] in
theorem left_projection (c : C) : IsStarProjection (D.left c 1) := by
  rw [D.left_unit]
  exact (D.common_projection c).map _

omit [DecidableEq C] in
theorem right_projection (c : C) : IsStarProjection (D.right c 1) := by
  rw [D.right_unit]
  exact (D.common_projection c).map _
omit [DecidableEq C] in
/-- Positive channel target weights make the actual support projection
nonzero in every simple matrix summand of the target common algebra. -/
theorem positive_common_blocks [Nonempty n]
    (hk : ∀ c j, 0 < k c j) (hT : ∀ c i j, 0 < T c i j) :
    ∀ c i, D.common c 1 i ≠ 0 := by
  intro c i
  apply D.common_block_nonzero c i
  obtain ⟨hK,hL⟩ := target_dimensions_positive (k c) (l c) (hk c) (T c) (hT c)
  cases i with
  | inl i => exact hK i
  | inr i => exact hL i

end Aggregate

/-- Positive integer diagrams give orthogonal actual finite diagrams for
arbitrary channel-dependent source weights, including amplified channels. -/
theorem integer_aggregate [Nonempty m]
    (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (hB : PositiveLifting.Positive B) (hB' : PositiveLifting.Positive B')
    (S H Z : C → Matrix m n ℤ)
    (hchain : ∀ c, S c * B = B' * H c)
    (hS : ∀ c, PositiveLifting.Positive (S c))
    (hT : ∀ c, PositiveLifting.Positive (MatrixDiagrams.diagram B (S c) (H c) (Z c)))
    (hR : ∀ c, PositiveLifting.Positive (S c + B' * Z c))
    (k l : C → n → ℕ) :
    Nonempty (Aggregate (natMatrix (1+B)) (natMatrix (1+B')) k l
      (fun c => natMatrix (MatrixDiagrams.diagram B (S c) (H c) (Z c)))) := by
  let D c := Classical.choice (integer_realization B B' (S c) (H c) (Z c)
    hB hB' (hchain c) (hS c) (hT c) (hR c) (k c) (l c))
  exact aggregate_realizations _ _ k l _ (fun c => natMatrix (S c))
    (fun c => natMatrix (S c+B'*Z c)) D
/-- Arbitrary maps of the actual integer presentations now yield an
orthogonal aggregate after the same simultaneous positive target change. -/
theorem simultaneous_aggregate [Nontrivial m]
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
        Nonempty (Aggregate (natMatrix (1+B)) (natMatrix (1+U*B')) k l
          (fun c => natMatrix (MatrixDiagrams.diagram B (S c) (H c) (Z c)))) := by
  obtain ⟨U,hU,hdet,hU0,hUB,hker,S,H,Z,h⟩ :=
    PositiveLifting.simultaneous_positive_lifting B B' hB hB' f₀ f₁
  refine ⟨U,hU,hdet,hU0,hUB,hker,S,H,Z,h,?_⟩
  exact integer_aggregate B (U*B') hB hUB S H Z
    (fun c => (h c).1) (fun c => (h c).2.1)
    (fun c => (h c).2.2.1) (fun c => (h c).2.2.2.1) k l

section EqualSource
variable (A : Matrix n n ℕ) (A' : Matrix m m ℕ) (k l : n → ℕ)
  (T : C → Matrix (m ⊕ m) (n ⊕ n) ℕ)
  (D : Aggregate A A' (fun _ => k) (fun _ => l) T)

def sumCommon : Blocks (Sum.elim k l) →⋆ₐ[ℂ]
    Blocks (Sum.elim (total (channelLeft (fun _ => k) (fun _ => l) T))
      (total (channelRight (fun _ => k) (fun _ => l) T))) :=
  OrthogonalChannels.sumHom D.common D.common_orthogonal D.common_unit_sum

def sumLeft : Blocks (k+l) →⋆ₐ[ℂ]
    Blocks (total (channelLeft (fun _ => k) (fun _ => l) T) +
      total (channelRight (fun _ => k) (fun _ => l) T)) :=
  OrthogonalChannels.sumHom D.left D.left_orthogonal D.left_unit_sum

def sumRight : Blocks (k + A *ᵥ l) →⋆ₐ[ℂ]
    Blocks (total (channelLeft (fun _ => k) (fun _ => l) T) +
      A' *ᵥ total (channelRight (fun _ => k) (fun _ => l) T)) :=
  OrthogonalChannels.sumHom D.right D.right_orthogonal D.right_unit_sum

omit [DecidableEq C] in
theorem sum_first_square :
    (sumLeft A A' k l T D).comp (firstInclusion k l) =
    (firstInclusion (total (channelLeft (fun _ => k) (fun _ => l) T))
      (total (channelRight (fun _ => k) (fun _ => l) T))).comp (sumCommon A A' k l T D) := by
  apply StarAlgHom.ext
  intro a
  change (∑ c, D.left c (firstInclusion k l a)) = _
  change (∑ c, D.left c (firstInclusion k l a)) =
    firstInclusion _ _ (∑ c, D.common c a)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun c _ => D.first_square c a)

omit [DecidableEq C] in
theorem sum_second_square :
    (sumRight A A' k l T D).comp (secondInclusion A k l) =
    (secondInclusion A' (total (channelLeft (fun _ => k) (fun _ => l) T))
      (total (channelRight (fun _ => k) (fun _ => l) T))).comp (sumCommon A A' k l T D) := by
  apply StarAlgHom.ext
  intro a
  change (∑ c, D.right c (secondInclusion A k l a)) =
    secondInclusion A' _ _ (∑ c, D.common c a)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun c _ => D.second_square c a)

omit [DecidableEq C] in
theorem sum_isometries [Nonempty C] :
    Isometry (sumCommon A A' k l T D) ∧ Isometry (sumLeft A A' k l T D) ∧
      Isometry (sumRight A A' k l T D) := by
  let c : C := Classical.choice inferInstance
  exact ⟨NonUnitalStarAlgHom.isometry _ (OrthogonalChannels.sumHom_injective _ _ _ c
      (D.common_isometry c).injective),
    NonUnitalStarAlgHom.isometry _ (OrthogonalChannels.sumHom_injective _ _ _ c
      (D.left_isometry c).injective),
    NonUnitalStarAlgHom.isometry _ (OrthogonalChannels.sumHom_injective _ _ _ c
      (D.right_isometry c).injective)⟩
end EqualSource

end Suzuki

omit [Fintype t] [DecidableEq C] [DecidableEq s] [DecidableEq t] in
/-- Scaling the source channel dimensions by q scales its dimension
contribution by q, while its representation multiplicities stay unchanged. -/
theorem weighted_total_dimensions (w : s → ℕ) (M : C → Matrix t s ℕ) (q : C → ℕ) :
    total (fun c => targetSize (fun j => q c * w j) (M c)) =
      targetSize w (∑ c, fun i j => q c * M c i j) := by
  funext i
  simp only [total, targetSize, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro c _
  ring


section Weighted
variable {n m : Type*} [Fintype n] [Fintype m]

omit [DecidableEq C] [Fintype m] in
/-- The aggregate common dimensions are exactly (sum_c q_c T_c)(k,l).
In particular q_+=q_-=1 and q_0=q give the manuscript's noise-amplified sizes. -/
theorem weighted_common_dimensions (k l : n → ℕ)
    (T : C → Matrix (m ⊕ m) (n ⊕ n) ℕ) (q : C → ℕ) :
    Sum.elim
      (total (channelLeft (fun c i => q c * k i) (fun c i => q c * l i) T))
      (total (channelRight (fun c i => q c * k i) (fun c i => q c * l i) T)) =
    targetSize (Sum.elim k l) (∑ c, fun i j => q c * T c i j) := by
  have hw (c : C) : Sum.elim (fun i => q c * k i) (fun i => q c * l i) =
      fun j => q c * Sum.elim k l j := by
    funext j; cases j <;> rfl
  calc
    _ = total (fun c => targetSize
      (Sum.elim (fun i => q c * k i) (fun i => q c * l i)) (T c)) := by
      funext j; cases j <;> rfl
    _ = total (fun c => targetSize (fun j => q c * Sum.elim k l j) (T c)) := by
      simp only [hw]
    _ = _ := weighted_total_dimensions (Sum.elim k l) T q
end Weighted

end Suzuki.OrthogonalFiniteDiagrams

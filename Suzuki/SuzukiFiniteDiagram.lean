import Suzuki.MultiplicityComposition
import Suzuki.PositiveLifting
/-!
# Actual finite Suzuki diagrams from positive integer lifts

The integer identities from `MatrixDiagrams` are converted faithfully to
natural multiplicities. `Realization` contains actual complex unital star
homomorphisms, all seven isometries, explicit copy-and-unitary certificates
for T, S and R, and both literal commuting squares with the same common map.
The target common dimensions are exactly T times the source dimensions.

`finite_prescribed_diagrams` connects this construction directly to the
simultaneous positive lifting theorem for arbitrary additive maps between the
actual integer kernels and cokernels. Its finite family uses a common
unimodular presentation change but channelwise target dimensions. Orthogonal
inclusions into a sum of channel dimensions, graph-algebra identification,
K-theory functoriality, and the manuscript main theorem are not claimed here.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Suzuki.FiniteDiagram
open Matrix MultiplicityEmbeddings PositiveLifting
open scoped CStarAlgebra ComplexOrder

/-- Natural multiplicities, used only with explicit nonnegativity evidence. -/
def natMatrix {r s : Type*} (M : Matrix r s ℤ) : Matrix r s ℕ := fun i j => (M i j).toNat

theorem natMatrix_cast {r s : Type*} (M : Matrix r s ℤ) (hM : ∀ i j, 0 ≤ M i j) :
    (natMatrix M).map (Nat.castRingHom ℤ) = M := by
  ext i j
  exact Int.toNat_of_nonneg (hM i j)

theorem natMatrix_positive {r s : Type*} (M : Matrix r s ℤ) (hM : Positive M) :
    ∀ i j, 0 < natMatrix M i j := by
  intro i j
  have h := hM i j
  dsimp [natMatrix]
  omega

theorem natMatrix_product_eq {r s t u : Type*} [Fintype s] [Fintype t]
    (A : Matrix r s ℤ) (B : Matrix s u ℤ) (C : Matrix r t ℤ) (D : Matrix t u ℤ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hC : ∀ i j, 0 ≤ C i j) (hD : ∀ i j, 0 ≤ D i j)
    (h : A * B = C * D) : natMatrix A * natMatrix B = natMatrix C * natMatrix D := by
  have he : (natMatrix A * natMatrix B).map (Nat.castRingHom ℤ) =
      (natMatrix C * natMatrix D).map (Nat.castRingHom ℤ) := by
    rw [Matrix.map_mul, Matrix.map_mul, natMatrix_cast A hA,
      natMatrix_cast B hB, natMatrix_cast C hC, natMatrix_cast D hD, h]
  ext i j
  exact Nat.cast_injective (congrArg (fun M : Matrix r u ℤ => M i j) he)

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [Fintype n] in
theorem identity_nonnegative (i j : n) : 0 ≤ (1 : Matrix n n ℤ) i j := by
  simp only [Matrix.one_apply]
  split_ifs <;> omega

omit [Fintype n] in
theorem successor_positive (B : Matrix n n ℤ) (hB : Positive B) : Positive (1 + B) := by
  intro i j
  exact add_pos_of_nonneg_of_pos (identity_nonnegative i j) (hB i j)

omit [Fintype n] in
@[simp] theorem natMatrix_first :
    natMatrix (Matrix.fromCols (1 : Matrix n n ℤ) 1) = firstMultiplicity (ι := n) := by
  ext i j
  cases j <;> simp only [natMatrix, firstMultiplicity, Matrix.fromCols_apply_inl,
    Matrix.fromCols_apply_inr, Matrix.one_apply] <;> split_ifs <;> rfl

omit [Fintype n] in
@[simp] theorem natMatrix_second (B : Matrix n n ℤ) :
    natMatrix (Matrix.fromCols (1 : Matrix n n ℤ) (1 + B)) =
      secondMultiplicity (natMatrix (1 + B)) := by
  ext i j
  cases j with
  | inl j => simp only [natMatrix, secondMultiplicity, Matrix.fromCols_apply_inl,
      Matrix.one_apply]; split_ifs <;> rfl
  | inr j => rfl

theorem natural_first_square (B : Matrix n n ℤ) (S H Z : Matrix m n ℤ)
    (hS : Positive S) (hT : Positive (MatrixDiagrams.diagram B S H Z)) :
    firstMultiplicity * natMatrix (MatrixDiagrams.diagram B S H Z) =
      natMatrix S * firstMultiplicity := by
  have hI : ∀ i j, 0 ≤ (Matrix.fromCols (1 : Matrix n n ℤ) (1 : Matrix n n ℤ)) i j := by
    intro i j; cases j <;> exact identity_nonnegative _ _
  have hI' : ∀ i j, 0 ≤ (Matrix.fromCols (1 : Matrix m m ℤ) (1 : Matrix m m ℤ)) i j := by
    intro i j; cases j <;> exact identity_nonnegative _ _
  simpa only [natMatrix_first] using natMatrix_product_eq _ _ _ _ hI'
    (fun i j => (hT i j).le) (fun i j => (hS i j).le) hI
    (MatrixDiagrams.first_square B S H Z)

theorem natural_second_square (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (S H Z : Matrix m n ℤ) (hB : Positive B) (hB' : Positive B')
    (hchain : S * B = B' * H) (hT : Positive (MatrixDiagrams.diagram B S H Z))
    (hR : Positive (S + B' * Z)) :
    secondMultiplicity (natMatrix (1 + B')) * natMatrix (MatrixDiagrams.diagram B S H Z) =
      natMatrix (S + B' * Z) * secondMultiplicity (natMatrix (1 + B)) := by
  have hI : ∀ i j, 0 ≤ (Matrix.fromCols (1 : Matrix n n ℤ) (1+B)) i j := by
    intro i j; cases j with
    | inl j => exact identity_nonnegative _ _
    | inr j => exact (successor_positive B hB i j).le
  have hI' : ∀ i j, 0 ≤ (Matrix.fromCols (1 : Matrix m m ℤ) (1+B')) i j := by
    intro i j; cases j with
    | inl j => exact identity_nonnegative _ _
    | inr j => exact (successor_positive B' hB' i j).le
  simpa only [natMatrix_second] using natMatrix_product_eq _ _ _ _ hI'
    (fun i j => (hT i j).le) (fun i j => (hR i j).le) hI
    (MatrixDiagrams.second_square B B' S H Z hchain)

section Transport
variable {ι ν η ω : Type*} [Fintype ι] [Fintype ν] [Fintype η] [Fintype ω]
  [DecidableEq ι] [DecidableEq ν] [DecidableEq η]

/-- The actual copy representation with multiplicity M, up to explicitly
provided coordinate enumerations and actual target unitary conjugations. -/
def HasMultiplicity (k : ι → ℕ) (M : Matrix ω ι ℕ) (d : ω → ℕ)
    (φ : Blocks k →⋆ₐ[ℂ] Blocks d) : Prop :=
  ∃ (E : ∀ w, Slots k M w ≃ Fin (d w))
    (U : ∀ w, unitary (CStarMatrix (Fin (d w)) (Fin (d w)) ℂ)),
    ∀ a w, φ a w = (Unitary.conjStarAlgAut ℂ _ (U w))
      (CStarMatrix.reindexₐ ℂ ℂ (E w)
        (copyHom k (fun c : Copies M w => c.1) a))

omit [Fintype ω] in
/-- The copy-coordinate certificate entails the exact unital dimension equation. -/
theorem HasMultiplicity.dimensions (k : ι → ℕ) (M : Matrix ω ι ℕ) (d : ω → ℕ)
    (φ : Blocks k →⋆ₐ[ℂ] Blocks d) (h : HasMultiplicity k M d φ) :
    targetSize k M = d := by
  obtain ⟨E, U, hU⟩ := h
  funext w
  calc
    targetSize k M w = Fintype.card (Slots k M w) := (card_slots k M w).symm
    _ = Fintype.card (Fin (d w)) := Fintype.card_congr (E w)
    _ = d w := Fintype.card_fin (d w)

omit [Fintype ω] in
/-- The standard embedding itself has the displayed literal multiplicities. -/
theorem intoDimensions_hasMultiplicity (k : ι → ℕ) (M : Matrix ω ι ℕ)
    (d : ω → ℕ) (hd : targetSize k M = d) :
    HasMultiplicity k M d (intoDimensions k M d hd) := by
  subst d
  refine ⟨slotEquiv k M, fun _ => 1, ?_⟩
  intro a w
  change rowHom k M w a = (Unitary.conjStarAlgAut ℂ _ 1) (rowHom k M w a)
  rw [map_one]
  rfl

/-- The explicit unitary correction also certifies the prescribed multiplicity
of the corrected final map. -/
theorem exact_square_with_multiplicity (k : ι → ℕ)
    (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ)
    (M' : Matrix η ι ℕ) (N' : Matrix ω η ℕ)
    (hprod : N * M = N' * M') (hN' : ∀ s, ∃ w, 0 < N' w s) :
    ∃ ψ : Blocks (targetSize k M') →⋆ₐ[ℂ] Blocks (targetSize (targetSize k M) N),
      Isometry ψ ∧
      HasMultiplicity (targetSize k M') N' (targetSize (targetSize k M) N) ψ ∧
      ψ.comp (multiplicityHom k M') =
        (multiplicityHom (targetSize k M) N).comp (multiplicityHom k M) := by
  choose U hU using fun w => compositions_unitarily_conjugate k M N M' N' hprod w
  let castRow := fun w => CStarMatrix.reindexₐ ℂ ℂ
    (finCongr (compositionDimensionEq k M N M' N' hprod w))
  let aut := fun w => Unitary.conjStarAlgAut ℂ _ (U w)
  let F := fun w => (aut w).symm.toStarAlgHom.comp
    ((castRow w).toStarAlgHom.comp (rowHom (targetSize k M') N' w))
  let ψ : Blocks (targetSize k M') →⋆ₐ[ℂ] Blocks (targetSize (targetSize k M) N) :=
    { toFun := fun a w => F w a
      map_zero' := by funext w; exact map_zero (F w)
      map_one' := by funext w; exact map_one (F w)
      map_add' := by intro a b; funext w; exact map_add (F w) a b
      map_mul' := by intro a b; funext w; exact map_mul (F w) a b
      commutes' := by intro z; funext w; exact (F w).commutes z
      map_star' := by intro a; funext w; exact map_star (F w) a }
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply multiplicityHom_injective (targetSize k M') N' hN'
    funext w
    have h := congrArg (fun z : Blocks (targetSize (targetSize k M) N) => z w) hab
    exact (castRow w).injective ((aut w).symm.injective h)
  refine ⟨ψ, NonUnitalStarAlgHom.isometry _ hψ, ?_, ?_⟩
  · refine ⟨fun w => (slotEquiv (targetSize k M') N' w).trans
        (finCongr (compositionDimensionEq k M N M' N' hprod w)),
      fun w => star (U w), ?_⟩
    intro a w
    change (Unitary.conjStarAlgAut ℂ _ (U w)).symm _ = _
    rw [Unitary.conjStarAlgAut_symm]
    rfl
  · apply StarAlgHom.ext
    intro a
    funext w
    change (aut w).symm ((castRow w)
      (multiplicityHom (targetSize k M') N' (multiplicityHom k M' a) w)) = _
    rw [hU w a]
    change (aut w).symm ((aut w)
      (multiplicityHom (targetSize k M) N (multiplicityHom k M a) w)) = _
    exact (aut w).symm_apply_apply _

theorem exact_square_intoDimensions (k : ι → ℕ)
    (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ)
    (M' : Matrix η ι ℕ) (N' : Matrix ω η ℕ)
    (hprod : N * M = N' * M') (hN' : ∀ s, ∃ w, 0 < N' w s)
    (d : ν → ℕ) (e : η → ℕ) (f : ω → ℕ)
    (hd : targetSize k M = d) (he : targetSize k M' = e)
    (hf : targetSize d N = f) :
    ∃ ψ : Blocks e →⋆ₐ[ℂ] Blocks f, Isometry ψ ∧ HasMultiplicity e N' f ψ ∧
      ψ.comp (intoDimensions k M' e he) =
        (intoDimensions d N f hf).comp (intoDimensions k M d hd) := by
  subst d
  subst e
  subst f
  simpa only [intoDimensions] using exact_square_with_multiplicity k M N M' N' hprod hN'
end Transport

/-- The two target common-algebra block-size vectors, computed from T. -/
def targetLeft (k l : n → ℕ) (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) : m → ℕ :=
  fun i => targetSize (Sum.elim k l) T (Sum.inl i)
def targetRight (k l : n → ℕ) (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) : m → ℕ :=
  fun i => targetSize (Sum.elim k l) T (Sum.inr i)

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem targetDimensions_eq (k l : n → ℕ) (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) :
    targetSize (Sum.elim k l) T = Sum.elim (targetLeft k l T) (targetRight k l T) := by
  funext i
  cases i <;> rfl

/-- The one standard common-algebra connecting map, shared by both squares. -/
def commonMap (k l : n → ℕ) (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) :
    Blocks (Sum.elim k l) →⋆ₐ[ℂ] Blocks (Sum.elim (targetLeft k l T) (targetRight k l T)) :=
  intoDimensions _ T _ (targetDimensions_eq k l T)

/-- A pair of literal squares in actual finite products of complex matrix
algebras. All seven maps preserve the C*-norm. -/
structure Realization (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) (S R : Matrix m n ℕ) (k l : n → ℕ) where
  left : Blocks (k + l) →⋆ₐ[ℂ] Blocks (targetLeft k l T + targetRight k l T)
  right : Blocks (k + A *ᵥ l) →⋆ₐ[ℂ]
    Blocks (targetLeft k l T + A' *ᵥ targetRight k l T)
  left_multiplicity : HasMultiplicity (k+l) S (targetLeft k l T + targetRight k l T) left
  right_multiplicity : HasMultiplicity (k + A *ᵥ l) R
    (targetLeft k l T + A' *ᵥ targetRight k l T) right
  common_multiplicity : HasMultiplicity (Sum.elim k l) T
    (Sum.elim (targetLeft k l T) (targetRight k l T)) (commonMap k l T)
  common_isometry : Isometry (commonMap k l T)
  left_isometry : Isometry left
  right_isometry : Isometry right
  source_first_isometry : Isometry (firstInclusion k l)
  source_second_isometry : Isometry (secondInclusion A k l)
  target_first_isometry : Isometry (firstInclusion (targetLeft k l T) (targetRight k l T))
  target_second_isometry : Isometry (secondInclusion A' (targetLeft k l T) (targetRight k l T))
  first_square : left.comp (firstInclusion k l) =
    (firstInclusion (targetLeft k l T) (targetRight k l T)).comp (commonMap k l T)
  second_square : right.comp (secondInclusion A k l) =
    (secondInclusion A' (targetLeft k l T) (targetRight k l T)).comp (commonMap k l T)

/-- The first vertical embedding has exactly the S-prescribed dimensions. -/
theorem Realization.left_dimensions (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) (S R : Matrix m n ℕ) (k l : n → ℕ)
    (D : Realization A A' T S R k l) :
    targetSize (k+l) S = targetLeft k l T + targetRight k l T :=
  HasMultiplicity.dimensions _ _ _ _ D.left_multiplicity

/-- The second vertical embedding has exactly the R-prescribed dimensions. -/
theorem Realization.right_dimensions (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) (S R : Matrix m n ℕ) (k l : n → ℕ)
    (D : Realization A A' T S R k l) :
    targetSize (k + A *ᵥ l) R = targetLeft k l T + A' *ᵥ targetRight k l T :=
  HasMultiplicity.dimensions _ _ _ _ D.right_multiplicity

/-- Nonzero columns and the two multiplicity identities suffice. The two
vertical factor maps are constructed by the proved unitary correction. -/
theorem natural_realization (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) (S R : Matrix m n ℕ) (k l : n → ℕ)
    (hA : ∀ j, ∃ i, 0 < A i j) (hA' : ∀ j, ∃ i, 0 < A' i j)
    (hT : ∀ j, ∃ i, 0 < T i j) (hS : ∀ j, ∃ i, 0 < S i j)
    (hR : ∀ j, ∃ i, 0 < R i j)
    (hfirst : firstMultiplicity * T = S * firstMultiplicity)
    (hsecond : secondMultiplicity A' * T = R * secondMultiplicity A) :
    Nonempty (Realization A A' T S R k l) := by
  obtain ⟨left, hleft, hleftM, hleft_square⟩ := exact_square_intoDimensions (Sum.elim k l)
    T firstMultiplicity firstMultiplicity S hfirst hS
    (Sum.elim (targetLeft k l T) (targetRight k l T)) (k+l)
    (targetLeft k l T + targetRight k l T)
    (targetDimensions_eq k l T) (first_targetSize k l)
    (first_targetSize (targetLeft k l T) (targetRight k l T))
  obtain ⟨right, hright, hrightM, hright_square⟩ := exact_square_intoDimensions (Sum.elim k l)
    T (secondMultiplicity A') (secondMultiplicity A) R hsecond hR
    (Sum.elim (targetLeft k l T) (targetRight k l T)) (k + A *ᵥ l)
    (targetLeft k l T + A' *ᵥ targetRight k l T)
    (targetDimensions_eq k l T) (second_targetSize A k l)
    (second_targetSize A' (targetLeft k l T) (targetRight k l T))
  refine ⟨⟨left, right, hleftM, hrightM, intoDimensions_hasMultiplicity _ _ _ _,
    ?_, hleft, hright, ?_, ?_, ?_, ?_, hleft_square, hright_square⟩⟩
  · exact NonUnitalStarAlgHom.isometry _ (intoDimensions_injective _ T _ _ hT)
  · exact NonUnitalStarAlgHom.isometry _ (firstInclusion_injective k l)
  · exact NonUnitalStarAlgHom.isometry _ (secondInclusion_injective A k l hA)
  · exact NonUnitalStarAlgHom.isometry _ (firstInclusion_injective _ _)
  · exact NonUnitalStarAlgHom.isometry _ (secondInclusion_injective A' _ _ hA')


/-- The actual integer block formula and chain equation now produce both
literal squares. S, T and R are entrywise strictly positive integer matrices. -/
theorem integer_realization [Nonempty m]
    (B : Matrix n n ℤ) (B' : Matrix m m ℤ) (S H Z : Matrix m n ℤ)
    (hB : Positive B) (hB' : Positive B') (hchain : S * B = B' * H)
    (hS : Positive S) (hT : Positive (MatrixDiagrams.diagram B S H Z))
    (hR : Positive (S + B' * Z)) (k l : n → ℕ) :
    Nonempty (Realization (natMatrix (1+B)) (natMatrix (1+B'))
      (natMatrix (MatrixDiagrams.diagram B S H Z)) (natMatrix S) (natMatrix (S+B'*Z)) k l) := by
  let i : m := Classical.choice inferInstance
  apply natural_realization _ _ _ (natMatrix S) (natMatrix (S+B'*Z)) k l
  · intro j
    exact ⟨j, natMatrix_positive _ (successor_positive B hB) j j⟩
  · intro j
    exact ⟨j, natMatrix_positive _ (successor_positive B' hB') j j⟩
  · intro j
    exact ⟨Sum.inl i, natMatrix_positive _ hT (Sum.inl i) j⟩
  · intro j
    exact ⟨i, natMatrix_positive _ hS i j⟩
  · intro j
    exact ⟨i, natMatrix_positive _ hR i j⟩
  · exact natural_first_square B S H Z hS hT
  · exact natural_second_square B B' S H Z hB hB' hchain hT hR

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- Positive source dimensions and positive T give nonzero target common blocks.
A nonempty source is necessary here; it is not hidden in a matrix convention. -/
theorem target_dimensions_positive [Nonempty n]
    (k l : n → ℕ) (hk : ∀ j, 0 < k j)
    (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) (hT : ∀ i j, 0 < T i j) :
    (∀ i, 0 < targetLeft k l T i) ∧ (∀ i, 0 < targetRight k l T i) := by
  let j : n := Classical.choice inferInstance
  constructor
  · intro i
    exact targetSize_pos _ T (Sum.inl i) ⟨Sum.inl j, hT _ _, hk j⟩
  · intro i
    exact targetSize_pos _ T (Sum.inr i) ⟨Sum.inl j, hT _ _, hk j⟩

omit [DecidableEq n] [DecidableEq m] in
/-- Every source and target factor dimension is positive when the left common
sizes are positive; the right common sizes remain explicit in the hypothesis. -/
theorem all_dimensions_positive [Nonempty n]
    (k l : n → ℕ) (hk : ∀ j, 0 < k j) (hl : ∀ j, 0 < l j)
    (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) (hT : ∀ i j, 0 < T i j) :
    (∀ j, 0 < Sum.elim k l j) ∧
    (∀ j, 0 < (k+l) j) ∧ (∀ j, 0 < (k + A *ᵥ l) j) ∧
    (∀ i, 0 < Sum.elim (targetLeft k l T) (targetRight k l T) i) ∧
    (∀ i, 0 < (targetLeft k l T + targetRight k l T) i) ∧
    (∀ i, 0 < (targetLeft k l T + A' *ᵥ targetRight k l T) i) := by
  obtain ⟨hk', hl'⟩ := target_dimensions_positive k l hk T hT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; cases j with
    | inl j => exact hk j
    | inr j => exact hl j
  · intro j; exact Nat.add_pos_left (hk j) _
  · intro j; exact Nat.add_pos_left (hk j) _
  · intro i; cases i with
    | inl i => exact hk' i
    | inr i => exact hl' i
  · intro i; exact Nat.add_pos_left (hk' i) _
  · intro i; exact Nat.add_pos_left (hk' i) _

/-- The actual source and target block dimensions are all nonzero. -/
def PositiveDimensions (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (T : Matrix (m ⊕ m) (n ⊕ n) ℕ) (k l : n → ℕ) : Prop :=
    (∀ j, 0 < Sum.elim k l j) ∧
    (∀ j, 0 < (k+l) j) ∧ (∀ j, 0 < (k + A *ᵥ l) j) ∧
    (∀ i, 0 < Sum.elim (targetLeft k l T) (targetRight k l T) i) ∧
    (∀ i, 0 < (targetLeft k l T + targetRight k l T) i) ∧
    (∀ i, 0 < (targetLeft k l T + A' *ᵥ targetRight k l T) i)

/-- A finite family of arbitrary homomorphisms of the actual integer kernels
and cokernels produces actual finite diagrams, channel by channel, under the
same unimodular target change. Each channel here has its own T-defined target
sizes; this theorem does not assert an orthogonal sum into total channel sizes. -/
theorem simultaneous_realizations [Nontrivial m]
    {C : Type*} [Fintype C]
    (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (hB : Positive B) (hB' : Positive B')
    (f₀ : C → Cokernel B →ₗ[ℤ] Cokernel B')
    (f₁ : C → Kernel B →ₗ[ℤ] Kernel B') (k l : n → ℕ) :
    ∃ (U : Matrix m m ℤ) (hU : IsUnit U),
      U.det = 1 ∧ (∀ i j, 0 ≤ U i j) ∧ Positive (U * B') ∧
      Kernel (U * B') = Kernel B' ∧
      ∃ (S H Z : C → Matrix m n ℤ), ∀ c,
        S c * B = (U * B') * H c ∧
        Positive (S c) ∧ Positive (MatrixDiagrams.diagram B (S c) (H c) (Z c)) ∧
        Positive (S c + (U * B') * Z c) ∧
        (∀ x, quotient (U * B') (S c *ᵥ x) =
          targetCokernelEquiv B' U hU (f₀ c (quotient B x))) ∧
        (∀ x : Kernel B, H c *ᵥ x.val = (f₁ c x).val) ∧
        Nonempty (Realization (natMatrix (1+B)) (natMatrix (1+U*B'))
          (natMatrix (MatrixDiagrams.diagram B (S c) (H c) (Z c)))
          (natMatrix (S c)) (natMatrix (S c + (U*B')*Z c)) k l) := by
  obtain ⟨U, hU, hdet, hU0, hUB, hker, S, H, Z, h⟩ :=
    simultaneous_positive_lifting B B' hB hB' f₀ f₁
  refine ⟨U, hU, hdet, hU0, hUB, hker, S, H, Z, fun c => ?_⟩
  obtain ⟨hc, hS, hT, hR, h₀, h₁⟩ := h c
  exact ⟨hc, hS, hT, hR, h₀, h₁,
    integer_realization B (U*B') (S c) (H c) (Z c) hB hUB hc hS hT hR k l⟩


/-- The finite-size form: arbitrary additive group maps, positive source
sizes, source size at least one, and target size at least two. It returns the
actual diagrams together with positivity of every source and target block. -/
theorem finite_prescribed_diagrams {r r' q : ℕ} (hr : 0 < r) (hr' : 2 ≤ r')
    (B : Matrix (Fin r) (Fin r) ℤ) (B' : Matrix (Fin r') (Fin r') ℤ)
    (hB : Positive B) (hB' : Positive B')
    (f₀ : Fin q → Cokernel B →+ Cokernel B')
    (f₁ : Fin q → Kernel B →+ Kernel B')
    (k l : Fin r → ℕ) (hk : ∀ j, 0 < k j) (hl : ∀ j, 0 < l j) :
    ∃ (U : Matrix (Fin r') (Fin r') ℤ) (hU : IsUnit U),
      U.det = 1 ∧ (∀ i j, 0 ≤ U i j) ∧ Positive (U * B') ∧
      Kernel (U * B') = Kernel B' ∧
      ∃ (S H Z : Fin q → Matrix (Fin r') (Fin r) ℤ), ∀ c,
        S c * B = (U * B') * H c ∧
        Positive (S c) ∧ Positive (MatrixDiagrams.diagram B (S c) (H c) (Z c)) ∧
        Positive (S c + (U * B') * Z c) ∧
        (∀ x, quotient (U * B') (S c *ᵥ x) =
          targetCokernelEquiv B' U hU (f₀ c (quotient B x))) ∧
        (∀ x : Kernel B, H c *ᵥ x.val = (f₁ c x).val) ∧
        Nonempty (Realization (natMatrix (1+B)) (natMatrix (1+U*B'))
          (natMatrix (MatrixDiagrams.diagram B (S c) (H c) (Z c)))
          (natMatrix (S c)) (natMatrix (S c + (U*B')*Z c)) k l) ∧
        PositiveDimensions (natMatrix (1+B)) (natMatrix (1+U*B'))
          (natMatrix (MatrixDiagrams.diagram B (S c) (H c) (Z c))) k l := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let : Nontrivial (Fin r') := Fin.nontrivial_iff_two_le.mpr hr'
  obtain ⟨U, hU, hdet, hU0, hUB, hker, S, H, Z, h⟩ :=
    simultaneous_realizations B B' hB hB'
      (fun c => (f₀ c).toIntLinearMap) (fun c => (f₁ c).toIntLinearMap) k l
  refine ⟨U, hU, hdet, hU0, hUB, hker, S, H, Z, fun c => ?_⟩
  obtain ⟨hc, hS, hT, hR, h₀, h₁, hreal⟩ := h c
  exact ⟨hc, hS, hT, hR, h₀, h₁, hreal,
    all_dimensions_positive k l hk hl _ _ _ (natMatrix_positive _ hT)⟩

end Suzuki.FiniteDiagram

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

/-!
# Actual finite-dimensional multiplicity homomorphisms

The source and target are finite products of complex matrix C*-algebras,
with their genuine operator norms and the finite-product C*-norm.
Multiplicity counts are natural numbers and dimensions are explicit.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Suzuki.MultiplicityEmbeddings

open scoped CStarAlgebra ComplexOrder
open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The finite direct sum of complex full matrix algebras of sizes `k i`.
For finite index sets the direct sum is the product, with its C*-norm. -/
abbrev Blocks (k : ι → ℕ) := ∀ i, CStarMatrix (Fin (k i)) (Fin (k i)) ℂ

/-- A labelled collection of copies of source matrix blocks. -/
abbrev CopySlots (k : ι → ℕ) (label : κ → ι) := Σ c : κ, Fin (k (label c))

/-- The concrete block-diagonal representation containing the copies named
by `label`. This is unital even when some or all block sizes are zero. -/
def copyHom (k : ι → ℕ) (label : κ → ι) :
    Blocks k →⋆ₐ[ℂ] CStarMatrix (CopySlots k label) (CopySlots k label) ℂ where
  toFun a := CStarMatrix.ofMatrix (Matrix.blockDiagonal' fun c =>
    CStarMatrix.ofMatrix.symm (a (label c)))
  map_zero' := Matrix.blockDiagonal'_zero
  map_one' := Matrix.blockDiagonal'_one
  map_add' a b := by
    exact Matrix.blockDiagonal'_add
      (fun c => CStarMatrix.ofMatrix.symm (a (label c)))
      (fun c => CStarMatrix.ofMatrix.symm (b (label c)))
  map_mul' a b := by
    exact Matrix.blockDiagonal'_mul
      (fun c => CStarMatrix.ofMatrix.symm (a (label c)))
      (fun c => CStarMatrix.ofMatrix.symm (b (label c)))
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change Matrix.blockDiagonal' (fun c => z • (1 : Matrix (Fin (k (label c))) (Fin (k (label c))) ℂ)) = z • 1
    calc
      _ = z • Matrix.blockDiagonal' (1 : ∀ c : κ,
          Matrix (Fin (k (label c))) (Fin (k (label c))) ℂ) :=
        Matrix.blockDiagonal'_smul z (1 : ∀ c : κ,
          Matrix (Fin (k (label c))) (Fin (k (label c))) ℂ)
      _ = z • 1 := by rw [Matrix.blockDiagonal'_one]
  map_star' a := by
    exact (Matrix.blockDiagonal'_conjTranspose
      (fun c => CStarMatrix.ofMatrix.symm (a (label c)))).symm

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem copyHom_same (k : ι → ℕ) (label : κ → ι) (a : Blocks k)
    (c : κ) (i j : Fin (k (label c))) :
    copyHom k label a ⟨c, i⟩ ⟨c, j⟩ = a (label c) i j :=
  Matrix.blockDiagonal'_apply_eq
    (fun c => CStarMatrix.ofMatrix.symm (a (label c))) c i j

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem copyHom_different (k : ι → ℕ) (label : κ → ι) (a : Blocks k)
    {c d : κ} (h : c ≠ d) (i : Fin (k (label c))) (j : Fin (k (label d))) :
    copyHom k label a ⟨c, i⟩ ⟨d, j⟩ = 0 :=
  Matrix.blockDiagonal'_apply_ne
    (fun c => CStarMatrix.ofMatrix.symm (a (label c))) i j h

omit [Fintype ι] [DecidableEq ι] in
/-- Every source block occurring among the labelled copies makes the
block-diagonal representation faithful. -/
theorem copyHom_injective (k : ι → ℕ) (label : κ → ι)
    (hlabel : Function.Surjective label) : Function.Injective (copyHom k label) := by
  intro a b hab
  funext s
  obtain ⟨c, rfl⟩ := hlabel s
  ext i j
  have h := congrArg (fun M : CStarMatrix (CopySlots k label) (CopySlots k label) ℂ =>
    M ⟨c, i⟩ ⟨c, j⟩) hab
  simpa only [copyHom_same] using h

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The individual copies occurring in one target row of a multiplicity matrix. -/
abbrev Copies (M : Matrix ν ι ℕ) (v : ν) := Σ i : ι, Fin (M v i)

/-- Actual matrix coordinates in target block `v`. -/
abbrev Slots (k : ι → ℕ) (M : Matrix ν ι ℕ) (v : ν) :=
  CopySlots k (fun c : Copies M v => c.1)

/-- The target dimension required by unitality. -/
def targetSize (k : ι → ℕ) (M : Matrix ν ι ℕ) (v : ν) : ℕ := ∑ i, M v i * k i

omit [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
/-- The actual target coordinate set has exactly the prescribed dimension. -/
theorem card_slots (k : ι → ℕ) (M : Matrix ν ι ℕ) (v : ν) :
    Fintype.card (Slots k M v) = targetSize k M v := by
  simp [Slots, CopySlots, Copies, targetSize, Fintype.card_sigma, Fintype.sum_sigma]

/-- A fixed enumeration of the target matrix coordinates. -/
def slotEquiv (k : ι → ℕ) (M : Matrix ν ι ℕ) (v : ν) :
    Slots k M v ≃ Fin (targetSize k M v) :=
  (Fintype.equivFin _).trans (finCongr (card_slots k M v))

/-- The actual row representation, after enumerating its coordinates. -/
def rowHom (k : ι → ℕ) (M : Matrix ν ι ℕ) (v : ν) :
    Blocks k →⋆ₐ[ℂ] CStarMatrix (Fin (targetSize k M v)) (Fin (targetSize k M v)) ℂ :=
  (CStarMatrix.reindexₐ ℂ ℂ (slotEquiv k M v)).toStarAlgHom.comp
    (copyHom k (fun c : Copies M v => c.1))

/-- The actual unital star homomorphism with the prescribed nonnegative
integer multiplicity matrix. Target dimensions are `M` times source dimensions. -/
def multiplicityHom (k : ι → ℕ) (M : Matrix ν ι ℕ) :
    Blocks k →⋆ₐ[ℂ] Blocks (targetSize k M) where
  toFun a v := rowHom k M v a
  map_zero' := by funext v; exact map_zero (rowHom k M v)
  map_one' := by funext v; exact map_one (rowHom k M v)
  map_add' a b := by funext v; exact map_add (rowHom k M v) a b
  map_mul' a b := by funext v; exact map_mul (rowHom k M v) a b
  commutes' z := by funext v; exact (rowHom k M v).commutes z
  map_star' a := by funext v; exact map_star (rowHom k M v) a

omit [Fintype ν] [DecidableEq ν] in
/-- The prescribed copies are literal submatrices of the output. -/
theorem multiplicityHom_copy (k : ι → ℕ) (M : Matrix ν ι ℕ) (a : Blocks k)
    (v : ν) (s : ι) (t : Fin (M v s)) (i j : Fin (k s)) :
    multiplicityHom k M a v
      (slotEquiv k M v ⟨⟨s, t⟩, i⟩) (slotEquiv k M v ⟨⟨s, t⟩, j⟩) = a s i j := by
  change Matrix.reindex (slotEquiv k M v) (slotEquiv k M v)
    (copyHom k (fun c : Copies M v => c.1) a)
      (slotEquiv k M v ⟨⟨s, t⟩, i⟩) (slotEquiv k M v ⟨⟨s, t⟩, j⟩) = _
  change copyHom k (fun c : Copies M v => c.1) a
    ((slotEquiv k M v).symm (slotEquiv k M v ⟨⟨s, t⟩, i⟩))
    ((slotEquiv k M v).symm (slotEquiv k M v ⟨⟨s, t⟩, j⟩)) = _
  simp only [Equiv.symm_apply_apply, copyHom_same]

omit [Fintype ν] [DecidableEq ν] in
/-- Nonzero columns suffice for injectivity; rows need not be strictly positive. -/
theorem multiplicityHom_injective (k : ι → ℕ) (M : Matrix ν ι ℕ)
    (hM : ∀ s, ∃ v, 0 < M v s) : Function.Injective (multiplicityHom k M) := by
  intro a b hab
  funext s
  obtain ⟨v, hv⟩ := hM s
  let t : Fin (M v s) := ⟨0, hv⟩
  ext i j
  have h := congrArg (fun f : Blocks (targetSize k M) => f v
    (slotEquiv k M v ⟨⟨s, t⟩, i⟩) (slotEquiv k M v ⟨⟨s, t⟩, j⟩)) hab
  simpa only [multiplicityHom_copy] using h

omit [DecidableEq ν] in
/-- These faithful maps preserve the actual C*-norm. -/
theorem multiplicityHom_isometry (k : ι → ℕ) (M : Matrix ν ι ℕ)
    (hM : ∀ s, ∃ v, 0 < M v s) : Isometry (multiplicityHom k M) :=
  NonUnitalStarAlgHom.isometry _ (multiplicityHom_injective k M hM)

omit [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
/-- The target block is nonzero whenever its row contains a positive
multiplicity for a nonzero source block. -/
theorem targetSize_pos (k : ι → ℕ) (M : Matrix ν ι ℕ) (v : ν)
    (hrow : ∃ s, 0 < M v s ∧ 0 < k s) : 0 < targetSize k M v := by
  obtain ⟨s, hs, hk⟩ := hrow
  exact lt_of_lt_of_le (Nat.mul_pos hs hk)
    (Finset.single_le_sum (fun i _ => Nat.zero_le (M v i * k i)) (Finset.mem_univ s))

omit [DecidableEq ν] in
/-- Strictly positive multiplicities and a nonempty target give an actual
isometric embedding. -/
theorem multiplicityHom_isometry_of_positive [Nonempty ν]
    (k : ι → ℕ) (M : Matrix ν ι ℕ) (hM : ∀ v s, 0 < M v s) :
    Isometry (multiplicityHom k M) := by
  let v : ν := Classical.choice inferInstance
  exact multiplicityHom_isometry k M (fun s => ⟨v, hM v s⟩)

/-- Transport the constructed homomorphism to any explicitly equal list of
target block sizes. Only the necessary unital dimension equation is supplied. -/
def intoDimensions (k : ι → ℕ) (M : Matrix ν ι ℕ) (d : ν → ℕ)
    (hd : targetSize k M = d) : Blocks k →⋆ₐ[ℂ] Blocks d :=
  hd ▸ multiplicityHom k M

omit [Fintype ν] [DecidableEq ν] in
/-- Exact target-dimension transport preserves injectivity. -/
theorem intoDimensions_injective (k : ι → ℕ) (M : Matrix ν ι ℕ) (d : ν → ℕ)
    (hd : targetSize k M = d) (hM : ∀ s, ∃ v, 0 < M v s) :
    Function.Injective (intoDimensions k M d hd) := by
  subst d
  exact multiplicityHom_injective k M hM

/-- The actual permutation unitary implementing a coordinate reordering. -/
def permutationUnitary (e : Equiv.Perm κ) : unitary (CStarMatrix κ κ ℂ) :=
  ⟨CStarMatrix.ofMatrix ((e⁻¹).permMatrix ℂ), by
    change ((e⁻¹).permMatrix ℂ).conjTranspose * (e⁻¹).permMatrix ℂ = 1 ∧
      (e⁻¹).permMatrix ℂ * ((e⁻¹).permMatrix ℂ).conjTranspose = 1
    simp [← Matrix.permMatrix_mul]⟩

/-- Reindexing a complex matrix is conjugation by an actual unitary matrix. -/
theorem reindex_eq_unitary_conjugation (e : Equiv.Perm κ) (a : CStarMatrix κ κ ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ e a =
      (permutationUnitary e : CStarMatrix κ κ ℂ) * a *
        star (permutationUnitary e : CStarMatrix κ κ ℂ) := by
  change Matrix.reindex e e (CStarMatrix.ofMatrix.symm a) =
    (e⁻¹).permMatrix ℂ * CStarMatrix.ofMatrix.symm a * ((e⁻¹).permMatrix ℂ).conjTranspose
  rw [Matrix.conjTranspose_permMatrix, inv_inv,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The common inclusion matrix `[I I]` in manuscript Section 2. -/
def firstMultiplicity : Matrix ι (ι ⊕ ι) ℕ := Matrix.fromCols 1 1

/-- The common inclusion matrix `[I A]` in manuscript Section 2. -/
def secondMultiplicity (A : Matrix ι ι ℕ) : Matrix ι (ι ⊕ ι) ℕ := Matrix.fromCols 1 A

/-- The exact unital block-size equation for `[I I]`. -/
theorem first_targetSize (k l : ι → ℕ) :
    targetSize (Sum.elim k l) (firstMultiplicity (ι := ι)) = k + l := by
  change Matrix.fromCols (1 : Matrix ι ι ℕ) 1 *ᵥ Sum.elim k l = k + l
  rw [Matrix.fromCols_mulVec_sumElim, Matrix.one_mulVec, Matrix.one_mulVec]

/-- The exact unital block-size equation for `[I A]`. -/
theorem second_targetSize (A : Matrix ι ι ℕ) (k l : ι → ℕ) :
    targetSize (Sum.elim k l) (secondMultiplicity A) = k + A *ᵥ l := by
  change Matrix.fromCols (1 : Matrix ι ι ℕ) A *ᵥ Sum.elim k l = k + A *ᵥ l
  rw [Matrix.fromCols_mulVec_sumElim, Matrix.one_mulVec]

/-- The actual first common-algebra inclusion into blocks of size `k+l`. -/
def firstInclusion (k l : ι → ℕ) :
    Blocks (Sum.elim k l) →⋆ₐ[ℂ] Blocks (k + l) :=
  intoDimensions _ firstMultiplicity _ (first_targetSize k l)

/-- The actual second common-algebra inclusion into blocks of size `k+A*l`. -/
def secondInclusion (A : Matrix ι ι ℕ) (k l : ι → ℕ) :
    Blocks (Sum.elim k l) →⋆ₐ[ℂ] Blocks (k + A *ᵥ l) :=
  intoDimensions _ (secondMultiplicity A) _ (second_targetSize A k l)

/-- The first common-algebra map is an embedding. -/
theorem firstInclusion_injective (k l : ι → ℕ) :
    Function.Injective (firstInclusion k l) := by
  apply intoDimensions_injective
  intro s
  cases s with
  | inl s => exact ⟨s, by simp [firstMultiplicity]⟩
  | inr s => exact ⟨s, by simp [firstMultiplicity]⟩

/-- The no-zero-column hypothesis from Section 2 makes the second
common-algebra map an embedding. -/
theorem secondInclusion_injective (A : Matrix ι ι ℕ) (k l : ι → ℕ)
    (hA : ∀ s, ∃ v, 0 < A v s) : Function.Injective (secondInclusion A k l) := by
  apply intoDimensions_injective
  intro s
  cases s with
  | inl s => exact ⟨s, by simp [secondMultiplicity]⟩
  | inr s => simpa only [secondMultiplicity, Matrix.fromCols_apply_inr] using hA s

section CopyMatching

variable {η : Type*} [Fintype η] [DecidableEq η]

omit [Fintype ι] [DecidableEq ι] in
/-- A bijection of copy labels preserving source blocks gives a literal
reindexing equality of their concrete representations. -/
theorem exists_copy_reindex_of_label_equiv (k : ι → ℕ)
    (f : κ → ι) (g : η → ι) (e : κ ≃ η) (he : f = g ∘ e) :
    ∃ E : CopySlots k f ≃ CopySlots k g, ∀ a : Blocks k,
      CStarMatrix.reindexₐ ℂ ℂ E (copyHom k f a) = copyHom k g a := by
  subst f
  let E : CopySlots k (g ∘ e) ≃ CopySlots k g :=
    Equiv.sigmaCongrLeft (β := fun c : η => Fin (k (g c))) e
  refine ⟨E, ?_⟩
  intro a
  apply CStarMatrix.ext
  intro r s
  obtain ⟨⟨c, i⟩, rfl⟩ := E.surjective r
  obtain ⟨⟨d, j⟩, rfl⟩ := E.surjective s
  change copyHom k (g ∘ e) a (E.symm (E ⟨c, i⟩)) (E.symm (E ⟨d, j⟩)) =
    copyHom k g a ⟨e c, i⟩ ⟨e d, j⟩
  simp only [Equiv.symm_apply_apply]
  by_cases hcd : c = d
  · subst d
    rw [copyHom_same, copyHom_same]
    rfl
  · rw [copyHom_different k (g ∘ e) a hcd,
      copyHom_different k g a (e.injective.ne hcd)]

omit [Fintype ι] in
/-- Equality of the finite multiplicity counts constructs a coordinate
bijection, with a proved equality of the actual block representations. -/
theorem exists_copy_reindex_of_counts (k : ι → ℕ) (f : κ → ι) (g : η → ι)
    (hcount : ∀ s, Fintype.card {c // f c = s} = Fintype.card {d // g d = s}) :
    ∃ E : CopySlots k f ≃ CopySlots k g, ∀ a : Blocks k,
      CStarMatrix.reindexₐ ℂ ℂ E (copyHom k f a) = copyHom k g a := by
  let fiber (s : ι) : {c // f c = s} ≃ {d // g d = s} :=
    Fintype.equivOfCardEq (hcount s)
  let e : κ ≃ η := Equiv.ofFiberEquiv fiber
  apply exists_copy_reindex_of_label_equiv k f g e
  funext c
  exact (Equiv.ofFiberEquiv_map fiber c).symm

omit [Fintype ι] in
/-- Equal multiplicities in two explicitly enumerated block representations
produce an actual permutation unitary conjugating them. No unitary or
representation-classification hypothesis is supplied. -/
theorem copies_unitarily_conjugate_of_counts (k : ι → ℕ) (f : κ → ι) (g : η → ι)
    (hcount : ∀ s, Fintype.card {c // f c = s} = Fintype.card {d // g d = s})
    {d : ℕ} (u : CopySlots k f ≃ Fin d) (v : CopySlots k g ≃ Fin d) :
    ∃ U : unitary (CStarMatrix (Fin d) (Fin d) ℂ), ∀ a : Blocks k,
      CStarMatrix.reindexₐ ℂ ℂ v (copyHom k g a) =
        (U : CStarMatrix (Fin d) (Fin d) ℂ) *
          CStarMatrix.reindexₐ ℂ ℂ u (copyHom k f a) *
            star (U : CStarMatrix (Fin d) (Fin d) ℂ) := by
  obtain ⟨E, hE⟩ := exists_copy_reindex_of_counts k f g hcount
  let e : Equiv.Perm (Fin d) := u.symm.trans (E.trans v)
  refine ⟨permutationUnitary e, ?_⟩
  intro a
  rw [← reindex_eq_unitary_conjugation, ← hE a]
  apply CStarMatrix.ext
  intro i j
  change copyHom k f a (E.symm (v.symm i)) (E.symm (v.symm j)) =
    copyHom k f a (u.symm (e.symm i)) (u.symm (e.symm j))
  simp [e]

end CopyMatching

omit [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
/-- Positive integer multiplicities from the lifting theorem have an exact
natural-number realization; no negative entry is silently retained. -/
theorem natCast_toNat_multiplicity (M : Matrix ν ι ℤ) (hM : ∀ v s, 0 ≤ M v s) :
    (fun v s => ((M v s).toNat : ℤ)) = M := by
  funext v s
  exact Int.toNat_of_nonneg (hM v s)

omit [DecidableEq ν] in
/-- The genuine C*-embedding associated to a strictly positive integer
multiplicity matrix, as produced by the positive lifting theorem. -/
theorem positive_integer_multiplicity_isometry [Nonempty ν]
    (k : ι → ℕ) (M : Matrix ν ι ℤ) (hM : ∀ v s, 0 < M v s) :
    Isometry (multiplicityHom k (fun v s => (M v s).toNat)) := by
  apply multiplicityHom_isometry_of_positive
  intro v s
  have := hM v s
  omega

section Composition

variable {ω : Type*} [Fintype ω] [DecidableEq ω]

omit [DecidableEq ι] [DecidableEq ν] [Fintype ω] [DecidableEq ω] in
/-- The explicit unital dimension equations are compatible with composition
of multiplicity matrices. -/
theorem targetSize_comp (k : ι → ℕ) (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ) :
    targetSize (targetSize k M) N = targetSize k (N * M) := by
  change N *ᵥ (M *ᵥ k) = (N * M) *ᵥ k
  exact Matrix.mulVec_mulVec k N M

omit [Fintype ω] [DecidableEq ω] in
/-- Each ordered pair of copies in two successive actual homomorphisms
recovers its source matrix block literally. -/
theorem composition_copy (k : ι → ℕ) (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ)
    (a : Blocks k) (w : ω) (v : ν) (s : ι)
    (t : Fin (N w v)) (u : Fin (M v s)) (i j : Fin (k s)) :
    multiplicityHom (targetSize k M) N (multiplicityHom k M a) w
      (slotEquiv (targetSize k M) N w ⟨⟨v, t⟩, slotEquiv k M v ⟨⟨s, u⟩, i⟩⟩)
      (slotEquiv (targetSize k M) N w ⟨⟨v, t⟩, slotEquiv k M v ⟨⟨s, u⟩, j⟩⟩) =
      a s i j := by
  rw [multiplicityHom_copy, multiplicityHom_copy]

end Composition

end Suzuki.MultiplicityEmbeddings

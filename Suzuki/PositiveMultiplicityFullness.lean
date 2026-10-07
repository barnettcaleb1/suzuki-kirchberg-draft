import Suzuki.SuzukiFiniteDiagram
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# The finite-constituent noise channel is full

This proves the manuscript's finite-dimensional ideal step for the actual
operator-norm matrix algebras. Strictly positive multiplicities make every
target-row representation faithful. Hence a nonzero evaluated element has
nonzero image in every target block and generates the entire target ideal.
The statement includes the actual permutation/unitary conjugations in a
`HasMultiplicity` certificate. Connecting it to the coefficient evaluation
and the aggregate nonunital noise channel remains a separate obligation.
-/

noncomputable section
namespace Suzuki.PositiveMultiplicityFullness
open Suzuki.MultiplicityEmbeddings Suzuki.FiniteDiagram
open scoped CStarAlgebra

variable {ι ν : Type*} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

omit [Fintype ν] [DecidableEq ν] in
/-- Every target block is faithful when its entire multiplicity row is positive. -/
theorem row_injective (k : ι → ℕ) (M : Matrix ν ι ℕ) (d : ν → ℕ)
    (φ : Blocks k →⋆ₐ[ℂ] Blocks d) (hφ : HasMultiplicity k M d φ)
    (v : ν) (hM : ∀ s, 0 < M v s) : Function.Injective (fun a => φ a v) := by
  obtain ⟨E,U,hU⟩ := hφ
  intro a b hab
  apply copyHom_injective k (fun c : Copies M v => c.1)
    (fun s => ⟨⟨s,⟨0,hM s⟩⟩,rfl⟩)
  apply (CStarMatrix.reindexₐ ℂ ℂ (E v)).injective
  apply (Unitary.conjStarAlgAut ℂ _ (U v)).injective
  exact (hU a v).symm.trans (hab.trans (hU b v))

omit [Fintype ν] [DecidableEq ν] in
/-- This detects the actual element, not merely the channel's unit support. -/
theorem image_block_ne_zero (k : ι → ℕ) (M : Matrix ν ι ℕ) (d : ν → ℕ)
    (φ : Blocks k →⋆ₐ[ℂ] Blocks d) (hφ : HasMultiplicity k M d φ)
    (hM : ∀ v s, 0 < M v s) {a : Blocks k} (ha : a ≠ 0) (v : ν) : φ a v ≠ 0 := by
  intro hz
  apply ha
  apply row_injective k M d φ hφ v (hM v)
  simpa only [map_zero, Pi.zero_apply] using hz

/-- A concrete nonunital ring map inserting one full matrix block. -/
def matrixBlock (d : ν → ℕ) (v : ν) : Matrix (Fin (d v)) (Fin (d v)) ℂ →ₙ+* Blocks d where
  toFun x := Pi.single v (CStarMatrix.ofMatrixRingEquiv x)
  map_zero' := by simp
  map_add' x y := by rw [map_add, Pi.single_add]
  map_mul' x y := by
    funext w
    by_cases h : w = v
    · subst w; simp
    · simp [Pi.single_eq_of_ne h]

omit [Fintype ν] in
/-- Multiplication by the central block unit extracts that block inside an ideal. -/
theorem single_mem (d : ν → ℕ) (I : TwoSidedIdeal (Blocks d))
    {x : Blocks d} (hx : x ∈ I) (v : ν) : Pi.single v (x v) ∈ I := by
  have he : Pi.single v (x v) = (Pi.single v (1 : CStarMatrix (Fin (d v)) (Fin (d v)) ℂ)) * x := by
    funext w
    by_cases h : w = v
    · subst w; simp
    · simp [Pi.single_eq_of_ne h]
  rw [he]
  exact I.mul_mem_left _ _ hx

/-- An element nonzero in every block generates the full finite product as an
algebraic two-sided ideal, so in particular as a closed C*-ideal. -/
theorem ideal_eq_top_of_blocks (d : ν → ℕ) (I : TwoSidedIdeal (Blocks d))
    {x : Blocks d} (hx : x ∈ I) (hne : ∀ v, x v ≠ 0) : I = ⊤ := by
  have hunit : ∀ v : ν, Pi.single v (1 : CStarMatrix (Fin (d v)) (Fin (d v)) ℂ) ∈ I := by
    intro v
    obtain ⟨i,j,hij⟩ : ∃ i j, x v i j ≠ 0 := by
      by_contra! h
      apply hne v
      ext i j
      exact h i j
    let : Nonempty (Fin (d v)) := ⟨i⟩
    let J := I.comap (matrixBlock d v)
    have hmem : CStarMatrix.ofMatrix.symm (x v) ∈ J := by
      apply (TwoSidedIdeal.mem_comap (matrixBlock d v)).mpr
      exact single_mem d I hx v
    have hn : CStarMatrix.ofMatrix.symm (x v) ≠ 0 := by
      intro hz
      exact hij (congrArg (fun m : Matrix (Fin (d v)) (Fin (d v)) ℂ => m i j) hz)
    have hone := IsSimpleRing.one_mem_of_ne_zero_mem J hn hmem
    have hone' : matrixBlock d v 1 ∈ I := (TwoSidedIdeal.mem_comap (matrixBlock d v)).mp hone
    have he : matrixBlock d v 1 = Pi.single v (1 : CStarMatrix (Fin (d v)) (Fin (d v)) ℂ) := rfl
    exact he ▸ hone'
  apply I.eq_top
  have he : (∑ v : ν, Pi.single v (1 : CStarMatrix (Fin (d v)) (Fin (d v)) ℂ)) = (1 : Blocks d) := by
    funext w
    simp
  rw [← he]
  apply Finset.sum_induction
  · exact fun _ _ ha hb => I.add_mem ha hb
  · exact I.zero_mem
  · exact fun v _ => hunit v

/-- The actual positive finite-dimensional multiplicity image is full. -/
theorem image_full (k : ι → ℕ) (M : Matrix ν ι ℕ) (d : ν → ℕ)
    (φ : Blocks k →⋆ₐ[ℂ] Blocks d) (hφ : HasMultiplicity k M d φ)
    (hM : ∀ v s, 0 < M v s) {a : Blocks k} (ha : a ≠ 0)
    (I : TwoSidedIdeal (Blocks d)) (hI : φ a ∈ I) : I = ⊤ :=
  ideal_eq_top_of_blocks d I hI (image_block_ne_zero k M d φ hφ hM ha)

/-- Fullness of a concrete constant element persists in any unital ambient
algebra. This is the form needed after extracting a noise branch in the limit. -/
theorem ambient_ideal_eq_top {A : Type*} [CStarAlgebra A] (d : ν → ℕ)
    (constant : Blocks d →⋆ₐ[ℂ] A) (I : TwoSidedIdeal A)
    {x : Blocks d} (hx : constant x ∈ I) (hne : ∀ v, x v ≠ 0) : I = ⊤ := by
  let J := I.comap constant.toRingHom
  have hJ : J = ⊤ := ideal_eq_top_of_blocks d J
    ((TwoSidedIdeal.mem_comap constant.toRingHom).mpr hx) hne
  have hunit : (1 : Blocks d) ∈ J := hJ ▸ TwoSidedIdeal.mem_top _
  have hunit' : constant 1 ∈ I := (TwoSidedIdeal.mem_comap constant.toRingHom).mp hunit
  apply I.eq_top
  simpa only [map_one] using hunit'

end Suzuki.PositiveMultiplicityFullness

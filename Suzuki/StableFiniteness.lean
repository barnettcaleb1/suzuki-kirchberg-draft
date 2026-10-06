import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NoncommRing

/-!
# A faithful trace implies stable finiteness

This file proves the algebraic implication used in Section 7 of the manuscript.
It does not assert the existence of a trace on the proposed limit algebras.
-/

namespace Suzuki
namespace StableFiniteness

variable {A : Type*} [Ring A] [StarRing A]

/-- The real-valued additive part of a faithful positive trace.
A faithful tracial state on a complex C*-algebra supplies these properties. -/
structure FaithfulTrace (A : Type*) [Ring A] [StarRing A] where
  toAddMonoidHom : A →+ ℝ
  cyclic : ∀ a b, toAddMonoidHom (a * b) = toAddMonoidHom (b * a)
  nonnegative : ∀ a, 0 ≤ toAddMonoidHom (star a * a)
  faithful : ∀ a, toAddMonoidHom (star a * a) = 0 → a = 0

/-- Finiteness: an isometry cannot have a nonzero defect projection. -/
theorem isometry_unitary (τ : FaithfulTrace A) (v : A) (hv : star v * v = 1) :
    v * star v = 1 := by
  let d : A := 1 - v * star v
  have he : (v * star v) * (v * star v) = v * star v := by
    calc
      (v * star v) * (v * star v) = v * (star v * v) * star v := by
        simp only [mul_assoc]
      _ = v * star v := by rw [hv]; simp
  have hstar : star d = d := by simp [d]
  have hd : d * d = d := by
    dsimp [d]
    noncomm_ring [he]
  have ht : τ.toAddMonoidHom d = 0 := by
    simp only [d, map_sub]
    rw [τ.cyclic v (star v), hv]
    exact sub_self _
  have hz : d = 0 := τ.faithful d (by rw [hstar, hd, ht])
  exact (sub_eq_zero.mp hz).symm

variable {n : Type*} [Fintype n]

/-- The unnormalized matrix extension of a trace. -/
def matrixTrace (τ : FaithfulTrace A) (M : Matrix n n A) : ℝ :=
  ∑ i, τ.toAddMonoidHom (M i i)

/-- Cyclicity persists over matrices with noncommutative entries. -/
theorem matrixTrace_cyclic (τ : FaithfulTrace A) (M N : Matrix n n A) :
    matrixTrace τ (M * N) = matrixTrace τ (N * M) := by
  simp only [matrixTrace, Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact τ.cyclic _ _

/-- Positivity of the matrix extension on squares. -/
theorem matrixTrace_nonnegative (τ : FaithfulTrace A) (M : Matrix n n A) :
    0 ≤ matrixTrace τ (M.conjTranspose * M) := by
  simp only [matrixTrace, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => τ.nonnegative _

/-- Faithfulness of the matrix extension is proved entry by entry. -/
theorem matrixTrace_faithful (τ : FaithfulTrace A) (M : Matrix n n A)
    (h : matrixTrace τ (M.conjTranspose * M) = 0) : M = 0 := by
  simp only [matrixTrace, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum] at h
  have hi (i : n) : (∑ j, τ.toAddMonoidHom (star (M j i) * M j i)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => τ.nonnegative (M j i))).mp h i
      (Finset.mem_univ i)
  ext i j
  apply τ.faithful
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => τ.nonnegative (M k j))).mp (hi j) i (Finset.mem_univ i)

variable [DecidableEq n]

/-- A faithful trace on the original algebra gives a faithful trace on every matrix ring. -/
def amplification (τ : FaithfulTrace A) : FaithfulTrace (Matrix n n A) where
  toAddMonoidHom := {
    toFun := matrixTrace τ
    map_zero' := by simp [matrixTrace]
    map_add' := by intro M N; simp [matrixTrace, Finset.sum_add_distrib] }
  cyclic := matrixTrace_cyclic τ
  nonnegative := matrixTrace_nonnegative τ
  faithful := matrixTrace_faithful τ

/-- The concrete matrix definition of stable finiteness used in the manuscript. -/
def IsStablyFinite (A : Type*) [Ring A] [StarRing A] : Prop :=
  ∀ (k : ℕ) (v : Matrix (Fin k) (Fin k) A),
    v.conjTranspose * v = 1 → v * v.conjTranspose = 1

omit [Fintype n] [DecidableEq n] in
/-- A faithful trace rules out proper isometries in every matrix algebra. -/
theorem faithful_trace_stablyFinite (τ : FaithfulTrace A) : IsStablyFinite A := by
  intro k v hv
  exact isometry_unitary (amplification τ) v hv

end StableFiniteness
end Suzuki

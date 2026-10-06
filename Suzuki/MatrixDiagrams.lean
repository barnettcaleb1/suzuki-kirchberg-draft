import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Abel

/-!
# Algebraic identities for the proposed Suzuki construction

These are universal identities for finite integer matrices, corresponding to
Section 3 of `paper.tex`. They do not construct C*-algebras or prove the main
Kirchberg-algebra claim. All hypotheses are explicit.
-/

namespace Suzuki
namespace MatrixDiagrams

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The block multiplicity matrix in equation (1), with `A = 1 + B`. -/
def diagram (B : Matrix n n ℤ) (S H Z : Matrix m n ℤ) :
    Matrix (m ⊕ m) (n ⊕ n) ℤ :=
  fromBlocks (S - Z) (S - H - Z * (1 + B)) Z (H + Z * (1 + B))

/-- The first commuting square in equation (2). -/
theorem first_square (B : Matrix n n ℤ) (S H Z : Matrix m n ℤ) :
    fromCols (1 : Matrix m m ℤ) 1 * diagram B S H Z =
      S * fromCols (1 : Matrix n n ℤ) 1 := by
  simp only [diagram, fromCols_mul_fromBlocks, Matrix.one_mul,
    mul_fromCols, Matrix.mul_one]
  congr 1 <;> abel

/-- The second commuting square in equation (2), under the chain equation. -/
theorem second_square (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (S H Z : Matrix m n ℤ) (h : S * B = B' * H) :
    fromCols (1 : Matrix m m ℤ) (1 + B') * diagram B S H Z =
      (S + B' * Z) * fromCols (1 : Matrix n n ℤ) (1 + B) := by
  unfold diagram
  rw [fromCols_mul_fromBlocks, mul_fromCols]
  congr 1
  · simp only [Matrix.one_mul, Matrix.add_mul, Matrix.mul_one]
    abel
  · simp only [Matrix.one_mul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_one, Matrix.mul_assoc]
    rw [h]
    abel

omit [Fintype m] [DecidableEq m] in
/-- The induced action on the kernel representatives `(-y,y)`. -/
theorem kernel_action (B : Matrix n n ℤ) (S H Z : Matrix m n ℤ)
    (y : n → ℤ) (hy : B *ᵥ y = 0) :
    diagram B S H Z *ᵥ Sum.elim (-y) y =
      Sum.elim (-(H *ᵥ y)) (H *ᵥ y) := by
  have hAy : (1 + B) *ᵥ y = y := by
    simp [Matrix.add_mulVec, hy]
  have hZA : (Z * (1 + B)) *ᵥ y = Z *ᵥ y := by
    rw [← Matrix.mulVec_mulVec, hAy]
  simp only [diagram, fromBlocks_mulVec, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Matrix.mulVec_neg,
    Matrix.sub_mulVec, Matrix.add_mulVec, hZA]
  congr 1 <;> abel

omit [DecidableEq n] [DecidableEq m] in
/-- A chain-homotopy adjustment preserves the chain equation. -/
theorem adjusted_chain (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (S H W : Matrix m n ℤ) (h : S * B = B' * H) :
    (S + B' * W) * B = B' * (H + W * B) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h]

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- That adjustment has no effect on the map on the source kernel. -/
theorem adjusted_kernel (B : Matrix n n ℤ) (H W : Matrix m n ℤ)
    (y : n → ℤ) (hy : B *ᵥ y = 0) :
    (H + W * B) *ᵥ y = H *ᵥ y := by
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hy]
  simp

end MatrixDiagrams
end Suzuki

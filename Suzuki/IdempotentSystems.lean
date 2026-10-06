import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

/-!
# Constant idempotent inverse systems

These additive-group lemmas justify the elementary sequence calculations in
Section 6 of `paper.tex`. They do not identify any group with a Kasparov group,
construct KK-theory, or establish the analytic Milnor exact sequence.
-/

namespace Suzuki
namespace IdempotentSystems

variable {G : Type*} [AddCommGroup G]

/-- Compatible sequences for a fixed idempotent are constant fixed-point sequences. -/
theorem compatible_iff_constant_fixed (p : G →+ G) (hp : ∀ x, p (p x) = p x)
    (x : ℕ → G) :
    (∀ n, p (x (n + 1)) = x n) ↔
      p (x 0) = x 0 ∧ ∀ n, x n = x 0 := by
  constructor
  · intro hx
    have hfix (n : ℕ) : p (x n) = x n := by
      calc
        p (x n) = p (p (x (n + 1))) := congrArg p (hx n).symm
        _ = p (x (n + 1)) := hp _
        _ = x n := hx n
    refine ⟨hfix 0, ?_⟩
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      calc
        x (n + 1) = p (x (n + 1)) := (hfix (n + 1)).symm
        _ = x n := hx n
        _ = x 0 := ih
  · rintro ⟨hfix, hconst⟩ n
    rw [hconst (n + 1), hconst n, hfix]

/-- Recursive correction used to solve `a n - p (a (n+1)) = b n`. -/
def correction (p : G →+ G) (b : ℕ → G) : ℕ → G
  | 0 => 0
  | n + 1 => correction p b n - p (b n)

/-- All correction terms lie in the fixed-point subgroup. -/
theorem correction_fixed (p : G →+ G) (hp : ∀ x, p (p x) = p x)
    (b : ℕ → G) (n : ℕ) : p (correction p b n) = correction p b n := by
  induction n with
  | zero => simp [correction]
  | succ n ih => simp only [correction, map_sub, ih, hp]

/-- The `1 - shift` map is surjective for any idempotent additive endomorphism.
No countability hypothesis on `G` is used. -/
theorem one_sub_shift_surjective (p : G →+ G) (hp : ∀ x, p (p x) = p x) :
    Function.Surjective (fun a : ℕ → G => fun n => a n - p (a (n + 1))) := by
  intro b
  let a : ℕ → G := fun n => b n - p (b n) + correction p b n
  refine ⟨a, ?_⟩
  funext n
  have hpa : p (a (n + 1)) = correction p b (n + 1) := by
    simp only [a, map_add, map_sub, hp, sub_self, zero_add,
      correction_fixed p hp]
  change a n - p (a (n + 1)) = b n
  rw [hpa]
  change (b n - p (b n) + correction p b n) -
    (correction p b n - p (b n)) = b n
  abel

end IdempotentSystems
end Suzuki

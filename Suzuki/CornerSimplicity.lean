import Suzuki.SimpleFullness

/-!
# Simplicity of nonzero projection corners

The ambient norm-closed simplicity hypothesis gives a finite expression for
one using any nonzero corner element. Compression turns that expression into
one in the corner ideal. No abstract Morita-invariance assertion is assumed.
-/

noncomputable section

namespace Suzuki.CornerSimplicity

open CommonCorner

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

/-- A corner element absorbs the two internal support projections. -/
theorem compress_sandwich (a b : A) (x : Corner hp) :
    compress hp (a * (x : A) * b) = compress hp a * x * compress hp b := by
  apply Subtype.ext
  change p * (a * (x : A) * b) * p = (p * a * p) * (x : A) * (p * b * p)
  calc
    _ = (p * a) * (x : A) * (b * p) := by simp only [mul_assoc]
    _ = (p * a) * (p * (x : A) * p) * (b * p) := by
      rw [left_support hp x, right_support hp x]
    _ = _ := by simp only [mul_assoc]

/-- Every two-sided ideal of a projection corner is trivial when the ambient
unital C⋆-algebra is simple. Closedness of the corner ideal is not required. -/
theorem ideals_trivial
    (hsimple : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤)
    (I : TwoSidedIdeal (Corner hp)) : I = ⊥ ∨ I = ⊤ := by
  classical
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ x ∈ I, x ≠ 0 := by
    by_contra! hz
    apply hI
    apply le_antisymm _ bot_le
    intro x hx
    simpa only [TwoSidedIdeal.mem_bot] using hz x hx
  obtain ⟨x, hx, hne⟩ := hex
  have hneA : (x : A) ≠ 0 := fun h => hne (Subtype.ext h)
  obtain ⟨n, a, b, hab⟩ :=
    (SimpleFullness.full_of_nonzero hsimple hneA).exists_sum_one
  have hs : (∑ i, compress hp (a i * (x : A) * b i)) = (1 : Corner hp) := by
    rw [← map_sum, hab]
    apply Subtype.ext
    change p * 1 * p = p
    simpa only [mul_one] using hp.isIdempotentElem.eq
  apply I.eq_top
  rw [← hs]
  have hterm (i : Fin n) : compress hp (a i * (x : A) * b i) ∈ I := by
    rw [compress_sandwich]
    exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hx)
  exact sum_mem (fun i _ => hterm i)

/-- The corner is nontrivial precisely when its unit projection is nonzero. -/
theorem nontrivial (hne : p ≠ 0) : Nontrivial (Corner hp) := by
  apply nontrivial_of_ne (1 : Corner hp) 0
  intro h
  apply hne
  exact congrArg Subtype.val h

/-- The concrete corner of a nonzero projection satisfies the target's exact
closed-ideal simplicity predicate. -/
theorem isSimple (B : Target.UnitalAlgebra) (hB : Target.IsSimple B)
    {q : B} (hq : IsStarProjection q) (hne : q ≠ 0) :
    Target.IsSimple ⟨Corner hq, inferInstance⟩ :=
  ⟨nontrivial hq hne, fun I _ => ideals_trivial hq hB.2 I⟩

end Suzuki.CornerSimplicity

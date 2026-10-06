import Suzuki.Target
import Suzuki.FullProjectionFrame

/-!
# Nonzero projections in simple algebras are full

This connects the manuscript's simplicity hypothesis to the ideal-theoretic
fullness used by the proved common-full-corner theorem. The closure is the
actual norm closure of an actual two-sided ideal.
-/

namespace Suzuki.SimpleFullness

variable {A : Type*} [CStarAlgebra A]

/-- The norm closure of an actual two-sided ideal remains a two-sided ideal. -/
def closedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal A := by
  let G : AddSubgroup A := {
    carrier := I
    zero_mem' := I.zero_mem
    add_mem' := fun ha hb => I.add_mem ha hb
    neg_mem' := fun ha => I.neg_mem ha }
  refine TwoSidedIdeal.mk' (closure (I : Set A))
    (subset_closure I.zero_mem) ?_ ?_ ?_ ?_
  · intro a b ha hb
    exact G.topologicalClosure.add_mem ha hb
  · intro a ha
    exact G.topologicalClosure.neg_mem ha
  · intro a b hb
    exact (show Set.MapsTo (a * ·) (I : Set A) (I : Set A) from
      fun x hx => I.mul_mem_left a x hx).closure (continuous_const.mul continuous_id) hb
  · intro a b ha
    exact (show Set.MapsTo (· * b) (I : Set A) (I : Set A) from
      fun x hx => I.mul_mem_right x b hx).closure (continuous_id.mul continuous_const) ha

theorem coe_closedIdeal (I : TwoSidedIdeal A) :
    (closedIdeal I : Set A) = closure (I : Set A) := by
  ext x
  change x - 0 ∈ closure (I : Set A) ↔ x ∈ closure (I : Set A)
  rw [sub_zero]

theorem closedIdeal_isClosed (I : TwoSidedIdeal A) : IsClosed (closedIdeal I : Set A) := by
  rw [coe_closedIdeal]
  exact isClosed_closure

/-- Every nonzero element in a simple C⋆-algebra generates a dense ideal.
The projection specialization is the fullness needed for the corner argument. -/
theorem full_of_nonzero
    (hsimple : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤)
    {p : A} (hp : p ≠ 0) : CommonCorner.FullProjection p := by
  let I := TwoSidedIdeal.span ({p} : Set A)
  have hmem : p ∈ closedIdeal I := by
    rw [← SetLike.mem_coe, coe_closedIdeal]
    exact subset_closure (TwoSidedIdeal.subset_span (Set.mem_singleton p))
  rcases hsimple (closedIdeal I) (closedIdeal_isClosed I) with hbot | htop
  · have hz : p = 0 := by simpa [hbot] using hmem
    exact (hp hz).elim
  · intro x
    have hm : x ∈ closedIdeal I := by simp [htop]
    rwa [← SetLike.mem_coe, coe_closedIdeal] at hm

/-- A nonzero projection of a simple bundled algebra admits an actual finite frame. -/
theorem exists_frame (A : Target.UnitalAlgebra) (hA : Target.IsSimple A)
    {p : A} (hp : IsStarProjection p) (hne : p ≠ 0) :
    ∃ n, Nonempty (CommonCorner.Frame hp n) :=
  (full_of_nonzero hA.2 hne).exists_frame hp

end Suzuki.SimpleFullness

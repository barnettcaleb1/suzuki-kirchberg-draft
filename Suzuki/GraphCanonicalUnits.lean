import Suzuki.GraphAmalgamInverse

/-! Canonical scalar matrix units for the two finite graph factors, and their
transport through arbitrary actual star homomorphisms. The representation
reconstructed from these units is proved equal to the original factor map.
No existence, faithfulness or compatibility of common inclusions is assumed. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace Suzuki.GraphCanonicalUnits
open GraphAmalgamInverse
universe u
variable {N V : Type} [Fintype N] [Fintype V] [DecidableEq N] [DecidableEq V]
  (label : N → V)

/-- Actual scalar matrix units of the finite product, with zero off-block entries. -/
def scalarUnit (i j : N) : MatrixUnits.Blocks (label := label) := fun _ =>
  CStarMatrix.ofMatrix (fun a b => if a.val = i ∧ b.val = j then (1 : ℂ) else 0)

omit [Fintype N] [Fintype V] [DecidableEq V] in
theorem scalarUnit_star (i j : N) : star (scalarUnit label i j) = scalarUnit label j i := by
  funext v
  apply CStarMatrix.ext
  intro a b
  change star (if b.val = i ∧ a.val = j then (1 : ℂ) else 0) =
    if a.val = j ∧ b.val = i then (1 : ℂ) else 0
  by_cases h : b.val = i ∧ a.val = j
  · simp [h]
  · have hn : ¬ (a.val = j ∧ b.val = i) := fun hh => h ⟨hh.2, hh.1⟩
    simp [h, hn]

omit [Fintype V] in
theorem scalarUnit_mul (i j r s : N) (hij : label i = label j) (hrs : label r = label s) :
    scalarUnit label i j * scalarUnit label r s = if j = r then scalarUnit label i s else 0 := by
  funext v
  apply CStarMatrix.ext
  intro a b
  change (∑ c : MatrixUnits.Block (label := label) v,
    (if a.val = i ∧ c.val = j then (1 : ℂ) else 0) *
    (if c.val = r ∧ b.val = s then (1 : ℂ) else 0)) =
      (if j = r then scalarUnit label i s else 0) v a b
  by_cases hv : label j = v
  · let c₀ : MatrixUnits.Block (label := label) v := ⟨j, hv⟩
    rw [Finset.sum_eq_single c₀]
    · by_cases hjr : j = r
      · subst r
        rw [if_pos rfl]
        change (if a.val = i ∧ j = j then (1 : ℂ) else 0) *
          (if j = j ∧ b.val = s then (1 : ℂ) else 0) = if a.val = i ∧ b.val = s then 1 else 0
        by_cases ha : a.val = i <;> by_cases hb : b.val = s <;> simp [ha, hb]
      · rw [if_neg hjr]
        change (if a.val = i ∧ j = j then (1 : ℂ) else 0) *
          (if j = r ∧ b.val = s then (1 : ℂ) else 0) = 0
        simp [hjr]
    · intro c _ hc
      have hcv : c.val ≠ j := fun h => hc (Subtype.ext h)
      simp only [hcv, and_false, if_false, zero_mul]
    · simp
  · have hz : (∑ c : MatrixUnits.Block (label := label) v,
        (if a.val = i ∧ c.val = j then (1 : ℂ) else 0) *
        (if c.val = r ∧ b.val = s then (1 : ℂ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      have hcv : c.val ≠ j := fun h => hv (h ▸ c.property)
      simp only [hcv, and_false, if_false, zero_mul]
    rw [hz]
    by_cases hjr : j = r
    · subst r
      rw [if_pos rfl]
      have hai : a.val ≠ i := fun h => hv (hij.symm.trans (h ▸ a.property))
      change (0 : ℂ) = if a.val = i ∧ b.val = s then 1 else 0
      simp [hai]
    · simp [hjr]

omit [Fintype V] [DecidableEq V] in
theorem scalarUnit_sum : (∑ i : N, scalarUnit label i i) = 1 := by
  funext v
  apply CStarMatrix.ext
  intro a b
  have hsum : (∑ i : N, scalarUnit label i i) v a b =
      ∑ i : N, scalarUnit label i i v a b := by
    let ev : MatrixUnits.Blocks (label := label) →+ ℂ :=
      { toFun := fun f => f v a b
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact map_sum ev _ _
  rw [hsum]
  change (∑ i : N, if a.val = i ∧ b.val = i then (1 : ℂ) else 0) = if a = b then 1 else 0
  rw [Finset.sum_eq_single a.val]
  · by_cases hab : a = b
    · subst b; simp
    · have hv : b.val ≠ a.val := fun h => hab (Subtype.ext h.symm)
      simp [hab, hv]
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

def canonical : MatrixUnits label (MatrixUnits.Blocks (label := label)) where
  unit := scalarUnit label
  star_eq i j _ := scalarUnit_star label i j
  mul_eq := scalarUnit_mul label
  sum_diag := scalarUnit_sum label

variable {C : Type u} [CStarAlgebra C]
/-- The actual canonical matrix units transported through a factor homomorphism. -/
def ofHom (f : MatrixUnits.Blocks (label := label) →⋆ₐ[ℂ] C) : MatrixUnits label C where
  unit i j := f (scalarUnit label i j)
  star_eq i j _ := by rw [← map_star, scalarUnit_star]
  mul_eq i j r s hij hrs := by
    rw [← map_mul, scalarUnit_mul label i j r s hij hrs]
    split_ifs <;> simp only [map_zero]
  sum_diag := by rw [← map_sum, scalarUnit_sum, map_one]


omit [Fintype N] [Fintype V] in
/-- Canonical same-block units are the literal coordinate matrices of the product. -/
theorem scalarUnit_single (v : V) (i j : MatrixUnits.Block (label := label) v) :
    scalarUnit label i.val j.val = Pi.single v (CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ))) := by
  funext w
  by_cases hw : w = v
  · subst w
    rw [Pi.single_eq_same]
    apply CStarMatrix.ext
    intro a b
    change (if a.val = i.val ∧ b.val = j.val then (1 : ℂ) else 0) =
      if i = a ∧ j = b then (1 : ℂ) else 0
    have ha : a.val = i.val ↔ i = a := ⟨fun h => Subtype.ext h.symm, fun h => by rw [h]⟩
    have hb : b.val = j.val ↔ j = b := ⟨fun h => Subtype.ext h.symm, fun h => by rw [h]⟩
    simp only [ha, hb]
  · rw [Pi.single_eq_of_ne hw]
    apply CStarMatrix.ext
    intro a b
    change (if a.val = i.val ∧ b.val = j.val then (1 : ℂ) else 0) = 0
    have ha : a.val ≠ i.val := fun h => hw (a.property.symm.trans ((congrArg label h).trans i.property))
    simp [ha]

/-- Reconstruct a finite product from its actual coordinate matrix units. -/
theorem reconstruction (a : MatrixUnits.Blocks (label := label)) :
    (∑ v, ∑ i : MatrixUnits.Block (label := label) v,
      ∑ j : MatrixUnits.Block (label := label) v, (a v i j) • scalarUnit label i.val j.val) = a := by
  funext w
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single w]
  · apply CStarMatrix.ext
    intro r s
    let ev : CStarMatrix (MatrixUnits.Block (label := label) w) (MatrixUnits.Block (label := label) w) ℂ →+ ℂ :=
      { toFun := fun M => M r s
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change ev (∑ i, ∑ j, (a w i j) • scalarUnit label i.val j.val w) = _
    simp only [map_sum]
    change (∑ i : MatrixUnits.Block (label := label) w,
      ∑ j : MatrixUnits.Block (label := label) w,
        (a w i j) * (if r.val = i.val ∧ s.val = j.val then (1 : ℂ) else 0)) = _
    have hi (i : MatrixUnits.Block (label := label) w) : r.val = i.val ↔ i = r :=
      ⟨fun h => Subtype.ext h.symm, fun h => by rw [h]⟩
    have hj (j : MatrixUnits.Block (label := label) w) : s.val = j.val ↔ j = s :=
      ⟨fun h => Subtype.ext h.symm, fun h => by rw [h]⟩
    let vals : MatrixUnits.Block (label := label) w → MatrixUnits.Block (label := label) w → ℂ := fun i j => a w i j
    change (∑ i, ∑ j, vals i j * (if r.val = i.val ∧ s.val = j.val then (1 : ℂ) else 0)) = vals r s
    simp only [hi, hj, mul_ite, mul_one, mul_zero]
    simp [ite_and]
  · intro v _ hv
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [scalarUnit_single label v i j, Pi.single_eq_of_ne hv.symm, smul_zero]
  · simp

/-- Canonical units retain the entire given factor homomorphism. -/
theorem representation_ofHom (f : MatrixUnits.Blocks (label := label) →⋆ₐ[ℂ] C) :
    (ofHom label f).representation = f := by
  apply StarAlgHom.ext
  intro a
  change (∑ v, (ofHom label f).blockHom v (a v)) = f a
  simp only [MatrixUnits.blockHom_apply]
  change (∑ v, ∑ i : MatrixUnits.Block (label := label) v,
    ∑ j : MatrixUnits.Block (label := label) v, (a v i j) • f (scalarUnit label i.val j.val)) = f a
  calc
    _ = f (∑ v, ∑ i : MatrixUnits.Block (label := label) v,
        ∑ j : MatrixUnits.Block (label := label) v, (a v i j) • scalarUnit label i.val j.val) := by
      simp only [map_sum, map_smul]
    _ = f a := congrArg f (reconstruction label a)

end Suzuki.GraphCanonicalUnits

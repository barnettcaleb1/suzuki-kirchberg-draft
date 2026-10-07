import Suzuki.GraphFiniteAmalgam
import Suzuki.MultiplicityEmbeddings

/-!
# The manuscript's actual common inclusions and graph equivalence

The common algebra is the finite product of the P and Q matrix blocks. The first
inclusion has one copy of each in its vertex block. The second has its P copy and
one Q copy for each incoming edge, labelled by that edge's source. Coordinate
bijections construct actual unital star homomorphisms and prove all P/Q images.
Compatibility is equivalent to the previously explicit CommonEntries equations.
The universal amalgam therefore is the actual weighted graph corner, assuming
only positive weights and no sinks. Both common inclusions are proved injective.

For A(v,w) edges w to v, copy counts and actual row reindexings identify these
maps with the prior [I I] and [I A] multiplicity homomorphisms. The universal norm
and both inverse maps are imported proved constructions, not theorem parameters.
No published input or UCT premise occurs in this module. The exact K-class and
subsequent coefficient/limit/unit correspondence remain open. Scalar graph
identification is in Type 0; common-map calculations permit target universe u.
-/
noncomputable section
open scoped CStarAlgebra ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Suzuki.GraphCommonInclusions
open WeightedGraphAmalgam MultiplicityEmbeddings
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (source target : E → V) (k l : V → ℕ)
abbrev Common := Blocks (Sum.elim k l)
abbrev Copies (v : V) := Unit ⊕ {e : E // target e = v}
def label (v : V) : Copies target v → V ⊕ V
  | .inl _ => .inl v
  | .inr e => .inr (source e)
def coordEquiv (v : V) :
    CopySlots (Sum.elim k l) (label source target v) ≃
      BlockIndex (source := source) (target := target) k l v where
  toFun x := match x with
    | ⟨.inl _, a⟩ => ⟨.inl ⟨v,a⟩, rfl⟩
    | ⟨.inr e, a⟩ => ⟨.inr ⟨e,a⟩, e.property⟩
  invFun x := match x with
    | ⟨.inl ⟨w,a⟩, h⟩ => ⟨.inl (), h ▸ a⟩
    | ⟨.inr ⟨e,a⟩, h⟩ => ⟨.inr ⟨e,h⟩, a⟩
  left_inv := by rintro ⟨(_|⟨e,h⟩),a⟩ <;> rfl
  right_inv := by
    rintro ⟨(⟨w,a⟩|⟨e,a⟩),h⟩
    · change w = v at h; subst w; rfl
    · rfl

def secondRow (v : V) : Common k l →⋆ₐ[ℂ]
    CStarMatrix (BlockIndex (source := source) (target := target) k l v)
      (BlockIndex (source := source) (target := target) k l v) ℂ :=
  (CStarMatrix.reindexₐ ℂ ℂ (coordEquiv source target k l v)).toStarAlgHom.comp
    (copyHom (Sum.elim k l) (label source target v))
def second : Common k l →⋆ₐ[ℂ] Factor (source := source) (target := target) k l where
  toFun a v := secondRow source target k l v a
  map_zero' := by funext v; exact map_zero _
  map_one' := by funext v; exact map_one _
  map_add' a b := by funext v; exact map_add _ a b
  map_mul' a b := by funext v; exact map_mul _ a b
  commutes' z := by funext v; exact (secondRow source target k l v).commutes z
  map_star' a := by funext v; exact map_star _ a

def firstCoordEquiv (v : V) :
    CopySlots (Sum.elim k l) (fun c : Bool => if c then Sum.inl v else Sum.inr v) ≃
      FirstBlockIndex k l v where
  toFun x := match x with
    | ⟨true, a⟩ => ⟨.inl ⟨v,a⟩, rfl⟩
    | ⟨false, a⟩ => ⟨.inr ⟨v,a⟩, rfl⟩
  invFun x := match x with
    | ⟨.inl ⟨w,a⟩, h⟩ => ⟨true, h ▸ a⟩
    | ⟨.inr ⟨w,a⟩, h⟩ => ⟨false, h ▸ a⟩
  left_inv := by rintro ⟨(_|_),a⟩ <;> rfl
  right_inv := by
    rintro ⟨(⟨w,a⟩|⟨w,a⟩),h⟩ <;> change w = v at h <;> subst w <;> rfl

def firstRow (v : V) : Common k l →⋆ₐ[ℂ]
    CStarMatrix (FirstBlockIndex k l v) (FirstBlockIndex k l v) ℂ :=
  (CStarMatrix.reindexₐ ℂ ℂ (firstCoordEquiv k l v)).toStarAlgHom.comp
    (copyHom (Sum.elim k l) (fun c : Bool => if c then Sum.inl v else Sum.inr v))
def first : Common k l →⋆ₐ[ℂ] FirstFactor k l where
  toFun a v := firstRow k l v a
  map_zero' := by funext v; exact map_zero _
  map_one' := by funext v; exact map_one _
  map_add' a b := by funext v; exact map_add _ a b
  map_mul' a b := by funext v; exact map_mul _ a b
  commutes' z := by funext v; exact (firstRow k l v).commutes z
  map_star' a := by funext v; exact map_star _ a


theorem first_pullback (a : Common k l) (v : V)
    (i j : CopySlots (Sum.elim k l) (fun c : Bool => if c then Sum.inl v else Sum.inr v)) :
    first k l a v (firstCoordEquiv k l v i) (firstCoordEquiv k l v j) =
      copyHom (Sum.elim k l) (fun c : Bool => if c then Sum.inl v else Sum.inr v) a i j := by
  change copyHom _ _ a ((firstCoordEquiv k l v).symm (firstCoordEquiv k l v i))
    ((firstCoordEquiv k l v).symm (firstCoordEquiv k l v j)) = _
  simp only [Equiv.symm_apply_apply]
theorem second_pullback (a : Common k l) (v : V)
    (i j : CopySlots (Sum.elim k l) (label source target v)) :
    second source target k l a v (coordEquiv source target k l v i) (coordEquiv source target k l v j) =
      copyHom (Sum.elim k l) (label source target v) a i j := by
  change copyHom _ _ a ((coordEquiv source target k l v).symm (coordEquiv source target k l v i))
    ((coordEquiv source target k l v).symm (coordEquiv source target k l v j)) = _
  simp only [Equiv.symm_apply_apply]

def unit (v : V ⊕ V) (a b : Fin (Sum.elim k l v)) : Common k l :=
  Pi.single v (CStarMatrix.ofMatrix (Matrix.single a b (1 : ℂ)))

theorem first_P (v : V) (a b : Fin (k v)) :
    first k l (unit k l (.inl v) a b) =
      GraphCanonicalUnits.scalarUnit (coordVertex k l)
        (GraphAmalgamInverse.pCoord k l v a) (GraphAmalgamInverse.pCoord k l v b) := by
  funext w
  apply CStarMatrix.ext
  intro i j
  obtain ⟨⟨c,i⟩, rfl⟩ := (firstCoordEquiv k l w).surjective i
  obtain ⟨⟨d,j⟩, rfl⟩ := (firstCoordEquiv k l w).surjective j
  rw [first_pullback]
  cases c <;> cases d
  · rw [copyHom_same]
    simp [unit, GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.pCoord]
  · rw [copyHom_different _ _ _ (by decide)]
    simp [GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.pCoord]
  · rw [copyHom_different _ _ _ (by decide)]
    simp [GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.pCoord]
  · rw [copyHom_same]
    by_cases h : w = v
    · subst w
      simp [unit, GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.pCoord,
        Matrix.single_apply, eq_comm]
    · simp [unit, h, GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.pCoord]

theorem first_Q (v : V) (a b : Fin (l v)) :
    first k l (unit k l (.inr v) a b) =
      GraphCanonicalUnits.scalarUnit (coordVertex k l)
        (GraphAmalgamInverse.qCoord k l v a) (GraphAmalgamInverse.qCoord k l v b) := by
  funext w
  apply CStarMatrix.ext
  intro i j
  obtain ⟨⟨c,i⟩, rfl⟩ := (firstCoordEquiv k l w).surjective i
  obtain ⟨⟨d,j⟩, rfl⟩ := (firstCoordEquiv k l w).surjective j
  rw [first_pullback]
  cases c <;> cases d
  · rw [copyHom_same]
    by_cases h : w = v
    · subst w
      simp [unit, GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.qCoord,
        Matrix.single_apply, eq_comm]
    · simp [unit, h, GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.qCoord]
  · rw [copyHom_different _ _ _ (by decide)]
    simp [GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.qCoord]
  · rw [copyHom_different _ _ _ (by decide)]
    simp [GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.qCoord]
  · rw [copyHom_same]
    simp [unit, GraphCanonicalUnits.scalarUnit, firstCoordEquiv, GraphAmalgamInverse.qCoord]


theorem second_P (v : V) (a b : Fin (k v)) :
    second source target k l (unit k l (.inl v) a b) =
      GraphCanonicalUnits.scalarUnit (indexVertex (source := source) (target := target) k l)
        (GraphAmalgamInverse.pIndex k l v a) (GraphAmalgamInverse.pIndex k l v b) := by
  funext w
  apply CStarMatrix.ext
  intro i j
  obtain ⟨⟨c,i⟩, rfl⟩ := (coordEquiv source target k l w).surjective i
  obtain ⟨⟨d,j⟩, rfl⟩ := (coordEquiv source target k l w).surjective j
  rw [second_pullback]
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      cases c; cases d
      rw [copyHom_same]
      by_cases h : w = v
      · subst w
        simp [unit, GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.pIndex,
          label, Matrix.single_apply, eq_comm]
      · simp [unit, h, GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.pIndex, label]
    | inr d =>
      rw [copyHom_different _ _ _ (by simp)]
      simp [GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.pIndex]
  | inr c =>
    cases d with
    | inl d =>
      rw [copyHom_different _ _ _ (by simp)]
      simp [GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.pIndex]
    | inr d =>
      by_cases h : c = d
      · subst d
        rw [copyHom_same]
        simp [unit, GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.pIndex, label]
      · rw [copyHom_different _ _ _ (by simpa)]
        simp [GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.pIndex]

theorem eval_sum {N W J : Type} [Fintype N] [Fintype W] [Fintype J]
    (f : N → W) (v : W) (r s : GraphAmalgamInverse.MatrixUnits.Block (label := f) v)
    (x : J → GraphAmalgamInverse.MatrixUnits.Blocks (label := f)) :
    (∑ j, x j) v r s = ∑ j, x j v r s := by
  let ev : GraphAmalgamInverse.MatrixUnits.Blocks (label := f) →+ ℂ :=
    { toFun := fun x => x v r s, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum ev _ _

theorem second_Q (w : V) (a b : Fin (l w)) :
    second source target k l (unit k l (.inr w) a b) =
      ∑ e : {e : E // source e = w},
      GraphCanonicalUnits.scalarUnit (indexVertex (source := source) (target := target) k l)
        (GraphAmalgamInverse.outIndex k l w a e) (GraphAmalgamInverse.outIndex k l w b e) := by
  funext v
  apply CStarMatrix.ext
  intro i j
  obtain ⟨⟨c,i⟩, rfl⟩ := (coordEquiv source target k l v).surjective i
  obtain ⟨⟨d,j⟩, rfl⟩ := (coordEquiv source target k l v).surjective j
  rw [second_pullback, eval_sum]
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      cases c; cases d
      rw [copyHom_same]
      simp [unit, GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.outIndex, GraphAmalgamInverse.qIndex, label]
    | inr d =>
      rw [copyHom_different _ _ _ (by simp)]
      simp [GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.outIndex, GraphAmalgamInverse.qIndex]
  | inr c =>
    cases d with
    | inl d =>
      rw [copyHom_different _ _ _ (by simp)]
      simp [GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.outIndex, GraphAmalgamInverse.qIndex]
    | inr d =>
      by_cases hcd : c = d
      · subst d
        rw [copyHom_same]
        by_cases hw : source c.val = w
        · subst w
          rw [Finset.sum_eq_single ⟨c.val, rfl⟩]
          · simp [unit, GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.outIndex, GraphAmalgamInverse.qIndex,
              label, Matrix.single_apply, eq_comm]
          · intro e _ he
            have hce : c.val ≠ e.val := fun h => he (Subtype.ext h.symm)
            simp [GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.outIndex, GraphAmalgamInverse.qIndex, hce]
          · simp
        · have hz : (unit k l (.inr w) a b) (.inr (source c.val)) = 0 := by
            simp [unit, hw]
          change (unit k l (.inr w) a b) (.inr (source c.val)) i j = _
          rw [hz]
          symm
          apply Finset.sum_eq_zero
          intro e _
          have hce : c.val ≠ e.val := fun h => hw (h ▸ e.property)
          simp [GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.outIndex, GraphAmalgamInverse.qIndex, hce]
      · rw [copyHom_different _ _ _ (by simpa)]
        symm
        apply Finset.sum_eq_zero
        intro e _
        have hne : c.val ≠ e.val ∨ d.val ≠ e.val := by
          by_cases h : c.val = e.val
          · exact Or.inr (fun h' => hcd (Subtype.ext (h.trans h'.symm)))
          · exact Or.inl h
        rcases hne with hne|hne <;>
          simp [GraphCanonicalUnits.scalarUnit, coordEquiv, GraphAmalgamInverse.outIndex, GraphAmalgamInverse.qIndex, hne]


universe u
variable {C : Type u} [CStarAlgebra C]
theorem hom_ext (f g : Common k l →⋆ₐ[ℂ] C)
    (h : ∀ v a b, f (unit k l v a b) = g (unit k l v a b)) : f = g := by
  apply StarAlgHom.ext
  intro x
  have hb (v : V ⊕ V) (a : CStarMatrix (Fin (Sum.elim k l v)) (Fin (Sum.elim k l v)) ℂ) :
      f (Pi.single v a) = g (Pi.single v a) := by
    let m := CStarMatrix.ofMatrix.symm a
    change f (Pi.single v (CStarMatrix.ofMatrix m)) = g (Pi.single v (CStarMatrix.ofMatrix m))
    induction m using Matrix.induction_on' with
    | h_zero => simp
    | h_add a b ha hb =>
      change f (Pi.single v (CStarMatrix.ofMatrix a + CStarMatrix.ofMatrix b)) =
        g (Pi.single v (CStarMatrix.ofMatrix a + CStarMatrix.ofMatrix b))
      simp only [Pi.single_add, map_add, ha, hb]
    | h_std_basis a b z =>
      have hz : Pi.single v (CStarMatrix.ofMatrix (Matrix.single a b z)) = z • unit k l v a b := by
        rw [unit, ← Pi.single_smul]
        congr 1
        change Matrix.single a b z = z • Matrix.single a b (1 : ℂ)
        simp
      rw [hz, map_smul, map_smul, h]
  rw [← Finset.univ_sum_single x, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun v _ => hb v (x v))

theorem commonEntries_of_commutes
    (f₀ : FirstFactor k l →⋆ₐ[ℂ] C)
    (f₁ : Factor (source := source) (target := target) k l →⋆ₐ[ℂ] C)
    (h : f₀.comp (first k l) = f₁.comp (second source target k l)) :
    GraphFiniteAmalgam.CommonEntries k l f₀ f₁ where
  P_entry v a b := by
    have hh := DFunLike.congr_fun h (unit k l (.inl v) a b)
    simpa only [StarAlgHom.comp_apply, first_P, second_P] using hh
  Q_entry v a b := by
    have hh := DFunLike.congr_fun h (unit k l (.inr v) a b)
    simpa only [StarAlgHom.comp_apply, first_Q, second_Q, map_sum] using hh

theorem commutes_of_commonEntries
    (f₀ : FirstFactor k l →⋆ₐ[ℂ] C)
    (f₁ : Factor (source := source) (target := target) k l →⋆ₐ[ℂ] C)
    (h : GraphFiniteAmalgam.CommonEntries k l f₀ f₁) :
    f₀.comp (first k l) = f₁.comp (second source target k l) := by
  apply hom_ext k l
  intro v a b
  cases v with
  | inl v => simpa only [StarAlgHom.comp_apply, first_P, second_P] using h.P_entry v a b
  | inr v => simpa only [StarAlgHom.comp_apply, first_Q, second_Q, map_sum] using h.Q_entry v a b


theorem first_injective : Function.Injective (first k l) := by
  intro a b h
  funext w
  apply CStarMatrix.ext
  intro i j
  cases w with
  | inl v =>
    have hh := congrArg (fun f : FirstFactor k l => f v
      (firstCoordEquiv k l v ⟨true,i⟩) (firstCoordEquiv k l v ⟨true,j⟩)) h
    rw [first_pullback, copyHom_same] at hh
    exact hh
  | inr v =>
    have hh := congrArg (fun f : FirstFactor k l => f v
      (firstCoordEquiv k l v ⟨false,i⟩) (firstCoordEquiv k l v ⟨false,j⟩)) h
    rw [first_pullback, copyHom_same] at hh
    exact hh

theorem second_injective (hns : GraphRelations.NoSinks source) :
    Function.Injective (second source target k l) := by
  intro a b h
  funext w
  apply CStarMatrix.ext
  intro i j
  cases w with
  | inl v =>
    have hh := congrArg (fun f : Factor (source := source) (target := target) k l => f v
      (coordEquiv source target k l v ⟨.inl (),i⟩)
      (coordEquiv source target k l v ⟨.inl (),j⟩)) h
    simpa only [second_pullback, copyHom_same, label] using hh
  | inr v =>
    obtain ⟨e, he⟩ := hns v
    subst v
    have hh := congrArg (fun f : Factor (source := source) (target := target) k l => f (target e)
      (coordEquiv source target k l (target e) ⟨.inr ⟨e,rfl⟩,i⟩)
      (coordEquiv source target k l (target e) ⟨.inr ⟨e,rfl⟩,j⟩)) h
    simpa only [second_pullback, copyHom_same, label] using hh

variable (hk : ∀ v, 0 < k v) (hl : ∀ v, 0 < l v) (hns : GraphRelations.NoSinks source)
local instance graphOrder : PartialOrder (GraphUniversal.Algebra.{0} source target) := CStarAlgebra.spectralOrder _
local instance graphOrderedRing : StarOrderedRing (GraphUniversal.Algebra.{0} source target) := CStarAlgebra.spectralOrderedRing _

theorem graph_commutes :
    (firstFactorHom (GraphCornerIdentification.graphFamily.{0} (source := source) (target := target)) k l).comp (first k l) =
    (factorHom (GraphCornerIdentification.graphFamily.{0} (source := source) (target := target)) k l hk hns).comp
      (second source target k l) :=
  commutes_of_commonEntries source target k l _ _ (GraphFiniteAmalgam.graph_commonEntries k l hk hns)

/-- The full amalgam of the actual P/Q common inclusions is the actual weighted
ordinary-graph corner. All common-entry and forward-compatibility equations are
proved above; none is an input to this equivalence. -/
def amalgamEquivCorner :
    UniversalAmalgam.Algebra (first k l) (second source target k l) ≃⋆ₐ[ℂ]
      GraphCornerIdentification.graphCorner.{0} (source := source) (target := target) k l :=
  GraphFiniteAmalgam.identify k l hk hl
    (UniversalAmalgam.left (first k l) (second source target k l))
    (UniversalAmalgam.right (first k l) (second source target k l))
    (commonEntries_of_commutes source target k l _ _
      (UniversalAmalgam.commutes (first k l) (second source target k l)))
    (first k l) (second source target k l)
    (UniversalAmalgam.isFullAmalgam (first k l) (second source target k l)) hns
    (graph_commutes source target k l hk hns)


omit [Fintype V] in
/-- One P-copy and one Q-copy occur in each first-factor vertex block. -/
theorem first_counts (v : V) (w : V ⊕ V) :
    Fintype.card {c : Bool // (if c then Sum.inl v else Sum.inr v) = w} =
      firstMultiplicity v w := by
  cases w with
  | inl w =>
    simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_bool]
    simp [firstMultiplicity, Matrix.one_apply]
  | inr w =>
    simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_bool]
    simp [firstMultiplicity, Matrix.one_apply]

/-- For the manuscript graph A(v,w), the second block has exactly [I A]
source-copy counts, with targets as rows and sources as columns. -/
theorem second_counts (M : Matrix V V ℕ) (v : V) (w : V ⊕ V) :
    Fintype.card {c : Copies (GraphRelations.matrixTarget M) v //
      label (GraphRelations.matrixSource M) (GraphRelations.matrixTarget M) v c = w} =
      secondMultiplicity M v w := by
  cases w with
  | inl w =>
    simp only [Copies, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_sum_type]
    simp [label, secondMultiplicity, Matrix.one_apply]
  | inr w =>
    simp only [Copies, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_sum_type, label, Sum.inr.injEq, Sum.inl_ne_inr, ↓reduceIte,
      Finset.sum_const_zero, zero_add, secondMultiplicity, Matrix.fromCols_apply_inr]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun e : GraphRelations.MatrixEdge M => GraphRelations.matrixTarget M e = v))
      (by simp) (fun e => if GraphRelations.matrixSource M e = w then (1 : ℕ) else 0)]
    simp only [Finset.sum_filter, GraphRelations.MatrixEdge, Fintype.sum_sigma,
      GraphRelations.matrixSource, GraphRelations.matrixTarget]
    change (∑ w' : V, ∑ v' : V, ∑ _t : Fin (M v' w'),
      if v' = v then if w' = w then (1 : ℕ) else 0 else 0) = M v w
    simp only [Finset.sum_ite_irrel]
    simp



theorem standard_copy_counts (M : Matrix V (V ⊕ V) ℕ) (v : V) (w : V ⊕ V) :
    Fintype.card {c : MultiplicityEmbeddings.Copies M v // c.1 = w} = M v w := by
  simp only [MultiplicityEmbeddings.Copies, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_sigma]
  rw [Finset.sum_eq_single w]
  · simp
  · intro s _ hs; simp [hs]
  · simp

/-- Explicit reindexing connects the constructed first inclusion to the existing
standard multiplicity map, on every common-algebra element. -/
theorem first_standard_coordinates (v : V) :
    ∃ E : FirstBlockIndex k l v ≃ Fin (targetSize (Sum.elim k l) firstMultiplicity v),
      ∀ a : Common k l, CStarMatrix.reindexₐ ℂ ℂ E (first k l a v) =
        multiplicityHom (Sum.elim k l) firstMultiplicity a v := by
  obtain ⟨e, he⟩ := exists_copy_reindex_of_counts (Sum.elim k l)
    (fun c : Bool => if c then Sum.inl v else Sum.inr v)
    (fun c : MultiplicityEmbeddings.Copies (firstMultiplicity (ι := V)) v => c.1)
    (fun w => (first_counts v w).trans (standard_copy_counts firstMultiplicity v w).symm)
  let E := (firstCoordEquiv k l v).symm.trans (e.trans (slotEquiv (Sum.elim k l) firstMultiplicity v))
  refine ⟨E, ?_⟩
  intro a
  apply CStarMatrix.ext
  intro i j
  have hh := congrArg (fun x => x
      ((slotEquiv (Sum.elim k l) firstMultiplicity v).symm i)
      ((slotEquiv (Sum.elim k l) firstMultiplicity v).symm j)) (he a)
  change copyHom _ _ a ((firstCoordEquiv k l v).symm (E.symm i))
    ((firstCoordEquiv k l v).symm (E.symm j)) =
      copyHom (Sum.elim k l) (fun c : MultiplicityEmbeddings.Copies firstMultiplicity v => c.1) a
        ((slotEquiv (Sum.elim k l) firstMultiplicity v).symm i)
        ((slotEquiv (Sum.elim k l) firstMultiplicity v).symm j)
  simpa only [E, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
    CStarMatrix.reindexₐ_apply, Matrix.reindex_apply, Matrix.submatrix_apply] using hh

/-- Explicit reindexing connects the constructed second inclusion to [I A]. -/
theorem second_standard_coordinates (M : Matrix V V ℕ) (v : V) :
    ∃ E : BlockIndex (source := GraphRelations.matrixSource M) (target := GraphRelations.matrixTarget M) k l v ≃
      Fin (targetSize (Sum.elim k l) (secondMultiplicity M) v),
      ∀ a : Common k l, CStarMatrix.reindexₐ ℂ ℂ E
        (second (GraphRelations.matrixSource M) (GraphRelations.matrixTarget M) k l a v) =
        multiplicityHom (Sum.elim k l) (secondMultiplicity M) a v := by
  obtain ⟨e, he⟩ := exists_copy_reindex_of_counts (Sum.elim k l)
    (label (GraphRelations.matrixSource M) (GraphRelations.matrixTarget M) v)
    (fun c : MultiplicityEmbeddings.Copies (secondMultiplicity M) v => c.1)
    (fun w => (second_counts M v w).trans (standard_copy_counts (secondMultiplicity M) v w).symm)
  let ce := coordEquiv (GraphRelations.matrixSource M) (GraphRelations.matrixTarget M) k l v
  let E := ce.symm.trans (e.trans (slotEquiv (Sum.elim k l) (secondMultiplicity M) v))
  refine ⟨E, ?_⟩
  intro a
  apply CStarMatrix.ext
  intro i j
  have hh := congrArg (fun x => x
      ((slotEquiv (Sum.elim k l) (secondMultiplicity M) v).symm i)
      ((slotEquiv (Sum.elim k l) (secondMultiplicity M) v).symm j)) (he a)
  change copyHom _ _ a (ce.symm (E.symm i)) (ce.symm (E.symm j)) =
      copyHom (Sum.elim k l) (fun c : MultiplicityEmbeddings.Copies (secondMultiplicity M) v => c.1) a
        ((slotEquiv (Sum.elim k l) (secondMultiplicity M) v).symm i)
        ((slotEquiv (Sum.elim k l) (secondMultiplicity M) v).symm j)
  simpa only [E, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
    CStarMatrix.reindexₐ_apply, Matrix.reindex_apply, Matrix.submatrix_apply] using hh


/-- Apply the proved graph equivalence to precisely A(v,w) edges from w to v. -/
def matrixAmalgamEquivCorner (M : Matrix V V ℕ) (hM : ∀ w, ∃ v, 0 < M v w) :=
  amalgamEquivCorner (GraphRelations.matrixSource M) (GraphRelations.matrixTarget M) k l hk hl
    ((GraphRelations.matrix_noSinks_iff M).mpr hM)

/-- The actual image of the amalgam unit is the displayed weighted projection q.
The identification of its K-class is a separate external-functor correspondence. -/
theorem amalgamEquivCorner_unit :
    ((amalgamEquivCorner source target k l hk hl hns 1 :
        GraphCornerIdentification.graphCorner.{0} (source := source) (target := target) k l) :
        CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{0} source target)) =
      projection (GraphCornerIdentification.graphFamily.{0} (source := source) (target := target)) k l := by
  rw [map_one]
  rfl
end Suzuki.GraphCommonInclusions

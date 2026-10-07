import Suzuki.WeightedGraphAmalgam
import Suzuki.GraphUniversal

/-!
# The backward weighted graph construction

The input consists of actual elements of a complex C*-algebra satisfying the
explicit finite matrix-unit equations of the two factors and their common
P/Q relations. The graph relations below are proved from these equations.
The explicit matrix-unit hypotheses are realized by actual unital contractive
star representations (`MatrixUnits.representation` and `representation_single`).
The CK family, fixed-universe graph lift, full-corner frame, and inflated backward
star homomorphism are constructed. `backward_first` and `backward_mixed` prove its
exact values on the proposed first and mixed second-factor generators.

Canonical common-map compatibility, the forward universal map, and both full
inverse equations are not yet packaged here. No graph/amalgam isomorphism, graph
relation, or inverse identity is assumed.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace Suzuki.GraphAmalgamInverse
open GraphRelations WeightedGraphAmalgam
universe u

/-- Concrete block matrix units. Off-block entries are unused; all asserted
relations have explicit same-block hypotheses. -/
structure MatrixUnits {N V : Type} [Fintype N] [DecidableEq N]
    (label : N → V) (C : Type u) [CStarAlgebra C] where
  unit : N → N → C
  star_eq : ∀ i j, label i = label j → star (unit i j) = unit j i
  mul_eq : ∀ i j r s, label i = label j → label r = label s →
    unit i j * unit r s = if j = r then unit i s else 0
  sum_diag : ∑ i, unit i i = 1

namespace MatrixUnits
variable {N V : Type} [Fintype N] [DecidableEq N] {label : N → V}
  {C : Type u} [CStarAlgebra C] (S : MatrixUnits label C)

theorem diagonal_projection (i : N) : IsStarProjection (S.unit i i) := by
  refine ⟨?_, S.star_eq i i rfl⟩
  change S.unit i i * S.unit i i = _
  rw [S.mul_eq i i i i rfl rfl, if_pos rfl]

section Representations
variable [Fintype V] [DecidableEq V]

abbrev Block (v : V) := {i : N // label i = v}
abbrev Blocks := ∀ v : V, CStarMatrix (Block (label := label) v) (Block (label := label) v) ℂ

def blockHom (v : V) :
    CStarMatrix (Block (label := label) v) (Block (label := label) v) ℂ →⋆ₙₐ[ℂ] C :=
  matrixUnitHom (fun i j => S.unit i.val j.val)
    (by
      intro i j r s
      rw [S.mul_eq _ _ _ _ (i.property.trans j.property.symm) (r.property.trans s.property.symm)]
      by_cases hjr : j = r
      · subst r; simp
      · rw [if_neg hjr, if_neg (fun h => hjr (Subtype.ext h))])
    (fun i j => S.star_eq i.val j.val (i.property.trans j.property.symm))

omit [Fintype V] in
theorem blockHom_apply (v : V)
    (a : CStarMatrix (Block (label := label) v) (Block (label := label) v) ℂ) :
    S.blockHom v a = ∑ i, ∑ j, (CStarMatrix.ofMatrix.symm a i j) • S.unit i.val j.val :=
  Matrix.liftLinear_apply _ _ _

omit [Fintype V] in
theorem blockHom_one (v : V) : S.blockHom v 1 = ∑ i : Block (label := label) v, S.unit i.val i.val := by
  change matrixEval (fun i j : Block (label := label) v => S.unit i.val j.val) (1 : Matrix _ _ ℂ) = _
  rw [← Matrix.sum_single_one]
  simp

theorem blockHom_sum_one : (∑ v, S.blockHom v 1) = 1 := by
  simp only [S.blockHom_one]
  exact (Fintype.sum_fiberwise label (fun i => S.unit i i)).trans S.sum_diag

omit [Fintype V] [DecidableEq V] in
theorem units_mul_other (v w : V) (hvw : v ≠ w)
    (i j : Block (label := label) v) (r s : Block (label := label) w) :
    S.unit i.val j.val * S.unit r.val s.val = 0 := by
  rw [S.mul_eq _ _ _ _ (i.property.trans j.property.symm) (r.property.trans s.property.symm), if_neg]
  intro hjr
  exact hvw (j.property.symm.trans ((congrArg label hjr).trans r.property))

omit [Fintype V] in
theorem blockHom_mul_other (v w : V) (hvw : v ≠ w)
    (a : CStarMatrix (Block (label := label) v) (Block (label := label) v) ℂ)
    (b : CStarMatrix (Block (label := label) w) (Block (label := label) w) ℂ) :
    S.blockHom v a * S.blockHom w b = 0 := by
  simp only [S.blockHom_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_smul,
    S.units_mul_other v w hvw, smul_zero, Finset.sum_const_zero]

/-- The explicit matrix-unit premises give a genuine unital complex factor representation. -/
def representation : Blocks (label := label) →⋆ₐ[ℂ] C where
  toFun a := ∑ v, S.blockHom v (a v)
  map_zero' := by simp
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_one' := S.blockHom_sum_one
  map_mul' a b := by
    simp only [Pi.mul_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
    symm
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_eq_single v]
    · intro w _ hw
      exact S.blockHom_mul_other w v hw (a w) (b v)
    · simp
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply, map_smul,
      ← Finset.smul_sum, S.blockHom_sum_one]
  map_star' a := by simp only [Pi.star_apply, map_star, star_sum]

/-- The constructed representation really realizes the given same-block matrix units. -/
theorem representation_single (v : V) (i j : Block (label := label) v) (z : ℂ) :
    S.representation (Pi.single v (CStarMatrix.ofMatrix (Matrix.single i j z))) = z • S.unit i.val j.val := by
  change (∑ w, S.blockHom w ((Pi.single v (CStarMatrix.ofMatrix (Matrix.single i j z)) : Blocks (label := label)) w)) = _
  rw [Finset.sum_eq_single v]
  · simp only [Pi.single_eq_same]
    exact matrixEval_single _ i j z
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, map_zero]
  · simp

theorem representation_contractive (a : Blocks (label := label)) : ‖S.representation a‖ ≤ ‖a‖ := by
  have : CStarAlgebra (Blocks (label := label)) := {}
  exact NonUnitalStarAlgHom.norm_apply_le S.representation a

end Representations

end MatrixUnits

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {C : Type u} [CStarAlgebra C] {source target : E → V}
variable (k l : V → ℕ) (hk : ∀ v, 0 < k v) (hl : ∀ v, 0 < l v)

abbrev P (v : V) : Coord k l := base k l hk v
def Q (v : V) : Coord k l := Sum.inr ⟨v, ⟨0, hl v⟩⟩
abbrev FP (v : V) : Index (source := source) k l := baseIndex k l hk v
def FQ (e : E) : Index (source := source) k l := Sum.inr ⟨e, ⟨0, hl (source e)⟩⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem P_vertex (v : V) : coordVertex k l (P k l hk v) = v := rfl
omit [Fintype V] [DecidableEq V] in
@[simp] theorem Q_vertex (v : V) : coordVertex k l (Q k l hl v) = v := rfl
omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem FP_vertex (v : V) :
    indexVertex (target := target) k l (FP (source := source) k l hk v) = v := rfl
omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem FQ_vertex (e : E) :
    indexVertex (target := target) k l (FQ (source := source) k l hl e) = target e := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem P_inj (v w : V) : P k l hk v = P k l hk w ↔ v = w := by
  constructor
  · intro h; exact congrArg (coordVertex k l) h
  · exact congrArg (P k l hk)
omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem FP_inj (v w : V) :
    FP (source := source) k l hk v = FP (source := source) k l hk w ↔ v = w := by
  constructor
  · intro h; exact congrArg Sigma.fst (Sum.inl.inj h)
  · exact congrArg (FP (source := source) k l hk)
omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem FQ_inj (e f : E) :
    FQ (source := source) k l hl e = FQ (source := source) k l hl f ↔ e = f := by
  constructor
  · intro h; exact congrArg Sigma.fst (Sum.inr.inj h)
  · exact congrArg (FQ (source := source) k l hl)

variable (S : MatrixUnits (coordVertex k l) C)
variable (T : MatrixUnits (indexVertex (source := source) (target := target) k l) C)

/-- The chosen first-factor vertex corner. -/
def vertex (v : V) : C := S.unit (P k l hk v) (P k l hk v)
def bridge (v : V) : C := S.unit (P k l hk v) (Q k l hl v)
def incoming (e : E) : C := T.unit (FQ k l hl e) (FP k l hk (target e))
def edge (e : E) : C := bridge k l hk hl S (source e) * incoming k l hk hl T e

/-- The common equations required for the backwards CK computation. These
are concrete matrix-entry equations, not graph relations. -/
structure Common : Prop where
  P_diag : ∀ v, S.unit (P k l hk v) (P k l hk v) = T.unit (FP k l hk v) (FP k l hk v)
  Q_diag : ∀ w, S.unit (Q k l hl w) (Q k l hl w) =
    ∑ e ∈ Finset.univ.filter (fun e => source e = w), T.unit (FQ k l hl e) (FQ k l hl e)

variable (h : Common k l hk hl S T)
include h

theorem q_incoming (e : E) :
    S.unit (Q k l hl (source e)) (Q k l hl (source e)) * incoming k l hk hl T e =
      incoming k l hk hl T e := by
  rw [h.Q_diag, Finset.sum_mul]
  unfold incoming
  have hm (g : E) :
      T.unit (FQ k l hl g) (FQ k l hl g) * T.unit (FQ k l hl e) (FP k l hk (target e)) =
        if g = e then T.unit (FQ k l hl g) (FP k l hk (target e)) else 0 := by
    simp only [T.mul_eq, FP_vertex, FQ_vertex, FQ_inj]
  simp only [hm]
  rw [Finset.sum_ite_eq']
  simp

theorem edge_initial (e : E) :
    star (edge k l hk hl S T e) * edge k l hk hl S T e = vertex k l hk S (target e) := by
  unfold edge bridge
  rw [star_mul, S.star_eq (P k l hk (source e)) (Q k l hl (source e)) rfl]
  calc
    _ = star (incoming k l hk hl T e) *
      (S.unit (Q k l hl (source e)) (P k l hk (source e)) *
        S.unit (P k l hk (source e)) (Q k l hl (source e))) * incoming k l hk hl T e := by
          noncomm_ring
    _ = star (incoming k l hk hl T e) * incoming k l hk hl T e := by
      simp only [S.mul_eq, P_vertex, Q_vertex, ↓reduceIte]
      rw [mul_assoc, q_incoming k l hk hl S T h]
    _ = vertex k l hk S (target e) := by
      unfold incoming vertex
      rw [T.star_eq (FQ k l hl e) (FP k l hk (target e)) rfl]
      simp only [T.mul_eq, FP_vertex, FQ_vertex, ↓reduceIte]
      exact (h.P_diag _).symm

theorem edge_orthogonal (e f : E) (hef : e ≠ f) :
    star (edge k l hk hl S T e) * edge k l hk hl S T f = 0 := by
  unfold edge bridge
  rw [star_mul, S.star_eq (P k l hk (source e)) (Q k l hl (source e)) rfl]
  have hpq := S.mul_eq (Q k l hl (source e)) (P k l hk (source e))
    (P k l hk (source f)) (Q k l hl (source f)) rfl rfl
  simp only [P_inj] at hpq
  calc
    _ = star (incoming k l hk hl T e) *
      (S.unit (Q k l hl (source e)) (P k l hk (source e)) *
        S.unit (P k l hk (source f)) (Q k l hl (source f))) * incoming k l hk hl T f := by
          noncomm_ring
    _ = 0 := by
      rw [hpq]
      by_cases hs : source e = source f
      · rw [if_pos hs, hs, mul_assoc, q_incoming k l hk hl S T h]
        unfold incoming
        rw [T.star_eq (FQ k l hl e) (FP k l hk (target e)) rfl]
        simp only [T.mul_eq, FP_vertex, FQ_vertex, FQ_inj, if_neg hef]
      · rw [if_neg hs, mul_zero, zero_mul]

omit h in
theorem edge_range (e : E) :
    edge k l hk hl S T e * star (edge k l hk hl S T e) =
      bridge k l hk hl S (source e) * T.unit (FQ k l hl e) (FQ k l hl e) *
        star (bridge k l hk hl S (source e)) := by
  unfold edge incoming
  rw [star_mul, T.star_eq (FQ k l hl e) (FP k l hk (target e)) rfl]
  calc
    _ = bridge k l hk hl S (source e) *
      (T.unit (FQ k l hl e) (FP k l hk (target e)) *
        T.unit (FP k l hk (target e)) (FQ k l hl e)) * star (bridge k l hk hl S (source e)) := by
          noncomm_ring
    _ = _ := by simp only [T.mul_eq, FP_vertex, FQ_vertex, ↓reduceIte]

theorem outgoing (w : V) :
    (∑ e ∈ Finset.univ.filter (fun e => source e = w),
      edge k l hk hl S T e * star (edge k l hk hl S T e)) = vertex k l hk S w := by
  simp only [edge_range]
  have heq : (∑ e ∈ Finset.univ.filter (fun e => source e = w),
      bridge k l hk hl S (source e) * T.unit (FQ k l hl e) (FQ k l hl e) *
        star (bridge k l hk hl S (source e))) =
      ∑ e ∈ Finset.univ.filter (fun e => source e = w),
        bridge k l hk hl S w * T.unit (FQ k l hl e) (FQ k l hl e) * star (bridge k l hk hl S w) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  rw [heq, ← Finset.sum_mul, ← Finset.mul_sum, ← h.Q_diag]
  unfold bridge vertex
  rw [S.star_eq (P k l hk w) (Q k l hl w) rfl]
  simp only [S.mul_eq, P_vertex, Q_vertex, ↓reduceIte]

omit h in
theorem vertex_projection (v : V) : IsStarProjection (vertex k l hk S v) := S.diagonal_projection _

omit h in
theorem vertex_mul (v w : V) : vertex k l hk S v * vertex k l hk S w =
    if v = w then vertex k l hk S v else 0 := by
  unfold vertex
  rw [S.mul_eq _ _ _ _ rfl rfl]
  by_cases hvw : v = w
  · subst w; simp
  · simp only [P_inj, if_neg hvw]

/-- The finite vertex corner in the ambient C*-algebra. -/
def cornerProjection : C := ∑ v, vertex k l hk S v

omit h in
theorem cornerProjection_isProjection : IsStarProjection (cornerProjection k l hk S) := by
  refine ⟨?_, ?_⟩
  · change cornerProjection k l hk S * cornerProjection k l hk S = _
    simp only [cornerProjection, Finset.sum_mul, Finset.mul_sum, vertex_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · change star (∑ v, vertex k l hk S v) = _
    simp only [star_sum, (vertex_projection k l hk S _).isSelfAdjoint.star_eq]
    rfl

omit h in
theorem cornerProjection_vertex (v : V) :
    cornerProjection k l hk S * vertex k l hk S v = vertex k l hk S v := by
  simp only [cornerProjection, Finset.sum_mul, vertex_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

omit h in
theorem vertex_cornerProjection (v : V) :
    vertex k l hk S v * cornerProjection k l hk S = vertex k l hk S v := by
  simp only [cornerProjection, Finset.mul_sum, vertex_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

omit h in
theorem vertex_edge (v : V) (e : E) :
    vertex k l hk S v * edge k l hk hl S T e =
      if v = source e then edge k l hk hl S T e else 0 := by
  unfold vertex edge bridge
  rw [← mul_assoc, S.mul_eq (P k l hk v) (P k l hk v)
    (P k l hk (source e)) (Q k l hl (source e)) rfl rfl]
  by_cases hv : v = source e
  · subst v; simp
  · simp only [P_inj, if_neg hv, zero_mul]

theorem edge_vertex (e : E) (v : V) :
    edge k l hk hl S T e * vertex k l hk S v =
      if target e = v then edge k l hk hl S T e else 0 := by
  unfold vertex
  rw [h.P_diag]
  unfold edge incoming
  rw [mul_assoc, T.mul_eq (FQ k l hl e) (FP k l hk (target e))
    (FP k l hk v) (FP k l hk v) rfl rfl]
  by_cases hv : target e = v
  · rw [if_pos hv]
    simp only [hv, ↓reduceIte]
  · simp only [FP_inj, if_neg hv, mul_zero]

omit h in
theorem cornerProjection_edge (e : E) :
    cornerProjection k l hk S * edge k l hk hl S T e = edge k l hk hl S T e := by
  simp only [cornerProjection, Finset.sum_mul, vertex_edge, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

theorem edge_cornerProjection (e : E) :
    edge k l hk hl S T e * cornerProjection k l hk S = edge k l hk hl S T e := by
  simp only [cornerProjection, Finset.mul_sum, edge_vertex k l hk hl S T h,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The selected vertex, inside the actual norm-closed corner with unit p. -/
def vertexInCorner (v : V) : CommonCorner.Corner (cornerProjection_isProjection k l hk S) :=
  CommonCorner.ofSupport (cornerProjection_isProjection k l hk S) (vertex k l hk S v)
    (cornerProjection_vertex k l hk S v) (vertex_cornerProjection k l hk S v)

/-- The reconstructed edge, inside that actual corner. -/
def edgeInCorner (e : E) : CommonCorner.Corner (cornerProjection_isProjection k l hk S) :=
  CommonCorner.ofSupport (cornerProjection_isProjection k l hk S) (edge k l hk hl S T e)
    (cornerProjection_edge k l hk hl S T e) (edge_cornerProjection k l hk hl S T h e)

/-- CK relations are a conclusion of common finite matrix-entry equations. -/
def family : Family source target (CommonCorner.Corner (cornerProjection_isProjection k l hk S)) where
  vertex := vertexInCorner k l hk S
  edge := edgeInCorner k l hk hl S T h
  vertex_projection v := by
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · exact (vertex_projection k l hk S v).isIdempotentElem.eq
    · exact (vertex_projection k l hk S v).isSelfAdjoint.star_eq
  vertex_orthogonal v w hvw := by
    apply Subtype.ext
    exact (vertex_mul k l hk S v w).trans (if_neg hvw)
  vertex_sum := by
    apply Subtype.ext
    simp only [CommonCorner.coe_sum, CommonCorner.coe_one]
    rfl
  initial e := by
    apply Subtype.ext
    exact edge_initial k l hk hl S T h e
  edge_orthogonal e f hef := by
    apply Subtype.ext
    exact edge_orthogonal k l hk hl S T h e f hef
  outgoing w _ := by
    apply Subtype.ext
    simp only [CommonCorner.coe_sum]
    exact outgoing k l hk hl S T h w

/-- The actual backwards graph map in the target's fixed representation universe. -/
def graphLift : GraphUniversal.Algebra.{u} source target →⋆ₐ[ℂ]
    CommonCorner.Corner (cornerProjection_isProjection k l hk S) :=
  GraphUniversal.lift source target (family k l hk hl S T h)

theorem graphLift_vertex (v : V) :
    (graphLift k l hk hl S T h (GraphUniversal.vertex.{u} source target v) : C) = vertex k l hk S v :=
  congrArg Subtype.val (GraphUniversal.lift_vertex source target (family k l hk hl S T h) v)

theorem graphLift_edge (e : E) :
    (graphLift k l hk hl S T h (GraphUniversal.edge.{u} source target e) : C) = edge k l hk hl S T e :=
  congrArg Subtype.val (GraphUniversal.lift_edge source target (family k l hk hl S T h) e)

omit h

def pCoord (v : V) (a : Fin (k v)) : Coord k l := Sum.inl ⟨v, a⟩
def qCoord (v : V) (b : Fin (l v)) : Coord k l := Sum.inr ⟨v, b⟩
def pIndex (v : V) (a : Fin (k v)) : Index (source := source) k l := Sum.inl ⟨v, a⟩
def qIndex (e : E) (b : Fin (l (source e))) : Index (source := source) k l := Sum.inr ⟨e, b⟩
def outIndex (w : V) (b : Fin (l w)) (e : {e : E // source e = w}) : Index (source := source) k l :=
  qIndex k l e (e.property.symm ▸ b)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem outIndex_zero (w : V) (e : {e : E // source e = w}) :
    outIndex k l w ⟨0, hl w⟩ e = FQ k l hl (e : E) := by
  rcases e with ⟨e, he⟩
  subst w
  rfl

/-- Full entrywise common-block equations needed for mixed-generator recovery. -/
structure AllCommon : Prop extends Common k l hk hl S T where
  P_all : ∀ (v : V) (a b : Fin (k v)),
    S.unit (pCoord k l v a) (pCoord k l v b) = T.unit (pIndex k l v a) (pIndex k l v b)
  Q_all : ∀ (w : V) (b c : Fin (l w)),
    S.unit (qCoord k l w b) (qCoord k l w c) =
      ∑ e : {e : E // source e = w}, T.unit (outIndex k l w b e) (outIndex k l w c e)

variable (H : AllCommon k l hk hl S T)
include H

theorem q_incoming_all (e : E) (b : Fin (l (source e))) :
    S.unit (qCoord k l (source e) b) (Q k l hl (source e)) * incoming k l hk hl T e =
      T.unit (qIndex k l e b) (FP k l hk (target e)) := by
  change S.unit (qCoord k l (source e) b) (qCoord k l (source e) ⟨0, hl (source e)⟩) * _ = _
  rw [H.Q_all, Finset.sum_mul]
  unfold incoming
  have hm (g : {g : E // source g = source e}) :
      T.unit (outIndex k l (source e) b g) (outIndex k l (source e) ⟨0, hl (source e)⟩ g) *
        T.unit (FQ k l hl e) (FP k l hk (target e)) =
      if g = ⟨e, rfl⟩ then T.unit (outIndex k l (source e) b g) (FP k l hk (target e)) else 0 := by
    rw [T.mul_eq (outIndex k l (source e) b g) (outIndex k l (source e) ⟨0, hl (source e)⟩ g)
      (FQ k l hl e) (FP k l hk (target e)) rfl rfl, outIndex_zero]
    by_cases hg : g = ⟨e, rfl⟩
    · subst g; simp
    · rw [if_neg hg, if_neg]
      intro he
      exact hg (Subtype.ext ((FQ_inj k l hl g.val e).mp he))
  simp only [hm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

/-- The manuscript's mixed-unit recovery identity is proved inside the arbitrary
ambient C*-algebra, before assuming or constructing either inverse map. -/
theorem mixed_recovery (e : E) (b : Fin (l (source e))) (a : Fin (k (target e))) :
    T.unit (qIndex k l e b) (pIndex k l (target e) a) =
      S.unit (qCoord k l (source e) b) (P k l hk (source e)) * edge k l hk hl S T e *
        S.unit (P k l hk (target e)) (pCoord k l (target e) a) := by
  symm
  unfold edge bridge
  calc
    _ = (S.unit (qCoord k l (source e) b) (Q k l hl (source e)) * incoming k l hk hl T e) *
        S.unit (P k l hk (target e)) (pCoord k l (target e) a) := by
      rw [← mul_assoc (S.unit (qCoord k l (source e) b) (P k l hk (source e))),
        S.mul_eq (qCoord k l (source e) b) (P k l hk (source e))
          (P k l hk (source e)) (Q k l hl (source e)) rfl rfl, if_pos rfl]
    _ = T.unit (qIndex k l e b) (FP k l hk (target e)) *
        T.unit (FP k l hk (target e)) (pIndex k l (target e) a) := by
      rw [q_incoming_all k l hk hl S T H]
      exact congrArg (fun z => T.unit (qIndex k l e b) (FP k l hk (target e)) * z)
        (H.P_all (target e) ⟨0, hk (target e)⟩ a)
    _ = _ := by
      rw [T.mul_eq (qIndex k l e b) (FP k l hk (target e))
        (FP k l hk (target e)) (pIndex k l (target e) a) rfl rfl, if_pos rfl]

omit H in
/-- Every second-factor unit is recovered from the distinguished P columns. -/
theorem unit_from_column (v : V) (i j : Index (source := source) k l)
    (hi : indexVertex (target := target) k l i = v)
    (hj : indexVertex (target := target) k l j = v) :
    T.unit i j = T.unit i (FP k l hk v) * star (T.unit j (FP k l hk v)) := by
  rw [T.star_eq j (FP k l hk v) hj, T.mul_eq i (FP k l hk v) (FP k l hk v) j hi hj.symm, if_pos rfl]

/-- Equality on first-factor units and recovered edges entails equality on every
second-factor unit. This is the generator calculation used in the inverse proof. -/
theorem hom_ext_units {B : Type u} [CStarAlgebra B] (φ ψ : C →⋆ₐ[ℂ] B)
    (hS : ∀ i j, coordVertex k l i = coordVertex k l j → φ (S.unit i j) = ψ (S.unit i j))
    (he : ∀ e, φ (edge k l hk hl S T e) = ψ (edge k l hk hl S T e))
    (i j : Index (source := source) k l)
    (hij : indexVertex (target := target) k l i = indexVertex (target := target) k l j) :
    φ (T.unit i j) = ψ (T.unit i j) := by
  have hcolumn (r : Index (source := source) k l) :
      φ (T.unit r (FP k l hk (indexVertex (target := target) k l r))) =
        ψ (T.unit r (FP k l hk (indexVertex (target := target) k l r))) := by
    cases r with
    | inl va =>
      rcases va with ⟨v, a⟩
      change φ (T.unit (pIndex k l v a) (pIndex k l v ⟨0, hk v⟩)) =
        ψ (T.unit (pIndex k l v a) (pIndex k l v ⟨0, hk v⟩))
      rw [← H.P_all]
      exact hS (pCoord k l v a) (pCoord k l v ⟨0, hk v⟩) rfl
    | inr eb =>
      rcases eb with ⟨e, b⟩
      change φ (T.unit (qIndex k l e b) (pIndex k l (target e) ⟨0, hk (target e)⟩)) =
        ψ (T.unit (qIndex k l e b) (pIndex k l (target e) ⟨0, hk (target e)⟩))
      rw [mixed_recovery k l hk hl S T H]
      have hleft := hS (qCoord k l (source e) b) (P k l hk (source e)) rfl
      have hright := hS (P k l hk (target e)) (pCoord k l (target e) ⟨0, hk (target e)⟩) rfl
      simp only [map_mul, hleft, hright, he]
  rw [unit_from_column k l hk T (indexVertex (target := target) k l i) i j rfl hij.symm]
  simp only [map_mul, map_star, hcolumn i]
  rw [hij, hcolumn j]

omit H

/-- An enumeration is only used to interface with the previously proved finite-frame API. -/
def enumeration : Coord k l ≃ Fin (Fintype.card (Coord k l)) := Fintype.equivFin _
def frameX (i : Fin (Fintype.card (Coord k l))) : C :=
  S.unit ((enumeration k l).symm i) (P k l hk (coordVertex k l ((enumeration k l).symm i)))

theorem frameX_support (i : Fin (Fintype.card (Coord k l))) :
    frameX k l hk S i * cornerProjection k l hk S = frameX k l hk S i := by
  unfold cornerProjection
  rw [Finset.mul_sum, Finset.sum_eq_single (coordVertex k l ((enumeration k l).symm i))]
  · unfold frameX vertex
    rw [S.mul_eq ((enumeration k l).symm i) (P k l hk (coordVertex k l ((enumeration k l).symm i)))
      (P k l hk (coordVertex k l ((enumeration k l).symm i)))
      (P k l hk (coordVertex k l ((enumeration k l).symm i))) rfl rfl, if_pos rfl]
  · intro v _ hv
    unfold frameX vertex
    rw [S.mul_eq ((enumeration k l).symm i) (P k l hk (coordVertex k l ((enumeration k l).symm i)))
      (P k l hk v) (P k l hk v) rfl rfl, if_neg]
    intro hp
    exact hv ((P_inj k l hk _ _).mp hp).symm
  · simp

theorem frameX_range (i : Fin (Fintype.card (Coord k l))) :
    frameX k l hk S i * star (frameX k l hk S i) =
      S.unit ((enumeration k l).symm i) ((enumeration k l).symm i) := by
  unfold frameX
  rw [S.star_eq ((enumeration k l).symm i) (P k l hk (coordVertex k l ((enumeration k l).symm i))) rfl,
    S.mul_eq ((enumeration k l).symm i) (P k l hk (coordVertex k l ((enumeration k l).symm i)))
      (P k l hk (coordVertex k l ((enumeration k l).symm i))) ((enumeration k l).symm i) rfl rfl, if_pos rfl]

/-- The first-factor units provide the actual full-corner frame, with no fullness premise. -/
def frame : CommonCorner.Frame (cornerProjection_isProjection k l hk S) (Fintype.card (Coord k l)) where
  x := frameX k l hk S
  support := frameX_support k l hk S
  total := by
    simp only [frameX_range]
    exact (Fintype.sum_equiv (enumeration k l).symm _ (fun i => S.unit i i) (fun _ => rfl)).trans S.sum_diag

theorem gram_entry (i j : Fin (Fintype.card (Coord k l))) :
    ((frame k l hk S).gram i j : C) =
      if i = j then vertex k l hk S (coordVertex k l ((enumeration k l).symm i)) else 0 := by
  rw [CommonCorner.Frame.coe_gram_apply]
  change star (frameX k l hk S i) * frameX k l hk S j = _
  unfold frameX
  rw [S.star_eq ((enumeration k l).symm i) (P k l hk (coordVertex k l ((enumeration k l).symm i))) rfl,
    S.mul_eq (P k l hk (coordVertex k l ((enumeration k l).symm i))) ((enumeration k l).symm i)
      ((enumeration k l).symm j) (P k l hk (coordVertex k l ((enumeration k l).symm j))) rfl rfl]
  by_cases hij : i = j
  · subst j; simp only [↓reduceIte]; rfl
  · rw [if_neg hij, if_neg (fun he => hij ((enumeration k l).symm.injective he))]

local instance graphOrder : PartialOrder (GraphUniversal.Algebra.{u} source target) :=
  CStarAlgebra.spectralOrder _
local instance graphOrderedRing : StarOrderedRing (GraphUniversal.Algebra.{u} source target) :=
  CStarAlgebra.spectralOrderedRing _

/-- Amplify the actual graph lift and reindex into the finite-frame coordinates. -/
def amplifiedGraphLift :
    CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{u} source target) →⋆ₙₐ[ℂ]
      CStarMatrix (Fin (Fintype.card (Coord k l))) (Fin (Fintype.card (Coord k l)))
        (CommonCorner.Corner (cornerProjection_isProjection k l hk S)) :=
  (CStarMatrix.reindexₐ ℂ _ (enumeration k l)).toStarAlgHom.toNonUnitalStarAlgHom.comp
    (CStarMatrix.mapₙₐ (graphLift k l hk hl S T h).toNonUnitalStarAlgHom)

include h in
theorem amplifiedGraphLift_projection :
    amplifiedGraphLift k l hk hl S T h
      (WeightedGraphAmalgam.projection (GraphUniversal.family.{u} source target) k l) =
        (frame k l hk S).gram := by
  apply CStarMatrix.ext
  intro i j
  apply Subtype.ext
  change (graphLift k l hk hl S T h
    ((WeightedGraphAmalgam.projection (GraphUniversal.family.{u} source target) k l)
      ((enumeration k l).symm i) ((enumeration k l).symm j)) : C) = _
  rw [gram_entry]
  change (graphLift k l hk hl S T h
    (if (enumeration k l).symm i = (enumeration k l).symm j then
      GraphUniversal.vertex.{u} source target (coordVertex k l ((enumeration k l).symm i)) else 0) : C) = _
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, if_pos rfl, graphLift_vertex]
  · rw [if_neg (fun he => hij ((enumeration k l).symm.injective he)), map_zero, if_neg hij]
    rfl

/-- Restrict the amplified graph lift to its actual projection corner. -/
def amplifiedCornerLift :
    CommonCorner.Corner (WeightedGraphAmalgam.projection_isProjection
      (GraphUniversal.family.{u} source target) k l) →⋆ₐ[ℂ]
      CommonCorner.Corner (frame k l hk S).gram_projection where
  toFun M := CommonCorner.ofSupport (frame k l hk S).gram_projection
    (amplifiedGraphLift k l hk hl S T h M)
    (by
      rw [← amplifiedGraphLift_projection k l hk hl S T h, ← map_mul, CommonCorner.left_support])
    (by
      rw [← amplifiedGraphLift_projection k l hk hl S T h, ← map_mul, CommonCorner.right_support])
  map_one' := Subtype.ext (amplifiedGraphLift_projection k l hk hl S T h)
  map_zero' := Subtype.ext (map_zero (amplifiedGraphLift k l hk hl S T h))
  map_add' a b := Subtype.ext (map_add (amplifiedGraphLift k l hk hl S T h) (a : CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{u} source target)) (b : CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{u} source target)))
  map_mul' a b := Subtype.ext (map_mul (amplifiedGraphLift k l hk hl S T h) (a : CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{u} source target)) (b : CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{u} source target)))
  map_star' a := Subtype.ext (map_star (amplifiedGraphLift k l hk hl S T h)
    (a : CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{u} source target)))
  commutes' z := Subtype.ext (by
    change amplifiedGraphLift k l hk hl S T h (z • _) = z • _
    rw [map_smul]
    exact congrArg (fun M => z • M) (amplifiedGraphLift_projection k l hk hl S T h))

/-- The manuscript's inflated backwards map, constructed as a unital star homomorphism. -/
def backward :
    CommonCorner.Corner (WeightedGraphAmalgam.projection_isProjection
      (GraphUniversal.family.{u} source target) k l) →⋆ₐ[ℂ] C :=
  (frame k l hk S).equivalence.symm.toStarAlgHom.comp (amplifiedCornerLift k l hk hl S T h)

include h in
theorem backward_coefficients (M : CommonCorner.Corner (WeightedGraphAmalgam.projection_isProjection
      (GraphUniversal.family.{u} source target) k l)) :
    (frame k l hk S).matrixHom (backward k l hk hl S T h M) = amplifiedGraphLift k l hk hl S T h M := by
  exact congrArg Subtype.val ((frame k l hk S).equivalence.apply_symm_apply
    (amplifiedCornerLift k l hk hl S T h M))

include h in
theorem backward_expand (M : CommonCorner.Corner (WeightedGraphAmalgam.projection_isProjection
      (GraphUniversal.family.{u} source target) k l)) :
    backward k l hk hl S T h M = (frame k l hk S).expand (amplifiedGraphLift k l hk hl S T h M) := by
  apply (frame k l hk S).matrixHom_injective
  rw [backward_coefficients, CommonCorner.Frame.matrixHom_expand]
  symm
  rw [← amplifiedGraphLift_projection k l hk hl S T h, ← map_mul, CommonCorner.left_support,
    ← map_mul, CommonCorner.right_support]

/-- A supported graph matrix entry, as an element of q M(Graph) q. -/
def supportedSingle (i j : Coord k l) (x : GraphUniversal.Algebra.{u} source target)
    (hx : GraphUniversal.vertex.{u} source target (coordVertex k l i) * x = x)
    (hy : x * GraphUniversal.vertex.{u} source target (coordVertex k l j) = x) :
    CommonCorner.Corner (WeightedGraphAmalgam.projection_isProjection
      (GraphUniversal.family.{u} source target) k l) :=
  CommonCorner.ofSupport (WeightedGraphAmalgam.projection_isProjection
    (GraphUniversal.family.{u} source target) k l) (single k l i j x)
    (by rw [projection_mul_single]; exact congrArg (single k l i j) hx)
    (by rw [single_mul_projection]; exact congrArg (single k l i j) hy)

include h in
theorem amplified_single_entry (i j : Coord k l) (x : GraphUniversal.Algebra.{u} source target)
    (r s : Fin (Fintype.card (Coord k l))) :
    (amplifiedGraphLift k l hk hl S T h (single k l i j x) r s : C) =
      if (enumeration k l) i = r ∧ (enumeration k l) j = s then (graphLift k l hk hl S T h x : C) else 0 := by
  change (graphLift k l hk hl S T h
    (Matrix.single i j x ((enumeration k l).symm r) ((enumeration k l).symm s)) : C) = _
  simp only [Matrix.single_apply, Equiv.eq_symm_apply]
  split_ifs <;> simp only [map_zero, ZeroMemClass.coe_zero]

include h in
/-- Exact entrywise formula for the constructed inflated inverse. -/
theorem backward_single (i j : Coord k l) (x : GraphUniversal.Algebra.{u} source target)
    (hx : GraphUniversal.vertex.{u} source target (coordVertex k l i) * x = x)
    (hy : x * GraphUniversal.vertex.{u} source target (coordVertex k l j) = x) :
    backward k l hk hl S T h (supportedSingle k l i j x hx hy) =
      S.unit i (P k l hk (coordVertex k l i)) * (graphLift k l hk hl S T h x : C) *
        S.unit (P k l hk (coordVertex k l j)) j := by
  rw [backward_expand]
  change (∑ r, ∑ s, frameX k l hk S r *
    (amplifiedGraphLift k l hk hl S T h (single k l i j x) r s : C) * star (frameX k l hk S s)) = _
  rw [Finset.sum_eq_single ((enumeration k l) i)]
  · rw [Finset.sum_eq_single ((enumeration k l) j)]
    · rw [amplified_single_entry, if_pos ⟨rfl, rfl⟩]
      simp only [frameX, Equiv.symm_apply_apply]
      rw [S.star_eq j (P k l hk (coordVertex k l j)) rfl]
    · intro s _ hs
      rw [amplified_single_entry, if_neg (by intro he; exact hs he.2.symm), mul_zero, zero_mul]
    · simp
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro s _
    rw [amplified_single_entry, if_neg (by intro he; exact hr he.1.symm), mul_zero, zero_mul]
  · simp

/-- The proposed image of a same-vertex first-factor matrix unit. -/
def firstImage (i j : Coord k l) (hij : coordVertex k l i = coordVertex k l j) :
    CommonCorner.Corner (WeightedGraphAmalgam.projection_isProjection
      (GraphUniversal.family.{u} source target) k l) :=
  supportedSingle k l i j (GraphUniversal.vertex.{u} source target (coordVertex k l i))
    ((GraphUniversal.vertex_projection.{u} source target _).isIdempotentElem.eq)
    (by rw [hij]; exact (GraphUniversal.vertex_projection.{u} source target _).isIdempotentElem.eq)

include h in
/-- The constructed backward map fixes each first-factor generator exactly. -/
theorem backward_first (i j : Coord k l) (hij : coordVertex k l i = coordVertex k l j) :
    backward k l hk hl S T h (firstImage (source := source) (target := target) k l i j hij) = S.unit i j := by
  unfold firstImage
  rw [backward_single, graphLift_vertex]
  unfold vertex
  rw [S.mul_eq i (P k l hk (coordVertex k l i)) (P k l hk (coordVertex k l i))
    (P k l hk (coordVertex k l i)) rfl rfl, if_pos rfl,
    S.mul_eq i (P k l hk (coordVertex k l i)) (P k l hk (coordVertex k l j)) j rfl rfl,
    if_pos (congrArg (P k l hk) hij)]

/-- The graph-corner image of a mixed second-factor generator. -/
def mixedImage (e : E) (b : Fin (l (source e))) (a : Fin (k (target e))) :
    CommonCorner.Corner (WeightedGraphAmalgam.projection_isProjection
      (GraphUniversal.family.{u} source target) k l) :=
  supportedSingle k l (qCoord k l (source e) b) (pCoord k l (target e) a)
    (GraphUniversal.edge.{u} source target e)
    ((GraphUniversal.family.{u} source target).edge_left_support e)
    ((GraphUniversal.family.{u} source target).edge_right_support e)

include h H in
/-- The constructed backward map fixes each mixed second-factor generator exactly. -/
theorem backward_mixed (e : E) (b : Fin (l (source e))) (a : Fin (k (target e))) :
    backward k l hk hl S T h (mixedImage (source := source) (target := target) k l e b a) =
      T.unit (qIndex k l e b) (pIndex k l (target e) a) := by
  unfold mixedImage
  rw [backward_single, graphLift_edge]
  exact (mixed_recovery k l hk hl S T H e b a).symm


include h in
theorem backward_contractive (M : CommonCorner.Corner (WeightedGraphAmalgam.projection_isProjection
      (GraphUniversal.family.{u} source target) k l)) :
    ‖backward k l hk hl S T h M‖ ≤ ‖M‖ :=
  NonUnitalStarAlgHom.norm_apply_le (backward k l hk hl S T h) M

end Suzuki.GraphAmalgamInverse

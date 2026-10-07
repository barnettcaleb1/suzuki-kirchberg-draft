import Suzuki.GraphRelations

/-!
# Weighted operators for the graph/amalgam identification

These are concrete operator-norm matrices over an actual Cuntz--Krieger family,
with arbitrary finite vertex weights. The results below establish the weighted
frame, common-block identities, and genuine unital star homomorphisms from
both weighted finite factors into the graph corner. The factor dimensions
are proved to be k+l and k+M*l, with the manuscript's source/target convention.

The recovered-edge and mixed-generator formulas are identities in this concrete
graph corner. Compatibility with the canonical multiplicity maps, a graph family
in the abstract universal amalgam, and both universal inverse maps remain to be
proved. No amalgam/graph isomorphism or generation theorem is assumed here.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped CStarAlgebra ComplexOrder
open Suzuki.GraphRelations
namespace Suzuki.WeightedGraphAmalgam
universe u
section MatrixUnits
variable {N : Type} [Fintype N] [DecidableEq N]
variable {B : Type u} [CStarAlgebra B]
variable (U : N → N → B)

def matrixEval : Matrix N N ℂ →ₗ[ℂ] B :=
  Matrix.liftLinear ℂ (fun i j => LinearMap.toSpanSingleton ℂ B (U i j))

@[simp] theorem matrixEval_single (i j : N) (z : ℂ) :
    matrixEval U (Matrix.single i j z) = z • U i j := by
  simp [matrixEval]

theorem matrixEval_mul (hmul : ∀ i j r s, U i j * U r s = if j = r then U i s else 0)
    (a b : Matrix N N ℂ) : matrixEval U (a * b) = matrixEval U a * matrixEval U b := by
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a c ha hc => simp only [add_mul, map_add, ha, hc]
  | h_std_basis i j z =>
    induction b using Matrix.induction_on' with
    | h_zero => simp
    | h_add b c hb hc => simp only [mul_add, map_add, hb, hc]
    | h_std_basis r s w =>
      by_cases h : j = r
      · subst r
        simp only [Matrix.single_mul_single_same, matrixEval_single, smul_mul_smul, hmul,
          ↓reduceIte]
      · rw [Matrix.single_mul_single_of_ne _ _ _ _ h]
        simp only [map_zero, matrixEval_single, smul_mul_smul, hmul, if_neg h, smul_zero]

theorem matrixEval_star (hstar : ∀ i j, star (U i j) = U j i) (a : Matrix N N ℂ) :
    matrixEval U (star a) = star (matrixEval U a) := by
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a b ha hb => simp only [star_add, map_add, ha, hb]
  | h_std_basis i j z =>
    change matrixEval U (Matrix.single i j z).conjTranspose = _
    simp only [Matrix.conjTranspose_single, matrixEval_single, star_smul, hstar]

/-- An actual nonunital star homomorphism obtained from proved matrix-unit relations. -/
def matrixUnitHom (hmul : ∀ i j r s, U i j * U r s = if j = r then U i s else 0)
    (hstar : ∀ i j, star (U i j) = U j i) : CStarMatrix N N ℂ →⋆ₙₐ[ℂ] B where
  toFun a := matrixEval U (CStarMatrix.ofMatrix.symm a)
  map_zero' := map_zero (matrixEval U)
  map_add' a b := (matrixEval U).map_add (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b)
  map_smul' z a := (matrixEval U).map_smul z (CStarMatrix.ofMatrix.symm a)
  map_mul' a b := matrixEval_mul U hmul (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b)
  map_star' a := matrixEval_star U hstar (CStarMatrix.ofMatrix.symm a)
end MatrixUnits

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {A : Type u} [CStarAlgebra A]
variable {source target : E → V} (F : Family source target A)
variable (k l : V → ℕ) (hk : ∀ v, 0 < k v)
local instance coefficientOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance coefficientOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

abbrev Coord := (Σ v, Fin (k v)) ⊕ (Σ v, Fin (l v))
abbrev Index := (Σ v, Fin (k v)) ⊕ (Σ e, Fin (l (source e)))

def coordVertex : Coord k l → V := Sum.elim Sigma.fst Sigma.fst
def indexVertex : Index (source := source) k l → V :=
  Sum.elim Sigma.fst (fun eb => target eb.1)
def row : Index (source := source) k l → Coord k l :=
  Sum.elim Sum.inl (fun eb => Sum.inr ⟨source eb.1, eb.2⟩)
def base (v : V) : Coord k l := Sum.inl ⟨v, ⟨0, hk v⟩⟩
def coefficient : Index (source := source) k l → A :=
  Sum.elim (fun va => F.vertex va.1) (fun eb => F.edge eb.1)

def single (i j : Coord k l) (a : A) : CStarMatrix (Coord k l) (Coord k l) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

def projection : CStarMatrix (Coord k l) (Coord k l) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal (fun i => F.vertex (coordVertex k l i)))

def op (i : Index (source := source) k l) : CStarMatrix (Coord k l) (Coord k l) A :=
  single k l (row k l i) (base k l hk (indexVertex (target := target) k l i)) (coefficient F k l i)

def initialProjection (v : V) : CStarMatrix (Coord k l) (Coord k l) A :=
  single k l (base k l hk v) (base k l hk v) (F.vertex v)

omit [Fintype V] in
@[simp] theorem single_star (i j : Coord k l) (a : A) :
    star (single k l i j a) = single k l j i (star a) := Matrix.conjTranspose_single _ _ _

@[simp] theorem single_mul_same (i j t : Coord k l) (a b : A) :
    single k l i j a * single k l j t b = single k l i t (a * b) :=
  Matrix.single_mul_single_same _ _ _ _ _

theorem single_mul_ne (i j s t : Coord k l) (a b : A) (h : j ≠ s) :
    single k l i j a * single k l s t b = 0 :=
  Matrix.single_mul_single_of_ne _ _ _ _ h _

omit [Fintype V] in
@[simp] theorem single_zero (i j : Coord k l) : single k l i j (0 : A) = 0 :=
  Matrix.single_zero _ _

theorem single_mul_of_coeff_zero (i j s t : Coord k l) (a b : A) (h : a * b = 0) :
    single k l i j a * single k l s t b = 0 := by
  by_cases hjs : j = s
  · subst s; rw [single_mul_same, h, single_zero]
  · exact single_mul_ne k l i j s t a b hjs

omit [DecidableEq E] in
theorem projection_isProjection : IsStarProjection (projection F k l) := by
  refine ⟨?_, ?_⟩
  · change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact (F.vertex_projection _).isIdempotentElem.eq
  · change (Matrix.diagonal _).conjTranspose = Matrix.diagonal _
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact (F.vertex_projection _).isSelfAdjoint.star_eq

omit [DecidableEq E] in
theorem initialProjection_isProjection (v : V) :
    IsStarProjection (initialProjection F k l hk v) := by
  refine ⟨?_, ?_⟩
  · change single k l _ _ _ * single k l _ _ _ = single k l _ _ _
    rw [single_mul_same, (F.vertex_projection v).isIdempotentElem.eq]
  · change star (single k l _ _ _) = single k l _ _ _
    rw [single_star, (F.vertex_projection v).isSelfAdjoint.star_eq]

omit [DecidableEq E] in
theorem projection_mul_single (i j : Coord k l) (a : A) :
    projection F k l * single k l i j a =
      single k l i j (F.vertex (coordVertex k l i) * a) := by
  change Matrix.diagonal _ * Matrix.single i j a = Matrix.single i j _
  ext r c
  simp only [Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩; rfl
  · exact mul_zero _

omit [DecidableEq E] in
theorem single_mul_projection (i j : Coord k l) (a : A) :
    single k l i j a * projection F k l =
      single k l i j (a * F.vertex (coordVertex k l j)) := by
  change Matrix.single i j a * Matrix.diagonal _ = Matrix.single i j _
  ext r c
  simp only [Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩; rfl
  · exact zero_mul _

omit [DecidableEq E] in
theorem op_left_support (i : Index (source := source) k l) :
    projection F k l * op F k l hk i = op F k l hk i := by
  rw [op, projection_mul_single]
  cases i with
  | inl va => exact congrArg (single k l _ _) (F.vertex_projection va.1).isIdempotentElem.eq
  | inr eb => exact congrArg (single k l _ _) (F.edge_left_support eb.1)

omit [DecidableEq E] in
theorem op_right_support (i : Index (source := source) k l) :
    op F k l hk i * projection F k l = op F k l hk i := by
  rw [op, single_mul_projection]
  cases i with
  | inl va => exact congrArg (single k l _ _) (F.vertex_projection va.1).isIdempotentElem.eq
  | inr eb => exact congrArg (single k l _ _) (F.edge_right_support eb.1)

/-- The weighted operators lie in the genuine C*-corner, whose unit is q. -/
def opInCorner (i : Index (source := source) k l) :
    CommonCorner.Corner (projection_isProjection F k l) :=
  CommonCorner.ofSupport (projection_isProjection F k l) (op F k l hk i)
    (op_left_support F k l hk i) (op_right_support F k l hk i)

/-- Orthogonal initial products, including indices in different vertex blocks. -/
theorem op_inner (i j : Index (source := source) k l) :
    star (op F k l hk i) * op F k l hk j =
      if i = j then initialProjection F k l hk (indexVertex (target := target) k l i) else 0 := by
  cases i with
  | inl va =>
    cases j with
    | inl wb =>
      by_cases h : va = wb
      · subst wb
        rw [if_pos rfl]
        simp only [op, row, indexVertex, coefficient, Sum.elim_inl, single_star,
          single_mul_same, (F.vertex_projection va.1).isSelfAdjoint.star_eq,
          (F.vertex_projection va.1).isIdempotentElem.eq, initialProjection]
      · rw [if_neg (by simpa)]
        simp only [op, row, coefficient, Sum.elim_inl, single_star]
        exact single_mul_ne k l _ _ _ _ _ _ (by simpa using h)
    | inr eb =>
      rw [if_neg (by simp)]
      simp only [op, row, coefficient, Sum.elim_inl, Sum.elim_inr, single_star]
      exact single_mul_ne k l _ _ _ _ _ _ (by simp)
  | inr ea =>
    cases j with
    | inl vb =>
      rw [if_neg (by simp)]
      simp only [op, row, coefficient, Sum.elim_inl, Sum.elim_inr, single_star]
      exact single_mul_ne k l _ _ _ _ _ _ (by simp)
    | inr fb =>
      rcases ea with ⟨e, a⟩
      rcases fb with ⟨f, b⟩
      by_cases hef : e = f
      · subst f
        by_cases hab : a = b
        · subst b
          rw [if_pos rfl]
          simp only [op, row, indexVertex, coefficient, Sum.elim_inr, single_star,
            single_mul_same, F.initial, initialProjection]
        · rw [if_neg (by simpa)]
          simp only [op, row, coefficient, Sum.elim_inr, single_star]
          exact single_mul_ne k l _ _ _ _ _ _ (by simpa using hab)
      · rw [if_neg (by intro h; exact hef (congrArg (fun x => x.1) (Sum.inr.inj h)))]
        simp only [op, row, coefficient, Sum.elim_inr, single_star]
        exact single_mul_of_coeff_zero k l _ _ _ _ _ _ (F.edge_orthogonal e f hef)

theorem op_contractive (i : Index (source := source) k l) : ‖op F k l hk i‖ ≤ 1 := by
  apply norm_le_one_of_initial (initialProjection_isProjection F k l hk (indexVertex (target := target) k l i))
  rw [op_inner, if_pos rfl]

/-- The manuscript's proposed second-factor matrix units. -/
def unit (i j : Index (source := source) k l) : CStarMatrix (Coord k l) (Coord k l) A :=
  op F k l hk i * star (op F k l hk j)

omit [DecidableEq E] in
@[simp] theorem unit_star (i j : Index (source := source) k l) :
    star (unit F k l hk i j) = unit F k l hk j i := by
  simp only [unit, star_mul, star_star]

theorem op_mul_initial (i : Index (source := source) k l) :
    op F k l hk i * initialProjection F k l hk (indexVertex (target := target) k l i) =
      op F k l hk i := by
  apply support_of_initial (initialProjection_isProjection F k l hk _)
  rw [op_inner, if_pos rfl]

theorem unit_mul (i j r s : Index (source := source) k l)
    (hij : indexVertex (target := target) k l i = indexVertex (target := target) k l j) :
    unit F k l hk i j * unit F k l hk r s =
      if j = r then unit F k l hk i s else 0 := by
  change (op F k l hk i * star (op F k l hk j)) *
    (op F k l hk r * star (op F k l hk s)) = _
  rw [mul_assoc, ← mul_assoc (star (op F k l hk j)), op_inner]
  by_cases hjr : j = r
  · rw [if_pos hjr, if_pos hjr, ← mul_assoc, ← hij, op_mul_initial]
    rfl
  · rw [if_neg hjr, if_neg hjr, zero_mul, mul_zero]

/-- Matrix units from different vertex blocks multiply to zero. -/
theorem unit_mul_of_vertex_ne (i j r s : Index (source := source) k l)
    (h : indexVertex (target := target) k l j ≠ indexVertex (target := target) k l r) :
    unit F k l hk i j * unit F k l hk r s = 0 := by
  have hjr : j ≠ r := fun he => h (congrArg (indexVertex (target := target) k l) he)
  change (op F k l hk i * star (op F k l hk j)) *
    (op F k l hk r * star (op F k l hk s)) = _
  rw [mul_assoc, ← mul_assoc (star (op F k l hk j)), op_inner, if_neg hjr,
    zero_mul, mul_zero]

omit [DecidableEq E] in
theorem unit_formula (i j : Index (source := source) k l)
    (hij : indexVertex (target := target) k l i = indexVertex (target := target) k l j) :
    unit F k l hk i j =
      single k l (row k l i) (row k l j) (coefficient F k l i * star (coefficient F k l j)) := by
  simp only [unit, op, single_star]
  rw [hij, single_mul_same]

omit [DecidableEq E] in
/-- The P matrix units of the two factors agree entry for entry. -/
theorem common_P (v : V) (a b : Fin (k v)) :
    unit F k l hk (Sum.inl ⟨v, a⟩) (Sum.inl ⟨v, b⟩) =
      single k l (Sum.inl ⟨v, a⟩) (Sum.inl ⟨v, b⟩) (F.vertex v) := by
  rw [unit_formula F k l hk (Sum.inl ⟨v, a⟩) (Sum.inl ⟨v, b⟩) rfl]
  change single k l _ _ (F.vertex v * star (F.vertex v)) = _
  rw [(F.vertex_projection v).isSelfAdjoint.star_eq, (F.vertex_projection v).isIdempotentElem.eq]
  rfl

omit [DecidableEq E] in
/-- Each edge copy contributes its actual range projection to a Q block. -/
theorem edge_Q (e : E) (a b : Fin (l (source e))) :
    unit F k l hk (Sum.inr ⟨e, a⟩) (Sum.inr ⟨e, b⟩) =
      single k l (Sum.inr ⟨source e, a⟩) (Sum.inr ⟨source e, b⟩)
        (F.edge e * star (F.edge e)) :=
  unit_formula F k l hk _ _ rfl

omit [Fintype V] in
theorem single_add (i j : Coord k l) (a b : A) :
    single k l i j (a + b) = single k l i j a + single k l i j b :=
  Matrix.single_add _ _ _ _

omit [Fintype V] in
theorem single_sum {T : Type*} (s : Finset T) (i j : Coord k l) (a : T → A) :
    single k l i j (∑ t ∈ s, a t) = ∑ t ∈ s, single k l i j (a t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht, single_add, ih]

omit [DecidableEq E] in
/-- The common Q identity is precisely the CK sum, with arbitrary matrix indices. -/
theorem common_Q (hns : NoSinks source) (w : V) (a b : Fin (l w)) :
    (∑ e ∈ Finset.univ.filter (fun e => source e = w),
      single k l (Sum.inr ⟨w, a⟩) (Sum.inr ⟨w, b⟩) (F.edge e * star (F.edge e))) =
        single k l (Sum.inr ⟨w, a⟩) (Sum.inr ⟨w, b⟩) (F.vertex w) := by
  rw [← single_sum, F.outgoing_of_noSinks hns]

omit [DecidableEq E] in
/-- The mixed F1 block is the edge itself in the appropriate matrix position. -/
theorem mixed_QP (e : E) (b : Fin (l (source e))) (a : Fin (k (target e))) :
    unit F k l hk (Sum.inr ⟨e, b⟩) (Sum.inl ⟨target e, a⟩) =
      single k l (Sum.inr ⟨source e, b⟩) (Sum.inl ⟨target e, a⟩) (F.edge e) := by
  rw [unit_formula F k l hk (Sum.inr ⟨e, b⟩) (Sum.inl ⟨target e, a⟩) rfl]
  change single k l _ _ (F.edge e * star (F.vertex (target e))) = _
  rw [(F.vertex_projection _).isSelfAdjoint.star_eq, F.edge_right_support]
  rfl

omit [DecidableEq E] in
/-- All edge copies over a fixed output coordinate satisfy its CK relation. -/
theorem range_coefficient_sum (hns : NoSinks source) (r : Coord k l) :
    (∑ i : Index (source := source) k l,
      if row k l i = r then coefficient F k l i * star (coefficient F k l i) else 0) =
        F.vertex (coordVertex k l r) := by
  cases r with
  | inl va =>
    simp only [Index, Fintype.sum_sum_type, row, coefficient, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr_ne_inl, ↓reduceIte, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte, coordVertex, Sum.elim_inl,
      (F.vertex_projection va.1).isSelfAdjoint.star_eq,
      (F.vertex_projection va.1).isIdempotentElem.eq]
  | inr wa =>
    rcases wa with ⟨w, a⟩
    simp only [Index, Fintype.sum_sum_type, row, coefficient, Sum.elim_inl, Sum.elim_inr,
      Sum.inl_ne_inr, ↓reduceIte, Finset.sum_const_zero, zero_add, Sum.inr.injEq,
      Fintype.sum_sigma]
    have hcopy (e : E) :
        (∑ b : Fin (l (source e)),
          if (⟨source e, b⟩ : Σ v, Fin (l v)) = ⟨w, a⟩ then
            F.edge e * star (F.edge e) else 0) =
          if source e = w then F.edge e * star (F.edge e) else 0 := by
      by_cases he : source e = w
      · subst w
        simp
      · have hne (b : Fin (l (source e))) :
            (⟨source e, b⟩ : Σ v, Fin (l v)) ≠ ⟨w, a⟩ :=
          fun hh => he (congrArg Sigma.fst hh)
        simp only [hne, ↓reduceIte, Finset.sum_const_zero, he]
    simp only [hcopy]
    simpa only [Finset.sum_filter, coordVertex, Sum.elim_inr] using
      F.outgoing_of_noSinks hns w

omit [DecidableEq E] in
/-- The weighted range projections exhaust the inflated projection q. -/
theorem range_sum (hns : NoSinks source) :
    (∑ i : Index (source := source) k l, unit F k l hk i i) = projection F k l := by
  have hformula (i : Index (source := source) k l) := unit_formula F k l hk i i rfl
  simp only [hformula]
  change (∑ i : Index (source := source) k l,
    Matrix.single (row k l i) (row k l i) (coefficient F k l i * star (coefficient F k l i))) =
      Matrix.diagonal (fun i => F.vertex (coordVertex k l i))
  ext r c
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hrc : r = c
  · subst c
    simp only [Matrix.single_apply, and_self]
    exact range_coefficient_sum F k l hns r
  · rw [if_neg hrc]
    apply Finset.sum_eq_zero
    intro i _
    rw [Matrix.single_apply, if_neg]
    rintro ⟨hr, hc⟩
    exact hrc (hr.symm.trans hc)

/-- First-factor matrix entries, used only within their vertex blocks. -/
def firstUnit (i j : Coord k l) : CStarMatrix (Coord k l) (Coord k l) A :=
  single k l i j (F.vertex (coordVertex k l i))

omit [DecidableEq E] in
theorem firstUnit_star (i j : Coord k l)
    (hij : coordVertex k l i = coordVertex k l j) :
    star (firstUnit F k l i j) = firstUnit F k l j i := by
  simp only [firstUnit, single_star, (F.vertex_projection _).isSelfAdjoint.star_eq, hij]

omit [DecidableEq E] in
theorem firstUnit_mul (i j r s : Coord k l)
    (hij : coordVertex k l i = coordVertex k l j) :
    firstUnit F k l i j * firstUnit F k l r s =
      if j = r then firstUnit F k l i s else 0 := by
  by_cases hjr : j = r
  · subst r
    rw [if_pos rfl]
    simp only [firstUnit, single_mul_same, ← hij, (F.vertex_projection _).isIdempotentElem.eq]
  · rw [if_neg hjr]
    exact single_mul_ne k l _ _ _ _ _ _ hjr

omit [DecidableEq E] in
theorem firstUnit_sum : (∑ i : Coord k l, firstUnit F k l i i) = projection F k l := by
  change (∑ i : Coord k l, Matrix.single i i (F.vertex (coordVertex k l i))) = Matrix.diagonal _
  exact Matrix.sum_single_eq_diagonal _

/-- The distinguished P coordinate inside each second-factor block. -/
def baseIndex (v : V) : Index (source := source) k l := Sum.inl ⟨v, ⟨0, hk v⟩⟩

/-- Every F1 matrix unit is a product of its two columns at the distinguished P coordinate. -/
theorem unit_from_column (i j : Index (source := source) k l) (v : V)
    (hi : indexVertex (target := target) k l i = v)
    (_hj : indexVertex (target := target) k l j = v) :
    unit F k l hk i j =
      unit F k l hk i (baseIndex k l hk v) * star (unit F k l hk j (baseIndex k l hk v)) := by
  rw [unit_star, unit_mul F k l hk _ _ _ _ (by exact hi), if_pos rfl]

/-- The manuscript's recovered graph edge, using the zero-th Q coordinate. -/
def recoveredEdge (hl : ∀ v, 0 < l v) (e : E) : CStarMatrix (Coord k l) (Coord k l) A :=
  firstUnit F k l (base k l hk (source e)) (Sum.inr ⟨source e, ⟨0, hl (source e)⟩⟩) *
    unit F k l hk (Sum.inr ⟨e, ⟨0, hl (source e)⟩⟩) (baseIndex k l hk (target e))

omit [DecidableEq E] in
/-- Recovering a graph edge from the proposed factors returns that actual edge. -/
theorem recoveredEdge_eq (hl : ∀ v, 0 < l v) (e : E) :
    recoveredEdge F k l hk hl e =
      single k l (base k l hk (source e)) (base k l hk (target e)) (F.edge e) := by
  change firstUnit F k l _ _ *
    unit F k l hk (Sum.inr ⟨e, ⟨0, hl (source e)⟩⟩) (Sum.inl ⟨target e, ⟨0, hk (target e)⟩⟩) = _
  rw [mixed_QP]
  simp only [firstUnit, single_mul_same]
  change single k l _ _ (F.vertex (source e) * F.edge e) = _
  rw [F.edge_left_support]
  rfl

omit [DecidableEq E] in
/-- The manuscript's mixed-generator inverse formula holds for every weight index. -/
theorem mixed_recovery (hl : ∀ v, 0 < l v) (e : E)
    (b : Fin (l (source e))) (a : Fin (k (target e))) :
    unit F k l hk (Sum.inr ⟨e, b⟩) (Sum.inl ⟨target e, a⟩) =
      firstUnit F k l (Sum.inr ⟨source e, b⟩) (base k l hk (source e)) *
        recoveredEdge F k l hk hl e *
          firstUnit F k l (base k l hk (target e)) (Sum.inl ⟨target e, a⟩) := by
  rw [mixed_QP, recoveredEdge_eq]
  simp only [firstUnit, single_mul_same]
  change single k l _ _ (F.edge e) =
    single k l _ _ ((F.vertex (source e) * F.edge e) * F.vertex (target e))
  rw [F.edge_left_support, F.edge_right_support]

/-- A Q unit written with source-compatible indices, avoiding implicit casts. -/
def outgoingUnit (w : V) (a b : Fin (l w)) (e : {e : E // source e = w}) :
    CStarMatrix (Coord k l) (Coord k l) A :=
  unit F k l hk
    (Sum.inr ⟨e, e.property.symm ▸ a⟩) (Sum.inr ⟨e, e.property.symm ▸ b⟩)

omit [DecidableEq E] in
theorem outgoingUnit_eq (w : V) (a b : Fin (l w)) (e : {e : E // source e = w}) :
    outgoingUnit F k l hk w a b e =
      single k l (Sum.inr ⟨w, a⟩) (Sum.inr ⟨w, b⟩) (F.edge e * star (F.edge e)) := by
  rcases e with ⟨e, he⟩
  subst w
  exact edge_Q F k l hk e a b

omit [DecidableEq E] in
/-- Genuine equality of the two candidate common Q images, including dependent weights. -/
theorem common_Q_units (hns : NoSinks source) (w : V) (a b : Fin (l w)) :
    (∑ e : {e : E // source e = w}, outgoingUnit F k l hk w a b e) =
      firstUnit F k l (Sum.inr ⟨w, a⟩) (Sum.inr ⟨w, b⟩) := by
  simp only [outgoingUnit_eq]
  exact (Finset.sum_subtype (Finset.univ.filter (fun e => source e = w))
    (by simp) (fun e => single k l (Sum.inr ⟨w, a⟩) (Sum.inr ⟨w, b⟩)
      (F.edge e * star (F.edge e)))).symm.trans (common_Q F k l hns w a b)

/-- The actual second-factor coordinates over vertex v. -/
abbrev BlockIndex (v : V) := {i : Index (source := source) k l // indexVertex (target := target) k l i = v}

/-- The second-factor matrix units, now as elements of the actual corner. -/
def blockUnit (v : V) (i j : BlockIndex (source := source) (target := target) k l v) :
    CommonCorner.Corner (projection_isProjection F k l) :=
  opInCorner F k l hk i * star (opInCorner F k l hk j)

omit [DecidableEq E] in
@[simp] theorem blockUnit_coe (v : V)
    (i j : BlockIndex (source := source) (target := target) k l v) :
    (blockUnit F k l hk v i j : CStarMatrix (Coord k l) (Coord k l) A) = unit F k l hk i j := rfl

theorem blockUnit_mul (v : V)
    (i j r s : BlockIndex (source := source) (target := target) k l v) :
    blockUnit F k l hk v i j * blockUnit F k l hk v r s =
      if j = r then blockUnit F k l hk v i s else 0 := by
  apply Subtype.ext
  change unit F k l hk i j * unit F k l hk r s =
    ((if j = r then blockUnit F k l hk v i s else 0) : CommonCorner.Corner _).val
  rw [unit_mul F k l hk _ _ _ _ (i.property.trans j.property.symm)]
  by_cases hjr : j = r
  · subst r; simp
  · have hval : j.val ≠ r.val := fun h => hjr (Subtype.ext h)
    simp only [if_neg hjr, if_neg hval]
    rfl

omit [DecidableEq E] in
@[simp] theorem blockUnit_star (v : V)
    (i j : BlockIndex (source := source) (target := target) k l v) :
    star (blockUnit F k l hk v i j) = blockUnit F k l hk v j i := by
  simp only [blockUnit, star_mul, star_star]

/-- Each full matrix block has a genuine star representation in the graph corner. -/
def blockHom (v : V) :
    CStarMatrix (BlockIndex (source := source) (target := target) k l v)
      (BlockIndex (source := source) (target := target) k l v) ℂ →⋆ₙₐ[ℂ]
        CommonCorner.Corner (projection_isProjection F k l) :=
  matrixUnitHom (blockUnit F k l hk v) (blockUnit_mul F k l hk v) (blockUnit_star F k l hk v)

@[simp] theorem blockHom_single (v : V)
    (i j : BlockIndex (source := source) (target := target) k l v) (z : ℂ) :
    blockHom F k l hk v (CStarMatrix.ofMatrix (Matrix.single i j z)) = z • blockUnit F k l hk v i j :=
  matrixEval_single _ i j z

theorem blockHom_one (v : V) :
    blockHom F k l hk v 1 = ∑ i, blockUnit F k l hk v i i := by
  change matrixEval (blockUnit F k l hk v) (1 : Matrix _ _ ℂ) = _
  rw [← Matrix.sum_single_one]
  simp

theorem blockHom_sum_one (hns : NoSinks source) : (∑ v, blockHom F k l hk v 1) = 1 := by
  simp only [blockHom_one]
  apply Subtype.ext
  simp only [CommonCorner.coe_sum, blockUnit_coe, CommonCorner.coe_one]
  exact (Fintype.sum_fiberwise (indexVertex (target := target) k l)
    (fun i => unit F k l hk i i)).trans (range_sum F k l hk hns)

/-- The actual finite product of incoming full matrix blocks, indexed by weighted slots. -/
abbrev Factor := ∀ v : V,
  CStarMatrix (BlockIndex (source := source) (target := target) k l v)
    (BlockIndex (source := source) (target := target) k l v) ℂ

theorem blockHom_apply (v : V) (a : CStarMatrix
    (BlockIndex (source := source) (target := target) k l v)
    (BlockIndex (source := source) (target := target) k l v) ℂ) :
    blockHom F k l hk v a =
      ∑ i, ∑ j, (CStarMatrix.ofMatrix.symm a i j) • blockUnit F k l hk v i j := by
  exact Matrix.liftLinear_apply _ _ _

theorem blockUnit_mul_other (v w : V) (hvw : v ≠ w)
    (i j : BlockIndex (source := source) (target := target) k l v)
    (r s : BlockIndex (source := source) (target := target) k l w) :
    blockUnit F k l hk v i j * blockUnit F k l hk w r s = 0 := by
  apply Subtype.ext
  change unit F k l hk i j * unit F k l hk r s = 0
  apply unit_mul_of_vertex_ne
  simpa only [j.property, r.property] using hvw

theorem blockHom_mul_other (v w : V) (hvw : v ≠ w)
    (a : CStarMatrix (BlockIndex (source := source) (target := target) k l v)
      (BlockIndex (source := source) (target := target) k l v) ℂ)
    (b : CStarMatrix (BlockIndex (source := source) (target := target) k l w)
      (BlockIndex (source := source) (target := target) k l w) ℂ) :
    blockHom F k l hk v a * blockHom F k l hk w b = 0 := by
  simp only [blockHom_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_smul,
    blockUnit_mul_other F k l hk v w hvw, smul_zero, Finset.sum_const_zero]

/-- The proposed weighted second-factor representation is a genuine unital complex
star homomorphism to the concrete graph corner. Its unit proof is the CK range sum. -/
def factorHom (hns : NoSinks source) :
    Factor (source := source) (target := target) k l →⋆ₐ[ℂ]
      CommonCorner.Corner (projection_isProjection F k l) where
  toFun a := ∑ v, blockHom F k l hk v (a v)
  map_zero' := by simp
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_one' := blockHom_sum_one F k l hk hns
  map_mul' a b := by
    simp only [Pi.mul_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
    symm
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_eq_single v]
    · intro w _ hw
      exact blockHom_mul_other F k l hk w v hw (a w) (b v)
    · simp
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply, map_smul,
      ← Finset.smul_sum, blockHom_sum_one F k l hk hns]
  map_star' a := by simp only [Pi.star_apply, map_star, star_sum]

/-- Formula for the actual weighted factor representation. -/
theorem factorHom_apply (hns : NoSinks source)
    (a : Factor (source := source) (target := target) k l) :
    factorHom F k l hk hns a =
      ∑ v, ∑ i, ∑ j, (CStarMatrix.ofMatrix.symm (a v) i j) • blockUnit F k l hk v i j := by
  change (∑ v, blockHom F k l hk v (a v)) = _
  simp only [blockHom_apply]

abbrev FirstBlockIndex (v : V) := {i : Coord k l // coordVertex k l i = v}
abbrev FirstFactor := ∀ v : V, CStarMatrix (FirstBlockIndex k l v) (FirstBlockIndex k l v) ℂ

/-- A first-factor matrix unit in the actual corner. -/
def firstBlockUnit (v : V) (i j : FirstBlockIndex k l v) :
    CommonCorner.Corner (projection_isProjection F k l) :=
  CommonCorner.ofSupport (projection_isProjection F k l) (firstUnit F k l i j)
    (by
      change projection F k l * single k l i j _ = _
      rw [projection_mul_single, (F.vertex_projection _).isIdempotentElem.eq]
      rfl)
    (by
      change single k l i j _ * projection F k l = _
      rw [single_mul_projection, i.property, j.property, (F.vertex_projection _).isIdempotentElem.eq]
      simp only [firstUnit, i.property])

omit [DecidableEq E] in
@[simp] theorem firstBlockUnit_coe (v : V) (i j : FirstBlockIndex k l v) :
    (firstBlockUnit F k l v i j : CStarMatrix (Coord k l) (Coord k l) A) =
      firstUnit F k l i j := rfl

omit [DecidableEq E] in
theorem firstBlockUnit_mul (v : V) (i j r s : FirstBlockIndex k l v) :
    firstBlockUnit F k l v i j * firstBlockUnit F k l v r s =
      if j = r then firstBlockUnit F k l v i s else 0 := by
  apply Subtype.ext
  change firstUnit F k l i j * firstUnit F k l r s =
    ((if j = r then firstBlockUnit F k l v i s else 0) : CommonCorner.Corner _).val
  rw [firstUnit_mul F k l _ _ _ _ (i.property.trans j.property.symm)]
  by_cases hjr : j = r
  · subst r; simp
  · have hval : j.val ≠ r.val := fun h => hjr (Subtype.ext h)
    simp only [if_neg hjr, if_neg hval]
    rfl

omit [DecidableEq E] in
theorem firstBlockUnit_star (v : V) (i j : FirstBlockIndex k l v) :
    star (firstBlockUnit F k l v i j) = firstBlockUnit F k l v j i := by
  apply Subtype.ext
  exact firstUnit_star F k l i j (i.property.trans j.property.symm)

/-- Genuine first-factor block homomorphisms, before summing the orthogonal blocks. -/
def firstBlockHom (v : V) :
    CStarMatrix (FirstBlockIndex k l v) (FirstBlockIndex k l v) ℂ →⋆ₙₐ[ℂ]
      CommonCorner.Corner (projection_isProjection F k l) :=
  matrixUnitHom (firstBlockUnit F k l v) (firstBlockUnit_mul F k l v) (firstBlockUnit_star F k l v)

omit [DecidableEq E] in
theorem firstBlockHom_apply (v : V) (a : CStarMatrix (FirstBlockIndex k l v) (FirstBlockIndex k l v) ℂ) :
    firstBlockHom F k l v a = ∑ i, ∑ j, (CStarMatrix.ofMatrix.symm a i j) • firstBlockUnit F k l v i j :=
  Matrix.liftLinear_apply _ _ _

omit [DecidableEq E] in
theorem firstBlockHom_sum_one : (∑ v, firstBlockHom F k l v 1) = 1 := by
  have hone (v : V) : firstBlockHom F k l v 1 = ∑ i, firstBlockUnit F k l v i i := by
    change matrixEval (firstBlockUnit F k l v) (1 : Matrix _ _ ℂ) = _
    rw [← Matrix.sum_single_one]
    simp
  simp only [hone]
  apply Subtype.ext
  simp only [CommonCorner.coe_sum, firstBlockUnit_coe, CommonCorner.coe_one]
  exact (Fintype.sum_fiberwise (coordVertex k l)
    (fun i => firstUnit F k l i i)).trans (firstUnit_sum F k l)

omit [DecidableEq E] in
theorem firstBlockUnit_mul_other (v w : V) (hvw : v ≠ w)
    (i j : FirstBlockIndex k l v) (r s : FirstBlockIndex k l w) :
    firstBlockUnit F k l v i j * firstBlockUnit F k l w r s = 0 := by
  apply Subtype.ext
  change firstUnit F k l i j * firstUnit F k l r s = 0
  rw [firstUnit_mul F k l _ _ _ _ (i.property.trans j.property.symm), if_neg]
  intro h
  exact hvw (j.property.symm.trans ((congrArg (coordVertex k l) h).trans r.property))

omit [DecidableEq E] in
theorem firstBlockHom_mul_other (v w : V) (hvw : v ≠ w)
    (a : CStarMatrix (FirstBlockIndex k l v) (FirstBlockIndex k l v) ℂ)
    (b : CStarMatrix (FirstBlockIndex k l w) (FirstBlockIndex k l w) ℂ) :
    firstBlockHom F k l v a * firstBlockHom F k l w b = 0 := by
  simp only [firstBlockHom_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_smul,
    firstBlockUnit_mul_other F k l v w hvw, smul_zero, Finset.sum_const_zero]

/-- The genuine unital first-factor representation into the graph corner. -/
def firstFactorHom : FirstFactor k l →⋆ₐ[ℂ] CommonCorner.Corner (projection_isProjection F k l) where
  toFun a := ∑ v, firstBlockHom F k l v (a v)
  map_zero' := by simp
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_one' := firstBlockHom_sum_one F k l
  map_mul' a b := by
    simp only [Pi.mul_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
    symm
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_eq_single v]
    · intro w _ hw
      exact firstBlockHom_mul_other F k l w v hw (a w) (b v)
    · simp
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply, map_smul,
      ← Finset.smul_sum, firstBlockHom_sum_one F k l]
  map_star' a := by simp only [Pi.star_apply, map_star, star_sum]

omit [DecidableEq E] in
/-- Exact incoming block dimension, before any enumeration by Fin. -/
theorem card_BlockIndex (v : V) :
    Fintype.card (BlockIndex (source := source) (target := target) k l v) =
      k v + ∑ e : E, if target e = v then l (source e) else 0 := by
  simp only [BlockIndex, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Index, Fintype.sum_sum_type, Fintype.sum_sigma, indexVertex, Sum.elim_inl, Sum.elim_inr]
  change (∑ w : V, ∑ _a : Fin (k w), if w = v then 1 else 0) +
    (∑ e : E, ∑ _b : Fin (l (source e)), if target e = v then 1 else 0) = _
  simp only [Finset.sum_ite_irrel]
  simp

omit [Fintype E] [DecidableEq E] in
/-- Exact first-factor block dimension. -/
theorem card_FirstBlockIndex (v : V) :
    Fintype.card (FirstBlockIndex k l v) = k v + l v := by
  simp only [FirstBlockIndex, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Coord, Fintype.sum_sum_type, Fintype.sum_sigma, coordVertex, Sum.elim_inl, Sum.elim_inr]
  change (∑ w : V, ∑ _a : Fin (k w), if w = v then 1 else 0) +
    (∑ w : V, ∑ _b : Fin (l w), if w = v then 1 else 0) = _
  simp only [Finset.sum_ite_irrel]
  simp

/-- For A(v,w) edges w→v, the constructed second factor has exactly the manuscript's dimension. -/
theorem card_matrixBlockIndex (M : Matrix V V ℕ) (v : V) :
    Fintype.card (BlockIndex (source := matrixSource M) (target := matrixTarget M) k l v) =
      k v + ∑ w : V, M v w * l w := by
  rw [card_BlockIndex]
  simp only [MatrixEdge, Fintype.sum_sigma, matrixSource, matrixTarget]
  change k v + (∑ w : V, ∑ v' : V, ∑ _e : Fin (M v' w), if v' = v then l w else 0) = _
  simp only [Finset.sum_ite_irrel]
  simp

/-- Both finite factor representations are contractive for the actual C*-norms. -/
theorem factorHom_contractive (hns : NoSinks source)
    (a : Factor (source := source) (target := target) k l) :
    ‖factorHom F k l hk hns a‖ ≤ ‖a‖ := by
  have : CStarAlgebra (Factor (source := source) (target := target) k l) := {}
  exact NonUnitalStarAlgHom.norm_apply_le (factorHom F k l hk hns) a

omit [DecidableEq E] in
theorem firstFactorHom_contractive (a : FirstFactor k l) :
    ‖firstFactorHom F k l a‖ ≤ ‖a‖ := by
  have : CStarAlgebra (FirstFactor k l) := {}
  exact NonUnitalStarAlgHom.norm_apply_le (firstFactorHom F k l) a

end Suzuki.WeightedGraphAmalgam

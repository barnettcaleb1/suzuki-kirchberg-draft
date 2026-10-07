import Suzuki.GraphAmalgamInverse
import Suzuki.GraphDensity
import Suzuki.UniversalAmalgam
import Suzuki.FullProjectionFrame

/-!
# Extending the concrete weighted graph inverse over both finite factors

The actual backward map extends both entire finite factors. A compressed-entry
argument proves norm generation and uniqueness, then proves both inverse
composites for an actual full amalgam satisfying the displayed finite common
relations. The weighted graph projection is algebraically full. The manuscript's
specific common inclusions still must be instantiated and checked against these
relations; no such correspondence or K-class calculation is assumed proved.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace Suzuki.GraphCornerIdentification
open GraphRelations WeightedGraphAmalgam GraphAmalgamInverse
universe u
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {source target : E → V}
  (k l : V → ℕ) (hk : ∀ v, 0 < k v) (hl : ∀ v, 0 < l v)
  {C : Type u} [CStarAlgebra C]
  (S : MatrixUnits (coordVertex k l) C)
  (T : MatrixUnits (indexVertex (source := source) (target := target) k l) C)
  (H : AllCommon k l hk hl S T)
local instance graphOrder : PartialOrder (GraphUniversal.Algebra.{u} source target) :=
  CStarAlgebra.spectralOrder _
local instance graphOrderedRing : StarOrderedRing (GraphUniversal.Algebra.{u} source target) :=
  CStarAlgebra.spectralOrderedRing _

abbrev graphFamily := GraphUniversal.family.{u} source target
abbrev graphCorner := CommonCorner.Corner (projection_isProjection (graphFamily.{u} (source := source) (target := target)) k l)

/-- Every first-factor matrix unit has the required inverse image. -/
theorem backward_firstBlock (v : V) (i j : FirstBlockIndex k l v) :
    backward k l hk hl S T H.toCommon
      (firstBlockUnit (graphFamily.{u} (source := source) (target := target)) k l v i j) =
        S.unit i.val j.val := by
  exact backward_first (source := source) (target := target) k l hk hl S T H.toCommon
    i.val j.val (i.property.trans j.property.symm)

/-- The whole first factor is recovered, not just its matrix generators. -/
theorem backward_firstFactor (a : FirstFactor k l) :
    backward k l hk hl S T H.toCommon
      (firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l a) =
        S.representation a := by
  change backward k l hk hl S T H.toCommon (∑ v, firstBlockHom _ k l v (a v)) =
    ∑ v, S.blockHom v (a v)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  simp only [firstBlockHom_apply, map_sum, map_smul, backward_firstBlock k l hk hl S T H,
    MatrixUnits.blockHom_apply]

/-- The distinguished column of the second factor is recovered for both kinds
of index, including every outgoing edge copy. -/
theorem backward_column (i : Index (source := source) k l) :
    backward k l hk hl S T H.toCommon
      (blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk
        (indexVertex (target := target) k l i) ⟨i, rfl⟩
        ⟨baseIndex k l hk (indexVertex (target := target) k l i), rfl⟩) =
      T.unit i (FP k l hk (indexVertex (target := target) k l i)) := by
  cases i with
  | inl va =>
    rcases va with ⟨v, a⟩
    have he : blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v
        ⟨pIndex k l v a, rfl⟩ ⟨FP k l hk v, rfl⟩ =
      firstImage (source := source) (target := target) k l
        (pCoord k l v a) (P k l hk v) rfl := by
      apply Subtype.ext
      exact common_P _ k l hk v a ⟨0, hk v⟩
    change backward k l hk hl S T H.toCommon
      (blockUnit _ k l hk v ⟨pIndex k l v a, rfl⟩ ⟨FP k l hk v, rfl⟩) = _
    rw [he, backward_first]
    exact H.P_all v a ⟨0, hk v⟩
  | inr eb =>
    rcases eb with ⟨e, b⟩
    have he : blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk (target e)
        ⟨qIndex k l e b, rfl⟩ ⟨FP k l hk (target e), rfl⟩ =
      mixedImage (source := source) (target := target) k l e b ⟨0, hk (target e)⟩ := by
      apply Subtype.ext
      exact mixed_QP _ k l hk e b ⟨0, hk (target e)⟩
    change backward k l hk hl S T H.toCommon
      (blockUnit _ k l hk (target e) ⟨qIndex k l e b, rfl⟩ ⟨FP k l hk (target e), rfl⟩) = _
    rw [he]
    exact backward_mixed (source := source) (target := target) k l hk hl S T H.toCommon H
      e b ⟨0, hk (target e)⟩

/-- Every second-factor matrix unit follows from its distinguished column. -/
theorem backward_secondBlock (v : V)
    (i j : BlockIndex (source := source) (target := target) k l v) :
    backward k l hk hl S T H.toCommon
      (blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v i j) =
        T.unit i.val j.val := by
  let b : BlockIndex (source := source) (target := target) k l v := ⟨baseIndex k l hk v, rfl⟩
  have he : blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v i j =
      blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v i b *
        star (blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v j b) := by
    rw [blockUnit_star, blockUnit_mul, if_pos rfl]
  rw [he, map_mul, map_star]
  have hi : backward k l hk hl S T H.toCommon
      (blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v i b) =
      T.unit i.val (FP k l hk v) := by
    have he : blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v i b =
        blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk
          (indexVertex (target := target) k l i.val) ⟨i.val, rfl⟩
          ⟨baseIndex k l hk (indexVertex (target := target) k l i.val), rfl⟩ := by
      apply Subtype.ext
      change unit _ k l hk i.val (baseIndex k l hk v) =
        unit _ k l hk i.val (baseIndex k l hk (indexVertex (target := target) k l i.val))
      rw [i.property]
    rw [he, backward_column k l hk hl S T H, i.property]
  have hj : backward k l hk hl S T H.toCommon
      (blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v j b) =
      T.unit j.val (FP k l hk v) := by
    have he : blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v j b =
        blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk
          (indexVertex (target := target) k l j.val) ⟨j.val, rfl⟩
          ⟨baseIndex k l hk (indexVertex (target := target) k l j.val), rfl⟩ := by
      apply Subtype.ext
      change unit _ k l hk j.val (baseIndex k l hk v) =
        unit _ k l hk j.val (baseIndex k l hk (indexVertex (target := target) k l j.val))
      rw [j.property]
    rw [he, backward_column k l hk hl S T H, j.property]
  rw [hi, hj]
  exact (GraphAmalgamInverse.unit_from_column k l hk T v i.val j.val i.property j.property).symm

/-- Full second-factor restriction, proved by summing actual matrix entries. -/
theorem backward_secondFactor (hns : NoSinks source)
    (a : Factor (source := source) (target := target) k l) :
    backward k l hk hl S T H.toCommon
      (factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns a) =
        T.representation a := by
  rw [factorHom_apply]
  change backward k l hk hl S T H.toCommon _ = ∑ v, T.blockHom v (a v)
  simp only [map_sum, map_smul, backward_secondBlock k l hk hl S T H, MatrixUnits.blockHom_apply]


/-- Compress one actual graph-algebra entry into the weighted matrix corner. -/
def entry (i j : Coord k l) : GraphUniversal.Algebra.{u} source target →ₗ[ℂ]
    graphCorner.{u} (source := source) (target := target) k l where
  toFun x := CommonCorner.compress
    (projection_isProjection (graphFamily.{u} (source := source) (target := target)) k l) (single k l i j x)
  map_add' x y := by rw [single_add, map_add]
  map_smul' z x := by
    have h : single k l i j (z • x) = z • single k l i j x := by
      apply CStarMatrix.ext
      intro a b
      simp [single, Matrix.single_apply]
    rw [h, map_smul]
    rfl

omit [DecidableEq E] in
@[simp] theorem entry_coe (i j : Coord k l) (x : GraphUniversal.Algebra.{u} source target) :
    (entry k l i j x : CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{u} source target)) =
      single k l i j (GraphUniversal.vertex.{u} source target (coordVertex k l i) * x *
        GraphUniversal.vertex.{u} source target (coordVertex k l j)) := by
  change projection (graphFamily.{u} (source := source) (target := target)) k l * single k l i j x * projection (graphFamily.{u} (source := source) (target := target)) k l = _
  rw [projection_mul_single, single_mul_projection]
  rfl

omit [DecidableEq E] in
theorem entry_continuous (i j : Coord k l) :
    Continuous (entry.{u} (source := source) (target := target) k l i j) := by
  apply Continuous.subtype_mk
  change Continuous (fun x => projection (graphFamily.{u} (source := source) (target := target)) k l * single k l i j x * projection (graphFamily.{u} (source := source) (target := target)) k l)
  apply Continuous.mul _ continuous_const
  apply Continuous.mul continuous_const
  apply CStarMatrix.ofMatrixL.continuous.comp
  exact continuous_pi fun a => continuous_pi fun b => by
    simp only [id_eq, Matrix.single_apply]
    split_ifs <;> fun_prop

omit [DecidableEq E] in
theorem entry_star (i j : Coord k l) (x : GraphUniversal.Algebra.{u} source target) :
    entry k l i j (star x) = star (entry k l j i x) := by
  apply Subtype.ext
  simp only [entry_coe, CommonCorner.coe_star, single_star, star_mul,
    (GraphUniversal.vertex_projection.{u} source target _).isSelfAdjoint.star_eq]
  congr 1
  noncomm_ring

omit [DecidableEq E] in
/-- Multiplication inserts the actual sum of vertex projections, once each. -/
theorem entry_mul (i j : Coord k l) (x y : GraphUniversal.Algebra.{u} source target) :
    entry k l i j (x * y) = ∑ v : V, entry k l i (base k l hk v) x * entry k l (base k l hk v) j y := by
  apply Subtype.ext
  simp only [entry_coe, CommonCorner.coe_sum, CommonCorner.coe_mul, single_mul_same]
  change single k l i j (_ * (x * y) * _) =
    ∑ v, single k l i j ((_ * x * GraphUniversal.vertex.{u} source target v) *
      (GraphUniversal.vertex.{u} source target v * y * _))
  rw [← single_sum]
  congr 1
  have hp (v : V) :
      (GraphUniversal.vertex.{u} source target (coordVertex k l i) * x * GraphUniversal.vertex.{u} source target v) *
      (GraphUniversal.vertex.{u} source target v * y * GraphUniversal.vertex.{u} source target (coordVertex k l j)) =
      (GraphUniversal.vertex.{u} source target (coordVertex k l i) * x) * GraphUniversal.vertex.{u} source target v *
        (y * GraphUniversal.vertex.{u} source target (coordVertex k l j)) := by
    have h := (GraphUniversal.vertex_projection.{u} source target v).isIdempotentElem.eq
    calc
      _ = (GraphUniversal.vertex.{u} source target (coordVertex k l i) * x) *
        (GraphUniversal.vertex.{u} source target v * GraphUniversal.vertex.{u} source target v) *
        (y * GraphUniversal.vertex.{u} source target (coordVertex k l j)) := by noncomm_ring
      _ = _ := by rw [h]
  symm
  calc
    _ = ∑ v, (GraphUniversal.vertex.{u} source target (coordVertex k l i) * x) *
        GraphUniversal.vertex.{u} source target v * (y * GraphUniversal.vertex.{u} source target (coordVertex k l j)) :=
      Finset.sum_congr rfl (fun v _ => hp v)
    _ = (GraphUniversal.vertex.{u} source target (coordVertex k l i) * x) *
        (∑ v, GraphUniversal.vertex.{u} source target v) *
        (y * GraphUniversal.vertex.{u} source target (coordVertex k l j)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by rw [GraphUniversal.vertex_sum.{u} source target, mul_one]; noncomm_ring

/-- Testing all actual compressed entries defines a closed star subalgebra of
Graph. This will propagate generator membership to the norm completion. -/
def coefficientAlgebra (Z : StarSubalgebra ℂ (graphCorner.{u} (source := source) (target := target) k l))
    (h1 : ∀ i j, entry k l i j (1 : GraphUniversal.Algebra.{u} source target) ∈ Z) :
    StarSubalgebra ℂ (GraphUniversal.Algebra.{u} source target) where
  carrier := {x | ∀ i j, entry k l i j x ∈ Z}
  mul_mem' hx hy i j := by
    rw [entry_mul k l hk]
    exact Z.sum_mem fun v _ => Z.mul_mem (hx i (base k l hk v)) (hy (base k l hk v) j)
  add_mem' hx hy i j := by rw [map_add]; exact Z.add_mem (hx i j) (hy i j)
  algebraMap_mem' z i j := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    exact Z.smul_mem (h1 i j) z
  star_mem' hx i j := by rw [entry_star]; exact star_mem (hx j i)

omit [DecidableEq E] in
theorem coefficientAlgebra_closed
    (Z : StarSubalgebra ℂ (graphCorner.{u} (source := source) (target := target) k l))
    (h1 : ∀ i j, entry k l i j (1 : GraphUniversal.Algebra.{u} source target) ∈ Z)
    (hZ : IsClosed (Z : Set (graphCorner.{u} (source := source) (target := target) k l))) :
    IsClosed (coefficientAlgebra k l hk Z h1 : Set (GraphUniversal.Algebra.{u} source target)) := by
  change IsClosed {x | ∀ i j, entry k l i j x ∈ Z}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    hZ.preimage (entry_continuous k l i j)


omit [DecidableEq E] in
/-- The unit entries lie in the first-factor algebra, including the zero
entries between different vertices. -/
theorem entry_one_mem
    (Z : StarSubalgebra ℂ (graphCorner.{u} (source := source) (target := target) k l))
    (hfirst : ∀ i j (hij : coordVertex k l i = coordVertex k l j),
      firstImage (source := source) (target := target) k l i j hij ∈ Z)
    (i j : Coord k l) : entry k l i j (1 : GraphUniversal.Algebra.{u} source target) ∈ Z := by
  by_cases hij : coordVertex k l i = coordVertex k l j
  · have he : entry k l i j (1 : GraphUniversal.Algebra.{u} source target) =
        firstImage (source := source) (target := target) k l i j hij := by
      apply Subtype.ext
      rw [entry_coe]
      change single k l i j (_ * 1 * _) = single k l i j _
      rw [mul_one, ← hij, (GraphUniversal.vertex_projection.{u} source target _).isIdempotentElem.eq]
    rw [he]; exact hfirst i j hij
  · have he : entry k l i j (1 : GraphUniversal.Algebra.{u} source target) = 0 := by
      apply Subtype.ext
      rw [entry_coe]
      change single k l i j (_ * 1 * _) = 0
      rw [mul_one, GraphUniversal.vertex_orthogonal.{u} source target _ _ hij, single_zero]
    rw [he]; exact Z.zero_mem

omit [DecidableEq E] in
theorem entry_vertex_mem
    (Z : StarSubalgebra ℂ (graphCorner.{u} (source := source) (target := target) k l))
    (hfirst : ∀ i j (hij : coordVertex k l i = coordVertex k l j),
      firstImage (source := source) (target := target) k l i j hij ∈ Z)
    (v : V) (i j : Coord k l) : entry k l i j (GraphUniversal.vertex.{u} source target v) ∈ Z := by
  by_cases hi : coordVertex k l i = v
  · by_cases hj : v = coordVertex k l j
    · have he : entry k l i j (GraphUniversal.vertex.{u} source target v) =
          firstImage (source := source) (target := target) k l i j (hi.trans hj) := by
        apply Subtype.ext
        rw [entry_coe]
        change single k l i j (_ * _ * _) = single k l i j _
        rw [hi, ← hj, (GraphUniversal.vertex_projection.{u} source target v).isIdempotentElem.eq,
          (GraphUniversal.vertex_projection.{u} source target v).isIdempotentElem.eq]
      rw [he]; exact hfirst i j (hi.trans hj)
    · have he : entry k l i j (GraphUniversal.vertex.{u} source target v) = 0 := by
        apply Subtype.ext
        rw [entry_coe]
        change single k l i j (_ * _ * _) = 0
        rw [hi, (GraphUniversal.vertex_projection.{u} source target v).isIdempotentElem.eq,
          GraphUniversal.vertex_orthogonal.{u} source target _ _ hj, single_zero]
      rw [he]; exact Z.zero_mem
  · have he : entry k l i j (GraphUniversal.vertex.{u} source target v) = 0 := by
      apply Subtype.ext
      rw [entry_coe]
      change single k l i j (_ * _ * _) = 0
      rw [GraphUniversal.vertex_orthogonal.{u} source target _ _ hi, zero_mul, single_zero]
    rw [he]; exact Z.zero_mem

omit [DecidableEq E] in
include hk hl in
/-- Arbitrary supported edge entries are products of actual first-factor and
mixed second-factor units. No generation assumption is used. -/
theorem entry_edge_mem
    (Z : StarSubalgebra ℂ (graphCorner.{u} (source := source) (target := target) k l))
    (hfirst : ∀ i j (hij : coordVertex k l i = coordVertex k l j),
      firstImage (source := source) (target := target) k l i j hij ∈ Z)
    (hmixed : ∀ (e : E) (b : Fin (l (source e))) (a : Fin (k (target e))),
      mixedImage (source := source) (target := target) k l e b a ∈ Z)
    (e : E) (i j : Coord k l) : entry k l i j (GraphUniversal.edge.{u} source target e) ∈ Z := by
  by_cases hi : coordVertex k l i = source e
  · by_cases hj : target e = coordVertex k l j
    · have he : entry k l i j (GraphUniversal.edge.{u} source target e) =
          firstImage (source := source) (target := target) k l i (Q k l hl (source e)) hi *
          mixedImage (source := source) (target := target) k l e ⟨0, hl (source e)⟩ ⟨0, hk (target e)⟩ *
          firstImage (source := source) (target := target) k l (P k l hk (target e)) j hj := by
        apply Subtype.ext
        rw [entry_coe]
        change single k l i j (_ * _ * _) =
          single k l i (Q k l hl (source e)) (GraphUniversal.vertex.{u} source target (coordVertex k l i)) *
          single k l (Q k l hl (source e)) (P k l hk (target e)) (GraphUniversal.edge.{u} source target e) *
          single k l (P k l hk (target e)) j (GraphUniversal.vertex.{u} source target (target e))
        rw [single_mul_same, single_mul_same, ← hj]
      rw [he]
      exact Z.mul_mem (Z.mul_mem (hfirst i (Q k l hl (source e)) hi) (hmixed e _ _)) (hfirst (P k l hk (target e)) j hj)
    · have he : entry k l i j (GraphUniversal.edge.{u} source target e) = 0 := by
        apply Subtype.ext
        rw [entry_coe]
        change single k l i j (_ * _ * _) = 0
        have hleft : GraphUniversal.vertex.{u} source target (source e) * GraphUniversal.edge.{u} source target e = GraphUniversal.edge.{u} source target e :=
          (graphFamily.{u} (source := source) (target := target)).edge_left_support e
        have hright : GraphUniversal.edge.{u} source target e * GraphUniversal.vertex.{u} source target (coordVertex k l j) = 0 :=
          (graphFamily.{u} (source := source) (target := target)).edge_vertex_zero e _ hj
        rw [hi, hleft, hright, single_zero]
      rw [he]; exact Z.zero_mem
  · have he : entry k l i j (GraphUniversal.edge.{u} source target e) = 0 := by
      apply Subtype.ext
      rw [entry_coe]
      change single k l i j (_ * _ * _) = 0
      have hleft : GraphUniversal.vertex.{u} source target (coordVertex k l i) * GraphUniversal.edge.{u} source target e = 0 :=
        (graphFamily.{u} (source := source) (target := target)).vertex_edge_zero _ e hi
      rw [hleft, zero_mul, single_zero]
    rw [he]; exact Z.zero_mem

omit [DecidableEq E] in
include hk hl in
/-- Norm closure of the graph generators implies norm closure of all weighted
corner entries. -/
theorem all_entries_mem
    (Z : StarSubalgebra ℂ (graphCorner.{u} (source := source) (target := target) k l))
    (hZ : IsClosed (Z : Set (graphCorner.{u} (source := source) (target := target) k l)))
    (hfirst : ∀ i j (hij : coordVertex k l i = coordVertex k l j),
      firstImage (source := source) (target := target) k l i j hij ∈ Z)
    (hmixed : ∀ (e : E) (b : Fin (l (source e))) (a : Fin (k (target e))),
      mixedImage (source := source) (target := target) k l e b a ∈ Z)
    (x : GraphUniversal.Algebra.{u} source target) (i j : Coord k l) : entry k l i j x ∈ Z := by
  let A := coefficientAlgebra k l hk Z (entry_one_mem k l Z hfirst)
  have hle : (graphFamily.{u} (source := source) (target := target)).generated ≤ A :=
    (graphFamily.{u} (source := source) (target := target)).generated_le A
      (coefficientAlgebra_closed k l hk Z _ hZ)
      (fun v => entry_vertex_mem k l Z hfirst v)
      (fun e => entry_edge_mem k l hk hl Z hfirst hmixed e)
  have hx : x ∈ A := hle (by rw [GraphDensity.generated_eq_top]; trivial)
  exact hx i j

omit [DecidableEq E] in
/-- Every actual corner matrix is reconstructed from its compressed entries. -/
theorem entry_reconstruction (M : graphCorner.{u} (source := source) (target := target) k l) :
    (∑ i, ∑ j, entry k l i j (M.val i j)) = M := by
  let A : CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{u} source target) := M.val
  let L := CommonCorner.compress (projection_isProjection (graphFamily.{u} (source := source) (target := target)) k l)
  have hM : (∑ i, ∑ j, single k l i j (A i j)) = A := by
    change CStarMatrix.ofMatrix (∑ i, ∑ j, Matrix.single i j (A i j)) = _
    rw [Matrix.sum_sum_single]
    rfl
  calc
    _ = L (∑ i, ∑ j, single k l i j (A i j)) := by
      simp only [map_sum]
      rfl
    _ = M := by
      rw [hM]
      exact CommonCorner.compress_coe _ M

omit [DecidableEq E] in
include hk hl in
/-- The first and mixed second-factor matrix units generate the entire weighted
corner as a norm-closed star algebra. -/
theorem corner_eq_top_of_generators
    (Z : StarSubalgebra ℂ (graphCorner.{u} (source := source) (target := target) k l))
    (hZ : IsClosed (Z : Set (graphCorner.{u} (source := source) (target := target) k l)))
    (hfirst : ∀ i j (hij : coordVertex k l i = coordVertex k l j),
      firstImage (source := source) (target := target) k l i j hij ∈ Z)
    (hmixed : ∀ (e : E) (b : Fin (l (source e))) (a : Fin (k (target e))),
      mixedImage (source := source) (target := target) k l e b a ∈ Z) : Z = ⊤ := by
  apply top_unique
  intro M _
  rw [← entry_reconstruction k l M]
  exact Z.sum_mem fun i _ => Z.sum_mem fun j _ => all_entries_mem k l hk hl Z hZ hfirst hmixed _ i j


omit [DecidableEq E] in
/-- Literal evaluation of a first-factor coordinate matrix. -/
theorem firstFactor_single (v : V) (i j : FirstBlockIndex k l v) (z : ℂ) :
    firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l
      (Pi.single v (CStarMatrix.ofMatrix (Matrix.single i j z))) =
      z • firstBlockUnit (graphFamily.{u} (source := source) (target := target)) k l v i j := by
  change (∑ w, firstBlockHom _ k l w
    ((Pi.single v (CStarMatrix.ofMatrix (Matrix.single i j z)) : FirstFactor k l) w)) = _
  rw [Finset.sum_eq_single v]
  · simp only [Pi.single_eq_same]
    exact matrixEval_single _ i j z
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, map_zero]
  · simp

/-- Literal evaluation of a second-factor coordinate matrix. -/
theorem secondFactor_single (hns : NoSinks source) (v : V)
    (i j : BlockIndex (source := source) (target := target) k l v) (z : ℂ) :
    factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns
      (Pi.single v (CStarMatrix.ofMatrix (Matrix.single i j z))) =
      z • blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v i j := by
  change (∑ w, blockHom _ k l hk w
    ((Pi.single v (CStarMatrix.ofMatrix (Matrix.single i j z)) : Factor (source := source) (target := target) k l) w)) = _
  rw [Finset.sum_eq_single v]
  · simp only [Pi.single_eq_same]
    exact matrixEval_single _ i j z
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, map_zero]
  · simp

include hl in
/-- Two continuous star homomorphisms agreeing on the finite factors agree on
the actual completed graph corner. -/
theorem hom_ext_factors (hns : NoSinks source)
    (φ ψ : graphCorner.{u} (source := source) (target := target) k l →⋆ₐ[ℂ] C)
    (hfirst : φ.comp (firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l) =
      ψ.comp (firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l))
    (hsecond : φ.comp (factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns) =
      ψ.comp (factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns)) : φ = ψ := by
  have htop : StarAlgHom.equalizer φ ψ = ⊤ := by
    apply corner_eq_top_of_generators k l hk hl
    · exact isClosed_eq (map_continuous φ) (map_continuous ψ)
    · intro i j hij
      have he := DFunLike.congr_fun hfirst
        (Pi.single (coordVertex k l i)
          (CStarMatrix.ofMatrix (Matrix.single
            (⟨i, rfl⟩ : FirstBlockIndex k l (coordVertex k l i))
            (⟨j, hij.symm⟩ : FirstBlockIndex k l (coordVertex k l i)) (1 : ℂ))))
      simp only [StarAlgHom.comp_apply, firstFactor_single, one_smul] at he
      exact he
    · intro e b a
      have he := DFunLike.congr_fun hsecond
        (Pi.single (target e)
          (CStarMatrix.ofMatrix (Matrix.single
            (⟨qIndex k l e b, rfl⟩ : BlockIndex (source := source) (target := target) k l (target e))
            (⟨pIndex k l (target e) a, rfl⟩ : BlockIndex (source := source) (target := target) k l (target e)) (1 : ℂ))))
      simp only [StarAlgHom.comp_apply, secondFactor_single, one_smul] at he
      have hx : blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk (target e)
          ⟨qIndex k l e b, rfl⟩ ⟨pIndex k l (target e) a, rfl⟩ =
          mixedImage (source := source) (target := target) k l e b a := by
        apply Subtype.ext
        exact mixed_QP _ k l hk e b a
      rw [hx] at he
      exact he
  ext x
  exact (show x ∈ StarAlgHom.equalizer φ ψ by rw [htop]; trivial)

include H in
/-- The weighted graph corner has exactly the extension property dictated by
the concrete common matrix-unit equations. The whole-factor restrictions and
uniqueness are conclusions of the construction. -/
theorem existsUnique_factor_extension (hns : NoSinks source) :
    ∃! φ : graphCorner.{u} (source := source) (target := target) k l →⋆ₐ[ℂ] C,
      φ.comp (firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l) = S.representation ∧
      φ.comp (factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns) = T.representation := by
  have hfirst : (backward k l hk hl S T H.toCommon).comp
      (firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l) = S.representation := by
    ext a
    exact backward_firstFactor k l hk hl S T H a
  have hsecond : (backward k l hk hl S T H.toCommon).comp
      (factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns) = T.representation := by
    ext a
    exact backward_secondFactor k l hk hl S T H hns a
  refine ⟨backward k l hk hl S T H.toCommon, ⟨hfirst, hsecond⟩, ?_⟩
  intro φ hφ
  exact hom_ext_factors k l hk hl hns φ _ (hφ.1.trans hfirst.symm) (hφ.2.trans hsecond.symm)


omit [DecidableEq E] in
include hk in
/-- The weighted graph projection is algebraically full: every vertex occurs
because each k(v) is positive. No simplicity theorem is needed for this step. -/
theorem weightedProjection_ideal_eq_top
    (I : TwoSidedIdeal (CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{u} source target)))
    (hI : projection (graphFamily.{u} (source := source) (target := target)) k l ∈ I) : I = ⊤ := by
  have hv (i : Coord k l) (v : V) : single k l i i (GraphUniversal.vertex.{u} source target v) ∈ I := by
    have hm := I.mul_mem_right _ (single k l (base k l hk v) i 1)
      (I.mul_mem_left (single k l i (base k l hk v) 1) _ hI)
    have he : single k l i (base k l hk v) (1 : GraphUniversal.Algebra.{u} source target) *
        projection (graphFamily.{u} (source := source) (target := target)) k l *
        single k l (base k l hk v) i 1 = single k l i i (GraphUniversal.vertex.{u} source target v) := by
      rw [single_mul_projection, single_mul_same, one_mul, mul_one]
      rfl
    exact he ▸ hm
  have hdiag (i : Coord k l) : single k l i i (1 : GraphUniversal.Algebra.{u} source target) ∈ I := by
    rw [← GraphUniversal.vertex_sum.{u} source target, single_sum]
    exact sum_mem fun v _ => hv i v
  apply I.eq_top
  have hone : (∑ i : Coord k l, single k l i i (1 : GraphUniversal.Algebra.{u} source target)) = 1 := by
    change CStarMatrix.ofMatrix (∑ i : Coord k l, Matrix.single i i (1 : GraphUniversal.Algebra.{u} source target)) = 1
    rw [Matrix.sum_single_one]
    rfl
  rw [← hone]
  exact sum_mem fun i _ => hdiag i

omit [DecidableEq E] in
include hk in
/-- Hence the actual weighted projection satisfies the dense-ideal definition
used by the existing full-corner Morita/frame construction. -/
theorem weightedProjection_full :
    CommonCorner.FullProjection (projection (graphFamily.{u} (source := source) (target := target)) k l) := by
  have ht := weightedProjection_ideal_eq_top k l hk
    (TwoSidedIdeal.span ({projection (graphFamily.{u} (source := source) (target := target)) k l} : Set _))
    (TwoSidedIdeal.subset_span (Set.mem_singleton _))
  unfold CommonCorner.FullProjection
  rw [ht]
  exact dense_univ

section AmalgamIdentification
variable {D P₀ : Type} [CStarAlgebra D] [CStarAlgebra P₀]
  (S₀ : MatrixUnits (coordVertex k l) P₀)
  (T₀ : MatrixUnits (indexVertex (source := source) (target := target) k l) P₀)
  (H₀ : AllCommon k l hk hl S₀ T₀)
  (i₀ : D →⋆ₐ[ℂ] FirstFactor k l)
  (i₁ : D →⋆ₐ[ℂ] Factor (source := source) (target := target) k l)
  (hP : CStarAmalgam.IsFullAmalgam i₀ i₁ S₀.representation T₀.representation)
  (hns : NoSinks source)
  (hc : (firstFactorHom (graphFamily.{0} (source := source) (target := target)) k l).comp i₀ =
    (factorHom (graphFamily.{0} (source := source) (target := target)) k l hk hns).comp i₁)

/-- The actual forward universal map; the finite common-map equation is an
explicit remaining coordinate obligation when this theorem is instantiated. -/
def forward : P₀ →⋆ₐ[ℂ] graphCorner.{0} (source := source) (target := target) k l :=
  hP.lift (firstFactorHom (graphFamily.{0} (source := source) (target := target)) k l)
    (factorHom (graphFamily.{0} (source := source) (target := target)) k l hk hns) hc

include H₀ in
/-- The composite fixes the entire graph corner by its proved generation. -/
theorem forward_backward :
    (forward k l hk S₀ T₀ i₀ i₁ hP hns hc).comp (backward k l hk hl S₀ T₀ H₀.toCommon) =
      StarAlgHom.id ℂ (graphCorner.{0} (source := source) (target := target) k l) := by
  apply hom_ext_factors k l hk hl hns
  · apply StarAlgHom.ext
    intro a
    change forward k l hk S₀ T₀ i₀ i₁ hP hns hc
      (backward k l hk hl S₀ T₀ H₀.toCommon
        (firstFactorHom (graphFamily.{0} (source := source) (target := target)) k l a)) = _
    rw [backward_firstFactor k l hk hl S₀ T₀ H₀]
    exact DFunLike.congr_fun (hP.lift_left _ _ hc) a
  · apply StarAlgHom.ext
    intro a
    change forward k l hk S₀ T₀ i₀ i₁ hP hns hc
      (backward k l hk hl S₀ T₀ H₀.toCommon
        (factorHom (graphFamily.{0} (source := source) (target := target)) k l hk hns a)) = _
    rw [backward_secondFactor k l hk hl S₀ T₀ H₀]
    exact DFunLike.congr_fun (hP.lift_right _ _ hc) a

include H₀ in
/-- The opposite composite fixes both actual amalgam factors, hence is the identity. -/
theorem backward_forward :
    (backward k l hk hl S₀ T₀ H₀.toCommon).comp (forward k l hk S₀ T₀ i₀ i₁ hP hns hc) =
      StarAlgHom.id ℂ P₀ := by
  apply hP.hom_ext
  · apply StarAlgHom.ext
    intro a
    change backward k l hk hl S₀ T₀ H₀.toCommon
      (forward k l hk S₀ T₀ i₀ i₁ hP hns hc (S₀.representation a)) = S₀.representation a
    rw [show forward k l hk S₀ T₀ i₀ i₁ hP hns hc (S₀.representation a) =
      firstFactorHom (graphFamily.{0} (source := source) (target := target)) k l a from
        DFunLike.congr_fun (hP.lift_left _ _ hc) a]
    exact backward_firstFactor k l hk hl S₀ T₀ H₀ a
  · apply StarAlgHom.ext
    intro a
    change backward k l hk hl S₀ T₀ H₀.toCommon
      (forward k l hk S₀ T₀ i₀ i₁ hP hns hc (T₀.representation a)) = T₀.representation a
    rw [show forward k l hk S₀ T₀ i₀ i₁ hP hns hc (T₀.representation a) =
      factorHom (graphFamily.{0} (source := source) (target := target)) k l hk hns a from
        DFunLike.congr_fun (hP.lift_right _ _ hc) a]
    exact backward_secondFactor k l hk hl S₀ T₀ H₀ hns a

/-- Concrete graph-corner identification from actual full-amalgam data and the
finite common equations. Neither inverse equation is a premise. The intended
canonical inclusions still have to be proved to supply H₀ and hc. -/
def amalgamEquivCorner : P₀ ≃⋆ₐ[ℂ] graphCorner.{0} (source := source) (target := target) k l :=
  StarAlgEquiv.ofBijective (forward k l hk S₀ T₀ i₀ i₁ hP hns hc) (by
    have hi : Function.LeftInverse (backward k l hk hl S₀ T₀ H₀.toCommon)
        (forward k l hk S₀ T₀ i₀ i₁ hP hns hc) := by
      intro x
      exact DFunLike.congr_fun (backward_forward k l hk hl S₀ T₀ H₀ i₀ i₁ hP hns hc) x
    have hs : Function.RightInverse (backward k l hk hl S₀ T₀ H₀.toCommon)
        (forward k l hk S₀ T₀ i₀ i₁ hP hns hc) := by
      intro x
      exact DFunLike.congr_fun (forward_backward k l hk hl S₀ T₀ H₀ i₀ i₁ hP hns hc) x
    exact ⟨hi.injective, hs.surjective⟩)

end AmalgamIdentification
end Suzuki.GraphCornerIdentification

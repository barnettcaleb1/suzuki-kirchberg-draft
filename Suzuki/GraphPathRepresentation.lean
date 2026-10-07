import Suzuki.GraphUniversal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The infinite-path representation of a finite graph

Operators act on the genuine complex Hilbert space `ℓ²` of infinite paths, with
its existing operator C*-norm. Edges prepend paths; vertices filter their start.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped ComplexConjugate InnerProductSpace
local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace Suzuki.GraphPathRepresentation

universe u v

abbrev Hilbert (X : Type u) := lp (fun _ : X => ℂ) 2

variable {X : Type u} {I : Type v}

/-- The canonical isometric inclusion of one coordinate in `ℓ²`. -/
def coordinate (x : X) : ℂ →ₗᵢ[ℂ] Hilbert X := by
  classical
  exact { toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : X => ℂ) 2 x
          norm_map' := fun a => lp.norm_single (E := fun _ : X => ℂ) (p := 2) (by norm_num) x a }

@[simp] theorem coordinate_apply (x : X) (a : ℂ) :
    coordinate x a = lp.single 2 x a := rfl

/-- Distinct coordinates are orthogonal in the actual Hilbert inner product. -/
theorem coordinate_orthogonal (f : I ↪ X) :
    OrthogonalFamily ℂ (fun _ : I => ℂ) (fun i => coordinate (f i)) := by
  classical
  intro i j hij a b
  simp only [coordinate_apply, lp.inner_single_left]
  rw [lp.single_apply_ne (E := fun _ : X => ℂ) 2 (f j) b (fun h => hij (f.injective h))]
  simp

/-- Extension by zero along any injection, built by the Hilbert sum theorem. -/
def inclusion (f : I ↪ X) : Hilbert I →ₗᵢ[ℂ] Hilbert X :=
  (coordinate_orthogonal f).linearIsometry

@[simp] theorem inclusion_single (f : I ↪ X) (i : I) (a : ℂ) :
    inclusion f (lp.single 2 i a) = lp.single 2 (f i) a := by
  classical
  exact (coordinate_orthogonal f).linearIsometry_apply_single (i := i) a

/-- The Hilbert adjoint of extension by zero is coordinate restriction. -/
theorem inclusion_adjoint_apply (f : I ↪ X) (ξ : Hilbert X) (i : I) :
    (inclusion f).toContinuousLinearMap.adjoint ξ i = ξ (f i) := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right
    (inclusion f).toContinuousLinearMap (lp.single 2 i (1 : ℂ)) ξ
  simpa only [LinearIsometry.coe_toContinuousLinearMap, inclusion_single,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using h

/-- A bounded operator on `ℓ²` is determined by its coordinate vectors. -/
theorem operator_ext {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T S : Hilbert X →L[ℂ] F}
    (h : ∀ x a, T (lp.single 2 x a) = S (lp.single 2 x a)) : T = S := by
  classical
  apply lp.ext_continuousLinearMap (by simp)
  intro x
  apply ContinuousLinearMap.ext
  intro a
  exact h x a

/-- Projection onto the coordinates in the range of an injection. -/
def rangeProjection (f : I ↪ X) : Hilbert X →L[ℂ] Hilbert X :=
  (inclusion f).toContinuousLinearMap ∘L (inclusion f).toContinuousLinearMap.adjoint

@[simp] theorem inclusion_adjoint_single (f : I ↪ X) (i : I) (a : ℂ) :
    (inclusion f).toContinuousLinearMap.adjoint (lp.single 2 (f i) a) =
      lp.single 2 i a := by
  have h := congrArg (fun T : Hilbert I →L[ℂ] Hilbert I => T (lp.single 2 i a))
    (inclusion f).adjoint_comp_self
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    inclusion_single, one_apply_eq_self] using h

@[simp] theorem inclusion_adjoint_single_of_notMem (f : I ↪ X) (x : X)
    (hx : x ∉ Set.range f) (a : ℂ) :
    (inclusion f).toContinuousLinearMap.adjoint (lp.single 2 x a) = 0 := by
  classical
  ext i
  rw [inclusion_adjoint_apply]
  exact lp.single_apply_ne (E := fun _ : X => ℂ) 2 x a (fun h => hx ⟨i, h⟩)

@[simp] theorem rangeProjection_single_mem (f : I ↪ X) (i : I) (a : ℂ) :
    rangeProjection f (lp.single 2 (f i) a) = lp.single 2 (f i) a := by
  simp [rangeProjection]

@[simp] theorem rangeProjection_single_notMem (f : I ↪ X) (x : X)
    (hx : x ∉ Set.range f) (a : ℂ) :
    rangeProjection f (lp.single 2 x a) = 0 := by
  simp [rangeProjection, inclusion_adjoint_single_of_notMem f x hx a]

/-- Range operators above are actual self-adjoint idempotents. -/
theorem rangeProjection_isStarProjection (f : I ↪ X) :
    IsStarProjection (rangeProjection f) := by
  constructor
  · apply operator_ext
    intro x a
    by_cases hx : x ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hx
      simp
    · simp [rangeProjection_single_notMem f x hx]
  · change star (rangeProjection f) = rangeProjection f
    simp [rangeProjection, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp]

/-- The range projection acts as a coordinate indicator. -/
theorem rangeProjection_single (f : I ↪ X) (x : X) (a : ℂ) :
    rangeProjection f (lp.single 2 x a) =
      if x ∈ Set.range f then lp.single 2 x a else 0 := by
  split_ifs with hx
  · obtain ⟨i, rfl⟩ := hx
    exact rangeProjection_single_mem f i a
  · exact rangeProjection_single_notMem f x hx a

/-- A partial coordinate bijection, realized as a bounded operator. -/
def transport (f g : I ↪ X) : Hilbert X →L[ℂ] Hilbert X :=
  (inclusion g).toContinuousLinearMap ∘L (inclusion f).toContinuousLinearMap.adjoint

/-- The initial projection is proved from the isometry of extension by zero. -/
theorem transport_initial (f g : I ↪ X) :
    star (transport f g) * transport f g = rangeProjection f := by
  simp only [transport, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.mul_def, rangeProjection]
  rw [← ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc (inclusion f).toContinuousLinearMap,
    (inclusion g).adjoint_comp_self]
  rfl

/-- The final projection is exactly the range-coordinate projection. -/
theorem transport_final (f g : I ↪ X) :
    transport f g * star (transport f g) = rangeProjection g := by
  simp only [transport, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.mul_def, rangeProjection]
  rw [← ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc (inclusion g).toContinuousLinearMap,
    (inclusion f).adjoint_comp_self]
  rfl

variable {V : Type u} {E : Type v} (source target : E → V)

/-- An infinite composable edge path, with the manuscript's edge orientation. -/
def Path := {p : ℕ → E // ∀ n, target (p n) = source (p (n + 1))}

namespace Path

variable {source target}

def head (p : Path source target) : E := p.val 0

def start (p : Path source target) : V := source p.head

def tail (p : Path source target) : Path source target :=
  ⟨fun n => p.val (n + 1), fun n => p.property (n + 1)⟩

@[simp] theorem start_tail (p : Path source target) : p.tail.start = target p.head :=
  (p.property 0).symm

/-- Prefixing is defined only when the target matches the path's start. -/
def prepend (e : E) (p : Path source target) (h : p.start = target e) :
    Path source target :=
  ⟨fun n => match n with | 0 => e | n + 1 => p.val n, by
    intro n
    cases n with
    | zero => exact h.symm
    | succ n => exact p.property n⟩

@[simp] theorem head_prefix (e : E) (p : Path source target) (h) :
    (prepend e p h).head = e := rfl

@[simp] theorem start_prefix (e : E) (p : Path source target) (h) :
    (prepend e p h).start = source e := rfl

@[simp] theorem tail_prefix (e : E) (p : Path source target) (h) :
    (prepend e p h).tail = p := rfl

@[simp] theorem prefix_head_tail (p : Path source target) :
    prepend p.head p.tail p.start_tail = p := by
  apply Subtype.ext
  funext n
  cases n <;> rfl

/-- No sinks gives an actual infinite path starting at each prescribed vertex. -/
theorem exists_start (h : GraphRelations.NoSinks source) (v : V) :
    ∃ p : Path source target, p.start = v := by
  classical
  let edge : V → E := fun v => (h v).choose
  have edge_source (v) : source (edge v) = v := (h v).choose_spec
  let verts : ℕ → V := fun n => (fun v => target (edge v))^[n] v
  have hs (n) : verts (n + 1) = target (edge (verts n)) := by
    exact Function.iterate_succ_apply' _ n v
  refine ⟨⟨fun n => edge (verts n), ?_⟩, ?_⟩
  · intro n
    change target (edge (verts n)) = source (edge (verts (n + 1)))
    rw [edge_source, hs]
  · exact edge_source v

end Path

/-- Inclusion of all paths starting at a vertex. -/
def startInclusion (v : V) : {p : Path source target // p.start = v} ↪ Path source target :=
  Function.Embedding.subtype _

/-- Left-prepend injection, with a domain consisting of the target-starting paths. -/
def prefixInclusion (e : E) :
    {p : Path source target // p.start = target e} ↪ Path source target where
  toFun p := p.val.prepend e p.property
  inj' p q h := by
    apply Subtype.ext
    simpa using congrArg Path.tail h

@[simp] theorem mem_range_startInclusion (v : V) (p : Path source target) :
    p ∈ Set.range (startInclusion source target v) ↔ p.start = v := by
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro h
    exact ⟨⟨p, h⟩, rfl⟩

@[simp] theorem mem_range_prefixInclusion (e : E) (p : Path source target) :
    p ∈ Set.range (prefixInclusion source target e) ↔ p.head = e := by
  constructor
  · rintro ⟨q, rfl⟩
    rfl
  · intro h
    subst e
    exact ⟨⟨p.tail, p.start_tail⟩, p.prefix_head_tail⟩

/-- Vertex projections in the bounded operators on the path Hilbert space. -/
def vertex (v : V) : Hilbert (Path source target) →L[ℂ] Hilbert (Path source target) :=
  rangeProjection (startInclusion source target v)

/-- The edge partial isometry prefixes precisely the paths starting at its target. -/
def edge (e : E) : Hilbert (Path source target) →L[ℂ] Hilbert (Path source target) :=
  transport (startInclusion source target (target e)) (prefixInclusion source target e)

@[simp] theorem vertex_single (v : V) (p : Path source target) (a : ℂ) :
    vertex source target v (lp.single 2 p a) =
      if p.start = v then lp.single 2 p a else 0 := by
  simp only [vertex, rangeProjection_single, mem_range_startInclusion]

/-- On an admissible coordinate, the edge operator literally prepends the edge. -/
theorem edge_single_of_start (e : E) (p : Path source target)
    (hp : p.start = target e) (a : ℂ) :
    edge source target e (lp.single 2 p a) = lp.single 2 (p.prepend e hp) a := by
  change inclusion (prefixInclusion source target e)
    ((inclusion (startInclusion source target (target e))).toContinuousLinearMap.adjoint
      (lp.single 2 ((startInclusion source target (target e)) ⟨p, hp⟩) a)) = _
  rw [inclusion_adjoint_single, inclusion_single]
  rfl

/-- Inadmissible coordinates are killed by the edge operator. -/
theorem edge_single_of_not_start (e : E) (p : Path source target)
    (hp : p.start ≠ target e) (a : ℂ) :
    edge source target e (lp.single 2 p a) = 0 := by
  have hn : p ∉ Set.range (startInclusion source target (target e)) :=
    fun hm => hp ((mem_range_startInclusion source target (target e) p).mp hm)
  simp only [edge, transport, ContinuousLinearMap.comp_apply,
    inclusion_adjoint_single_of_notMem _ _ hn, map_zero]

/-- The adjoint removes the first edge on exactly its corresponding path coordinates. -/
theorem edge_adjoint_single_of_head (e : E) (p : Path source target)
    (hp : p.head = e) (a : ℂ) :
    star (edge source target e) (lp.single 2 p a) = lp.single 2 p.tail a := by
  have ht : p.tail.start = target e := p.start_tail.trans (congrArg target hp)
  have he : prefixInclusion source target e ⟨p.tail, ht⟩ = p := by
    subst e
    exact p.prefix_head_tail
  have ha := inclusion_adjoint_single (prefixInclusion source target e) ⟨p.tail, ht⟩ a
  rw [he] at ha
  simp only [edge, transport, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply, ha, LinearIsometry.coe_toContinuousLinearMap,
    inclusion_single]
  rfl

/-- Every other first-edge coordinate is killed by the adjoint. -/
theorem edge_adjoint_single_of_not_head (e : E) (p : Path source target)
    (hp : p.head ≠ e) (a : ℂ) :
    star (edge source target e) (lp.single 2 p a) = 0 := by
  have hn : p ∉ Set.range (prefixInclusion source target e) :=
    fun hm => hp ((mem_range_prefixInclusion source target e p).mp hm)
  simp only [edge, transport, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply, inclusion_adjoint_single_of_notMem _ _ hn, map_zero]

@[simp] theorem edge_initial (e : E) :
    star (edge source target e) * edge source target e = vertex source target (target e) :=
  transport_initial _ _

@[simp] theorem edge_final (e : E) :
    edge source target e * star (edge source target e) =
      rangeProjection (prefixInclusion source target e) :=
  transport_final _ _

@[simp] theorem edge_range_single (e : E) (p : Path source target) (a : ℂ) :
    (edge source target e * star (edge source target e)) (lp.single 2 p a) =
      if p.head = e then lp.single 2 p a else 0 := by
  simp only [edge_final, rangeProjection_single, mem_range_prefixInclusion]

/-- All vertex operators are self-adjoint projections. -/
theorem vertex_projection (v : V) : IsStarProjection (vertex source target v) :=
  rangeProjection_isStarProjection _

/-- Distinct vertex coordinates give orthogonal projections. -/
theorem vertex_orthogonal (v w : V) (h : v ≠ w) :
    vertex source target v * vertex source target w = 0 := by
  apply operator_ext
  intro p a
  change vertex source target v (vertex source target w (lp.single 2 p a)) = 0
  rw [vertex_single]
  by_cases hw : p.start = w
  · rw [if_pos hw, vertex_single, if_neg (fun hv => h (hv.symm.trans hw))]
  · simp [hw]

/-- Distinct first edges give orthogonal final projections. -/
theorem edge_ranges_orthogonal (e f : E) (h : e ≠ f) :
    (edge source target e * star (edge source target e)) *
      (edge source target f * star (edge source target f)) = 0 := by
  apply operator_ext
  intro p a
  change (edge source target e * star (edge source target e))
    ((edge source target f * star (edge source target f)) (lp.single 2 p a)) = 0
  rw [edge_range_single]
  by_cases hf : p.head = f
  · rw [if_pos hf, edge_range_single, if_neg (fun he => h (he.symm.trans hf))]
  · simp [hf]

/-- Orthogonality of the edge initial products follows without any extra hypothesis. -/
theorem edge_orthogonal (e f : E) (h : e ≠ f) :
    star (edge source target e) * edge source target f = 0 :=
  (GraphRelations.orthogonal_iff_ranges
    (vertex_projection source target (target e)) (vertex_projection source target (target f))
    (edge_initial source target e) (edge_initial source target f)).mpr
      (edge_ranges_orthogonal source target e f h)

variable [Fintype V] [Fintype E]

omit [Fintype E] in
/-- The vertex projections partition the identity operator. -/
theorem vertex_sum : ∑ v, vertex source target v = 1 := by
  apply operator_ext
  intro p a
  simp only [sum_apply, vertex_single, one_apply_eq_self]
  simp

omit [Fintype V] in
/-- Each path has exactly one first edge, giving the Cuntz--Krieger outgoing sum. -/
theorem outgoing (v : V) :
    ∑ e ∈ Finset.univ.filter (fun e => source e = v),
      edge source target e * star (edge source target e) = vertex source target v := by
  apply operator_ext
  intro p a
  simp only [sum_apply, edge_range_single, vertex_single]
  simp [Path.start]

/-- A concrete Cuntz--Krieger family in the genuine operator C*-algebra on path `ℓ²`. -/
def family : GraphRelations.Family source target
    (Hilbert (Path source target) →L[ℂ] Hilbert (Path source target)) where
  vertex := vertex source target
  edge := edge source target
  vertex_projection := vertex_projection source target
  vertex_orthogonal := vertex_orthogonal source target
  vertex_sum := vertex_sum source target
  initial := edge_initial source target
  edge_orthogonal := edge_orthogonal source target
  outgoing v _ := outgoing source target v

omit [Fintype V] [Fintype E] in
/-- The coordinate vector of any path starting at `v` witnesses a nonzero vertex. -/
theorem vertex_ne_zero (h : GraphRelations.NoSinks source) (v : V) :
    vertex source target v ≠ 0 := by
  obtain ⟨p, hp⟩ := Path.exists_start (target := target) h v
  intro hz
  have ht := congrArg (fun T : Hilbert (Path source target) →L[ℂ] Hilbert (Path source target) =>
    T (lp.single 2 p (1 : ℂ))) hz
  have : (lp.single 2 p (1 : ℂ) : Hilbert (Path source target)) = 0 := by
    simpa [hp] using ht
  have hc := congrArg (fun ξ : Hilbert (Path source target) => ξ p) this
  simp at hc

/-- Every finite graph without sinks has a Cuntz--Krieger family whose vertices are all nonzero. -/
theorem exists_family_nonzero (h : GraphRelations.NoSinks source) :
    ∃ F : GraphRelations.Family source target
      (Hilbert (Path source target) →L[ℂ] Hilbert (Path source target)),
      ∀ v, F.vertex v ≠ 0 :=
  ⟨family source target, vertex_ne_zero source target h⟩

/-- A nonzero projection in an actual C*-algebra has norm one. -/
theorem projection_norm_one {A : Type*} [CStarAlgebra A] {p : A}
    (hp : IsStarProjection p) (hn : p ≠ 0) : ‖p‖ = 1 := by
  have hc := CStarRing.norm_star_mul_self (x := p)
  rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] at hc
  have hpos := norm_pos_iff.mpr hn
  nlinarith

omit [Fintype V] [Fintype E] in
/-- Every path vertex has operator norm one when the graph has no sinks. -/
theorem vertex_norm_one (h : GraphRelations.NoSinks source) (v : V) :
    ‖vertex source target v‖ = 1 :=
  projection_norm_one (vertex_projection source target v) (vertex_ne_zero source target h v)

omit [Fintype V] [Fintype E] in
/-- Every edge partial isometry has its genuine operator norm equal to one. -/
theorem edge_norm_one (h : GraphRelations.NoSinks source) (e : E) :
    ‖edge source target e‖ = 1 := by
  have hc := CStarRing.norm_star_mul_self (x := edge source target e)
  rw [edge_initial, vertex_norm_one source target h] at hc
  nlinarith [norm_nonneg (edge source target e)]

/-- The path representation belongs to the carrier universe of the edge type.
Thus its lift proves vertex nonzeroness in that precise universal graph algebra. -/
theorem universal_vertex_ne_zero (h : GraphRelations.NoSinks source) (vtx : V) :
    GraphUniversal.vertex.{v} source target vtx ≠ 0 :=
  GraphUniversal.vertex_ne_zero_of_representation source target (family source target) vtx
    (vertex_ne_zero source target h vtx)

/-- The corresponding universal vertices have their actual C*-norm equal to one. -/
theorem universal_vertex_norm_one (h : GraphRelations.NoSinks source) (vtx : V) :
    ‖GraphUniversal.vertex.{v} source target vtx‖ = 1 :=
  projection_norm_one (GraphUniversal.vertex_projection source target vtx)
    (universal_vertex_ne_zero source target h vtx)

/-- The universal edges are nonzero, as their initial projections are nonzero. -/
theorem universal_edge_ne_zero (h : GraphRelations.NoSinks source) (e : E) :
    GraphUniversal.edge.{v} source target e ≠ 0 := by
  intro hz
  apply universal_vertex_ne_zero source target h (target e)
  rw [← GraphUniversal.initial source target e, hz, star_zero, zero_mul]

end Suzuki.GraphPathRepresentation

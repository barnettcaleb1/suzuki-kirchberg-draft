import Suzuki.CommonCorner
import Suzuki.MultiplicityEmbeddings
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Data.Matrix.Basis

/-!
# Concrete finite graph Cuntz--Krieger families

An edge has source `source e = w` and target `target e = v`; its initial
projection is `p v`, and the sum of its outgoing range projections is `p w`.
All families live in genuine complex C*-algebras with their existing norms.
This file does not assert existence of a universal graph algebra, simplicity,
nuclearity, or the manuscript's graph/amalgam isomorphism.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace Suzuki.GraphRelations

universe u v w

variable {A : Type u} [CStarAlgebra A]

/-- Initial projection implies the actual partial-isometry support equation. -/
theorem support_of_initial {s p : A} (hp : IsStarProjection p)
    (hs : star s * s = p) : s * p = s := by
  have hz : star (s - s * p) * (s - s * p) = 0 := by
    rw [star_sub, star_mul, hp.isSelfAdjoint.star_eq]
    calc
      (star s - p * star s) * (s - s * p) =
          star s * s - (star s * s) * p - p * (star s * s) + p * (star s * s) * p := by
        noncomm_ring
      _ = 0 := by rw [hs, hp.isIdempotentElem.eq]; noncomm_ring [hp.isIdempotentElem.eq]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)).symm

/-- The final projection is proved, rather than added as an independent axiom. -/
theorem range_isProjection {s p : A} (hp : IsStarProjection p)
    (hs : star s * s = p) : IsStarProjection (s * star s) := by
  refine ⟨?_, ?_⟩
  · change (s * star s) * (s * star s) = s * star s
    calc
      _ = (s * (star s * s)) * star s := by noncomm_ring
      _ = s * star s := by rw [hs, support_of_initial hp hs]
  · exact IsSelfAdjoint.mul_star_self s

/-- Every edge satisfying an initial projection relation is a contraction. -/
theorem norm_le_one_of_initial {s p : A} (hp : IsStarProjection p)
    (hs : star s * s = p) : ‖s‖ ≤ 1 := by
  have h := hp.norm_le
  have hn := CStarRing.norm_star_mul_self (x := s)
  rw [hs] at hn
  nlinarith [norm_nonneg s]

/-- For partial isometries, the two usual orthogonality conventions agree. -/
theorem orthogonal_iff_ranges {s t p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hs : star s * s = p) (ht : star t * t = q) :
    star s * t = 0 ↔ (s * star s) * (t * star t) = 0 := by
  constructor
  · intro h
    calc
      _ = s * (star s * t) * star t := by noncomm_ring
      _ = 0 := by rw [h]; simp
  · intro h
    have hsp : p * star s = star s := by
      simpa only [star_mul, hp.isSelfAdjoint.star_eq] using
        congrArg star (support_of_initial hp hs)
    calc
      star s * t = (p * star s) * (t * q) := by rw [hsp, support_of_initial hq ht]
      _ = star s * ((s * star s) * (t * star t)) * t := by rw [← hs, ← ht]; noncomm_ring
      _ = 0 := by rw [h]; simp

variable {V : Type v} {E : Type w} [Fintype V] [Fintype E]
  [DecidableEq V]

/-- A finite graph has no sinks when every vertex emits at least one edge. -/
def NoSinks (source : E → V) : Prop := ∀ v, ∃ e, source e = v

/-- The manuscript's matrix convention: M(v,w) edges from w to v. -/
abbrev MatrixEdge (M : Matrix V V ℕ) := Σ w : V, Σ v : V, Fin (M v w)

def matrixSource (M : Matrix V V ℕ) (e : MatrixEdge M) : V := e.1

def matrixTarget (M : Matrix V V ℕ) (e : MatrixEdge M) : V := e.2.1

omit [Fintype V] [DecidableEq V] in
/-- No zero column is precisely no sinks for this orientation. -/
theorem matrix_noSinks_iff (M : Matrix V V ℕ) :
    NoSinks (matrixSource M) ↔ ∀ w, ∃ v, 0 < M v w := by
  constructor
  · intro h w
    obtain ⟨⟨w', v, t⟩, hw⟩ := h w
    change w' = w at hw
    subst w'
    exact ⟨v, Nat.zero_lt_of_lt t.isLt⟩
  · intro h w
    obtain ⟨v, hv⟩ := h w
    exact ⟨⟨w, v, ⟨0, hv⟩⟩, rfl⟩

omit [DecidableEq V] in
/-- Total edge count with exactly the target-row/source-column convention. -/
theorem card_matrixEdge (M : Matrix V V ℕ) :
    Fintype.card (MatrixEdge M) = ∑ w, ∑ v, M v w := by
  simp only [MatrixEdge, Fintype.card_sigma, Fintype.card_fin]

/-- Concrete unital Cuntz--Krieger relations. The off-diagonal initial products
express orthogonal edge ranges; their equivalence is proved below. CK is imposed
at emitting vertices only, so sink vertices are not forced to vanish. Vertex
nonzeroness is not assumed and is stated separately when needed. -/
structure Family (source target : E → V) (A : Type u) [CStarAlgebra A] where
  vertex : V → A
  edge : E → A
  vertex_projection : ∀ v, IsStarProjection (vertex v)
  vertex_orthogonal : ∀ v w, v ≠ w → vertex v * vertex w = 0
  vertex_sum : ∑ v, vertex v = 1
  initial : ∀ e, star (edge e) * edge e = vertex (target e)
  edge_orthogonal : ∀ e f, e ≠ f → star (edge e) * edge f = 0
  outgoing : ∀ v, (∃ e, source e = v) →
    ∑ e ∈ Finset.univ.filter (fun e => source e = v), edge e * star (edge e) = vertex v

/-- The zero family in any actual subsingleton C*-algebra. This provides
representations even before a nonzero graph model has been constructed. -/
def zeroFamily (source target : E → V) [Subsingleton A] : Family source target A where
  vertex _ := 0
  edge _ := 0
  vertex_projection _ := ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  vertex_orthogonal _ _ _ := Subsingleton.elim _ _
  vertex_sum := Subsingleton.elim _ _
  initial _ := Subsingleton.elim _ _
  edge_orthogonal _ _ _ := Subsingleton.elim _ _
  outgoing _ _ := Subsingleton.elim _ _

/-- An actual complete zero C*-algebra in every carrier universe. -/
abbrev ZeroAlgebra : Type u := ULift.{u} (Fin 0) → ℂ

/-- An explicit member of the class of concrete graph representations.
No assertion that any vertex survives in a universal model is made here. -/
def zeroModel (source target : E → V) : Family source target ZeroAlgebra.{u} :=
  zeroFamily source target

/-- Construct the family from the manuscript's orthogonal-range formulation.
The edge initial relation makes this equivalent to the off-diagonal relation. -/
def ofRangeRelations {source target : E → V} (p : V → A) (s : E → A)
    (hp : ∀ v, IsStarProjection (p v))
    (hpp : ∀ v w, v ≠ w → p v * p w = 0) (hunit : ∑ v, p v = 1)
    (hinit : ∀ e, star (s e) * s e = p (target e))
    (horth : ∀ e f, e ≠ f → (s e * star (s e)) * (s f * star (s f)) = 0)
    (hck : ∀ v, (∃ e, source e = v) →
      ∑ e ∈ Finset.univ.filter (fun e => source e = v), s e * star (s e) = p v) :
    Family source target A :=
  ⟨p, s, hp, hpp, hunit, hinit,
    fun e f hef => (orthogonal_iff_ranges (hp _) (hp _) (hinit e) (hinit f)).mpr (horth e f hef), hck⟩

namespace Family
variable {source target : E → V} (F : Family source target A)

@[simp] theorem edge_right_support (e : E) : F.edge e * F.vertex (target e) = F.edge e :=
  support_of_initial (F.vertex_projection _) (F.initial e)

theorem range_projection (e : E) : IsStarProjection (F.edge e * star (F.edge e)) :=
  range_isProjection (F.vertex_projection _) (F.initial e)

theorem edge_contractive (e : E) : ‖F.edge e‖ ≤ 1 :=
  norm_le_one_of_initial (F.vertex_projection _) (F.initial e)

theorem vertex_contractive (v : V) : ‖F.vertex v‖ ≤ 1 := (F.vertex_projection v).norm_le

/-- Distinct edges have orthogonal range projections in the ambient algebra. -/
theorem ranges_orthogonal (e f : E) (h : e ≠ f) :
    (F.edge e * star (F.edge e)) * (F.edge f * star (F.edge f)) = 0 := by
  calc
    _ = F.edge e * (star (F.edge e) * F.edge f) * star (F.edge f) := by noncomm_ring
    _ = 0 := by rw [F.edge_orthogonal e f h]; simp

/-- The outgoing relation gives left support at the source vertex. -/
@[simp] theorem edge_left_support (e : E) : F.vertex (source e) * F.edge e = F.edge e := by
  classical
  rw [← F.outgoing (source e) ⟨e, rfl⟩, Finset.sum_mul]
  rw [Finset.sum_eq_single e]
  · calc
      (F.edge e * star (F.edge e)) * F.edge e =
          F.edge e * (star (F.edge e) * F.edge e) := mul_assoc _ _ _
      _ = F.edge e := by rw [F.initial, F.edge_right_support]
  · intro f _ hfe
    rw [mul_assoc, F.edge_orthogonal f e hfe, mul_zero]
  · intro he
    exact False.elim (he (by simp))

/-- Wrong source vertices annihilate an edge. -/
theorem vertex_edge_zero (v : V) (e : E) (h : v ≠ source e) :
    F.vertex v * F.edge e = 0 := by
  rw [← F.edge_left_support e, ← mul_assoc, F.vertex_orthogonal v (source e) h, zero_mul]

/-- Wrong target vertices annihilate an edge on the right. -/
theorem edge_vertex_zero (e : E) (v : V) (h : target e ≠ v) :
    F.edge e * F.vertex v = 0 := by
  rw [← F.edge_right_support e, mul_assoc, F.vertex_orthogonal (target e) v h, mul_zero]

/-- Every edge is supported between its source and target vertex corners. -/
theorem edge_sandwich (e : E) :
    F.vertex (source e) * F.edge e * F.vertex (target e) = F.edge e := by
  rw [F.edge_left_support, F.edge_right_support]

theorem outgoing_of_noSinks (h : NoSinks source) (v : V) :
    ∑ e ∈ Finset.univ.filter (fun e => source e = v), F.edge e * star (F.edge e) = F.vertex v :=
  F.outgoing v (h v)

/-- Nonzero target projections force nonzero edges. -/
theorem edge_ne_zero (e : E) (h : F.vertex (target e) ≠ 0) : F.edge e ≠ 0 := by
  intro he
  apply h
  rw [← F.initial e, he, star_zero, zero_mul]

/-- Under nonzero target projections the edge norm is exactly one. -/
theorem edge_norm_eq_one (e : E) (h : F.vertex (target e) ≠ 0) : ‖F.edge e‖ = 1 := by
  have hnorm := CStarRing.norm_star_mul_self (x := F.vertex (target e))
  rw [(F.vertex_projection _).isSelfAdjoint.star_eq,
    (F.vertex_projection _).isIdempotentElem.eq] at hnorm
  have hp : ‖F.vertex (target e)‖ = 1 := by nlinarith [norm_pos_iff.mpr h]
  have hn := CStarRing.norm_star_mul_self (x := F.edge e)
  rw [F.initial e, hp] at hn
  nlinarith [norm_nonneg (F.edge e)]

/-- Letters in algebraic graph words: vertices, edges and formal edge adjoints. -/
abbrev Letter := V ⊕ (E ⊕ E)

/-- Self-adjoint generators for a real free-algebra presentation: vertices,
real parts of edges, and imaginary parts of edges. -/
def selfAdjointGenerator : Letter (V := V) (E := E) → selfAdjoint A
  | Sum.inl v => ⟨F.vertex v, (F.vertex_projection v).isSelfAdjoint⟩
  | Sum.inr (Sum.inl e) => realPart (F.edge e)
  | Sum.inr (Sum.inr e) => imaginaryPart (F.edge e)

theorem selfAdjointGenerator_contractive (i : Letter (V := V) (E := E)) :
    ‖F.selfAdjointGenerator i‖ ≤ 1 := by
  rcases i with v | (e | e)
  · exact F.vertex_contractive v
  · exact (realPart.norm_le (F.edge e)).trans (F.edge_contractive e)
  · exact (imaginaryPart.norm_le (F.edge e)).trans (F.edge_contractive e)

/-- The original edge is recovered exactly from those self-adjoint generators. -/
theorem edge_from_selfAdjointGenerators (e : E) :
    (F.selfAdjointGenerator (Sum.inr (Sum.inl e)) : A) +
      Complex.I • (F.selfAdjointGenerator (Sum.inr (Sum.inr e)) : A) = F.edge e :=
  realPart_add_I_smul_imaginaryPart _

def evalLetter : Letter (V := V) (E := E) → A
  | Sum.inl v => F.vertex v
  | Sum.inr (Sum.inl e) => F.edge e
  | Sum.inr (Sum.inr e) => star (F.edge e)

theorem evalLetter_contractive (a : Letter (V := V) (E := E)) : ‖F.evalLetter a‖ ≤ 1 := by
  rcases a with v | (e | e)
  · exact F.vertex_contractive v
  · exact F.edge_contractive e
  · simpa only [evalLetter, norm_star] using F.edge_contractive e

/-- Evaluation in the given concrete C*-algebra; the empty word is 1. -/
def evalWord (w : List (Letter (V := V) (E := E))) : A := (w.map F.evalLetter).prod

/-- Uniform contraction bound, independent of the concrete representing algebra. -/
theorem evalWord_contractive (w : List (Letter (V := V) (E := E))) : ‖F.evalWord w‖ ≤ 1 := by
  induction w with
  | nil =>
    exact IsStarProjection.norm_le (1 : A) ⟨by change (1 : A) * 1 = 1; exact one_mul 1, by change star (1 : A) = 1; simp only [star_one]⟩
  | cons a w ih =>
    change ‖F.evalLetter a * F.evalWord w‖ ≤ 1
    calc
      _ ≤ ‖F.evalLetter a‖ * ‖F.evalWord w‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (F.evalLetter_contractive a) ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _

/-- A finite complex linear combination of graph words is bounded by the
sum of coefficient norms, uniformly over all concrete CK families. -/
theorem polynomial_bound {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (words : ι → List (Letter (V := V) (E := E))) :
    ‖∑ i ∈ s, c i • F.evalWord (words i)‖ ≤ ∑ i ∈ s, ‖c i‖ := by
  calc
    _ ≤ ∑ i ∈ s, ‖c i • F.evalWord (words i)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (F.evalWord_contractive _) (norm_nonneg _)).trans_eq
        (mul_one _)

/-- Matrix units formed by edges with the same target vertex. -/
def incomingUnit (v : V) (e f : {e : E // target e = v}) : A :=
  F.edge e * star (F.edge f)

@[simp] theorem incomingUnit_star (v : V) (e f : {e : E // target e = v}) :
    star (F.incomingUnit v e f) = F.incomingUnit v f e := by
  simp only [incomingUnit, star_mul, star_star]

/-- These are genuine matrix-unit multiplication relations in the ambient algebra. -/
theorem incomingUnit_mul [DecidableEq E] (v : V) (e f g h : {e : E // target e = v}) :
    F.incomingUnit v e f * F.incomingUnit v g h =
      if f = g then F.incomingUnit v e h else 0 := by
  classical
  by_cases hfg : f = g
  · subst g
    rw [if_pos rfl]
    change (F.edge e * star (F.edge f)) * (F.edge f * star (F.edge h)) = _
    calc
      _ = F.edge e * (star (F.edge f) * F.edge f) * star (F.edge h) := by noncomm_ring
      _ = F.edge e * F.vertex (target e) * star (F.edge h) := by rw [F.initial, f.property, e.property]
      _ = _ := by rw [F.edge_right_support]; rfl
  · rw [if_neg hfg]
    have hfg' : (f : E) ≠ g := fun hh => hfg (Subtype.ext hh)
    change (F.edge e * star (F.edge f)) * (F.edge g * star (F.edge h)) = 0
    calc
      _ = F.edge e * (star (F.edge f) * F.edge g) * star (F.edge h) := by noncomm_ring
      _ = 0 := by rw [F.edge_orthogonal _ _ hfg']; simp

/-- The generating set includes vertices and edges; adjoints enter through star adjoin. -/
def generators : Set A := Set.range F.vertex ∪ Set.range F.edge

/-- The genuine norm-closed unital C*-subalgebra generated by this concrete family. -/
def generated : StarSubalgebra ℂ A := (StarAlgebra.adjoin ℂ F.generators).topologicalClosure

instance generated_closed : IsClosed (F.generated : Set A) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance generated_cstar : CStarAlgebra F.generated := inferInstance

theorem vertex_mem_generated (v : V) : F.vertex v ∈ F.generated :=
  StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ F.generators (Set.mem_union_left _ ⟨v, rfl⟩))

theorem edge_mem_generated (e : E) : F.edge e ∈ F.generated :=
  StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ F.generators (Set.mem_union_right _ ⟨e, rfl⟩))

/-- Minimality refers to norm-closed star subalgebras, not only algebraic words. -/
theorem generated_le (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (hv : ∀ v, F.vertex v ∈ S) (he : ∀ e, F.edge e ∈ S) : F.generated ≤ S := by
  apply StarSubalgebra.topologicalClosure_minimal _ hS
  apply StarAlgebra.adjoin_le
  rintro x (⟨v, rfl⟩ | ⟨e, rfl⟩)
  · exact hv v
  · exact he e

variable {B : Type*} [CStarAlgebra B]

/-- Existing actual unital star homomorphisms carry graph families to graph families. -/
def map (φ : A →⋆ₐ[ℂ] B) : Family source target B where
  vertex v := φ (F.vertex v)
  edge e := φ (F.edge e)
  vertex_projection v := ⟨by
    change φ (F.vertex v) * φ (F.vertex v) = φ (F.vertex v)
    rw [← map_mul, (F.vertex_projection v).isIdempotentElem.eq], by
    change star (φ (F.vertex v)) = φ (F.vertex v)
    rw [← map_star, (F.vertex_projection v).isSelfAdjoint.star_eq]⟩
  vertex_orthogonal v w h := by rw [← map_mul, F.vertex_orthogonal v w h, map_zero]
  vertex_sum := by rw [← map_sum, F.vertex_sum, map_one]
  initial e := by rw [← map_star, ← map_mul, F.initial]
  edge_orthogonal e f h := by rw [← map_star, ← map_mul, F.edge_orthogonal e f h, map_zero]
  outgoing v hv := by
    simp only [← map_star, ← map_mul, ← map_sum, F.outgoing v hv]

/-- Two continuous C*-homomorphisms agreeing on the concrete generators agree
on their entire norm-closed generated subalgebra. -/
theorem hom_eq_on_generated (φ ψ : A →⋆ₐ[ℂ] B)
    (hv : ∀ v, φ (F.vertex v) = ψ (F.vertex v))
    (he : ∀ e, φ (F.edge e) = ψ (F.edge e)) :
    ∀ a ∈ F.generated, φ a = ψ a := by
  apply F.generated_le (StarAlgHom.equalizer φ ψ)
    (isClosed_eq (map_continuous φ) (map_continuous ψ)) hv he

/-- Generator equality determines maps whenever the concrete family generates A. -/
theorem hom_ext (hgen : F.generated = ⊤) (φ ψ : A →⋆ₐ[ℂ] B)
    (hv : ∀ v, φ (F.vertex v) = ψ (F.vertex v))
    (he : ∀ e, φ (F.edge e) = ψ (F.edge e)) : φ = ψ := by
  apply StarAlgHom.ext
  intro a
  apply F.hom_eq_on_generated φ ψ hv he a
  rw [hgen]
  trivial

/-- The actual vertex element inside the generated closed subalgebra. -/
def vertexIn (v : V) : F.generated := ⟨F.vertex v, F.vertex_mem_generated v⟩

/-- The actual edge element inside the generated closed subalgebra. -/
def edgeIn (e : E) : F.generated := ⟨F.edge e, F.edge_mem_generated e⟩

/-- Maps whose domain is the generated C*-algebra are determined by the
vertices and edges. Norm closure is handled using automatic continuity. -/
theorem generated_hom_ext (φ ψ : F.generated →⋆ₐ[ℂ] B)
    (hv : ∀ v, φ (F.vertexIn v) = ψ (F.vertexIn v))
    (he : ∀ e, φ (F.edgeIn e) = ψ (F.edgeIn e)) : φ = ψ := by
  apply StarAlgHom.ext_topologicalClosure (map_continuous φ) (map_continuous ψ)
  apply StarAlgHom.ext_adjoin
  intro x hx
  rcases hx with ⟨v, hvx⟩ | ⟨e, hex⟩
  · have hxv : StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure _) x =
        F.vertexIn v := Subtype.ext hvx.symm
    exact ((congrArg φ hxv).trans (hv v)).trans (congrArg ψ hxv).symm
  · have hxe : StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure _) x =
        F.edgeIn e := Subtype.ext hex.symm
    exact ((congrArg φ hxe).trans (he e)).trans (congrArg ψ hxe).symm

/-- A genuine ambient star homomorphism restricts to the generated algebras.
This is restriction of an existing map, not assumed universal extension. -/
def generatedMap (φ : A →⋆ₐ[ℂ] B) : F.generated →⋆ₐ[ℂ] (F.map φ).generated :=
  (φ.comp F.generated.subtype).codRestrict (F.map φ).generated (by
    intro x
    have hle := F.generated_le ((F.map φ).generated.comap φ)
      ((F.map φ).generated_closed.preimage (map_continuous φ))
      (fun v => (F.map φ).vertex_mem_generated v)
      (fun e => (F.map φ).edge_mem_generated e)
    exact hle x.property)

@[simp] theorem generatedMap_coe (φ : A →⋆ₐ[ℂ] B) (x : F.generated) :
    (F.generatedMap φ x : B) = φ x := rfl

theorem generatedMap_contractive (φ : A →⋆ₐ[ℂ] B) (x : F.generated) :
    ‖F.generatedMap φ x‖ ≤ ‖x‖ := NonUnitalStarAlgHom.norm_apply_le _ _

theorem generatedMap_isometry (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) :
    Isometry (F.generatedMap φ) := by
  apply NonUnitalStarAlgHom.isometry
  intro x y hxy
  apply Subtype.ext
  apply hφ
  exact congrArg Subtype.val hxy

section InflatedFrame
variable [DecidableEq E]

local instance frameCoefficientOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance frameCoefficientOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- Diagonal multiplication with a concrete single-entry operator matrix. -/
private theorem diagonal_mul_single {N : Type*} [Fintype N] [DecidableEq N]
    (d : N → A) (i j : N) (a : A) :
    CStarMatrix.ofMatrix (Matrix.diagonal d) * CStarMatrix.ofMatrix (Matrix.single i j a) =
      CStarMatrix.ofMatrix (Matrix.single i j (d i * a)) := by
  change Matrix.diagonal d * Matrix.single i j a = Matrix.single i j (d i * a)
  ext r c
  simp only [Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    rfl
  · exact mul_zero _

private theorem single_mul_diagonal {N : Type*} [Fintype N] [DecidableEq N]
    (d : N → A) (i j : N) (a : A) :
    CStarMatrix.ofMatrix (Matrix.single i j a) * CStarMatrix.ofMatrix (Matrix.diagonal d) =
      CStarMatrix.ofMatrix (Matrix.single i j (a * d j)) := by
  change Matrix.single i j a * Matrix.diagonal d = Matrix.single i j (a * d j)
  ext r c
  simp only [Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    rfl
  · exact zero_mul _

/-- The manuscript's inflated projection for k=l=1: each vertex occurs twice. -/
def inflatedProjection : CStarMatrix (V ⊕ V) (V ⊕ V) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal (Sum.elim F.vertex F.vertex))

omit [DecidableEq E] in
theorem inflatedProjection_isProjection : IsStarProjection F.inflatedProjection := by
  refine ⟨?_, ?_⟩
  · change Matrix.diagonal (Sum.elim F.vertex F.vertex) *
      Matrix.diagonal (Sum.elim F.vertex F.vertex) =
      Matrix.diagonal (Sum.elim F.vertex F.vertex)
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    cases i <;> exact (F.vertex_projection _).isIdempotentElem.eq
  · change (Matrix.diagonal (Sum.elim F.vertex F.vertex)).conjTranspose =
      Matrix.diagonal (Sum.elim F.vertex F.vertex)
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    cases i <;> exact (F.vertex_projection _).isSelfAdjoint.star_eq

/-- The k=l=1 factor index: one P-coordinate and one Q-coordinate per incoming edge. -/
abbrev FrameIndex (v : V) := Option {e : E // target e = v}

/-- Concrete operators used in the manuscript's inflated graph corner, for
k=l=1. They are finite operator-norm matrices over the original C*-algebra. -/
def frameOp (v : V) : FrameIndex (target := target) v → CStarMatrix (V ⊕ V) (V ⊕ V) A
  | none => CStarMatrix.ofMatrix (Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v))
  | some e => CStarMatrix.ofMatrix
      (Matrix.single (Sum.inr (source e)) (Sum.inl v) (F.edge e))

omit [DecidableEq E] in
theorem frameOp_left_support (v : V) (i : FrameIndex (target := target) v) :
    F.inflatedProjection * F.frameOp v i = F.frameOp v i := by
  cases i with
  | none =>
    change CStarMatrix.ofMatrix (Matrix.diagonal _) * CStarMatrix.ofMatrix (Matrix.single _ _ _) = _
    rw [diagonal_mul_single]
    change CStarMatrix.ofMatrix (Matrix.single _ _ (F.vertex v * F.vertex v)) = _
    rw [(F.vertex_projection _).isIdempotentElem.eq]
    rfl
  | some e =>
    change CStarMatrix.ofMatrix (Matrix.diagonal _) * CStarMatrix.ofMatrix (Matrix.single _ _ _) = _
    rw [diagonal_mul_single]
    change CStarMatrix.ofMatrix (Matrix.single _ _ (F.vertex (source e) * F.edge e)) = _
    rw [F.edge_left_support]
    rfl

omit [DecidableEq E] in
theorem frameOp_right_support (v : V) (i : FrameIndex (target := target) v) :
    F.frameOp v i * F.inflatedProjection = F.frameOp v i := by
  cases i with
  | none =>
    change CStarMatrix.ofMatrix (Matrix.single _ _ _) * CStarMatrix.ofMatrix (Matrix.diagonal _) = _
    rw [single_mul_diagonal]
    change CStarMatrix.ofMatrix (Matrix.single _ _ (F.vertex v * F.vertex v)) = _
    rw [(F.vertex_projection _).isIdempotentElem.eq]
    rfl
  | some e =>
    change CStarMatrix.ofMatrix (Matrix.single _ _ _) * CStarMatrix.ofMatrix (Matrix.diagonal _) = _
    rw [single_mul_diagonal]
    change CStarMatrix.ofMatrix (Matrix.single _ _ (F.edge e * F.vertex v)) = _
    have he : F.edge e * F.vertex v = F.edge e := by
      simpa only [e.property] using F.edge_right_support (e : E)
    rw [he]
    rfl

/-- These operators really belong to the concrete normed corner q M q. -/
def frameInCorner (v : V) (i : FrameIndex (target := target) v) :
    CommonCorner.Corner F.inflatedProjection_isProjection :=
  CommonCorner.ofSupport F.inflatedProjection_isProjection (F.frameOp v i)
    (F.frameOp_left_support v i) (F.frameOp_right_support v i)

omit [DecidableEq E] in
@[simp] theorem frameInCorner_coe (v : V) (i : FrameIndex (target := target) v) :
    (F.frameInCorner v i : CStarMatrix (V ⊕ V) (V ⊕ V) A) = F.frameOp v i := rfl

/-- Common initial projection of the inflated incoming frame. -/
def baseMatrix (v : V) : CStarMatrix (V ⊕ V) (V ⊕ V) A := F.frameOp v none

omit [DecidableEq E] in
theorem baseMatrix_projection (v : V) : IsStarProjection (F.baseMatrix v) := by
  refine ⟨?_, ?_⟩
  · change Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v) *
      Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v) =
      (Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v) : Matrix (V ⊕ V) (V ⊕ V) A)
    rw [Matrix.single_mul_single_same, (F.vertex_projection v).isIdempotentElem.eq]
  · change (Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v) : Matrix (V ⊕ V) (V ⊕ V) A).conjTranspose = _
    rw [Matrix.conjTranspose_single, (F.vertex_projection v).isSelfAdjoint.star_eq]
    rfl

/-- Actual initial products, including the off-diagonal zero equations needed
for the factor matrix units. No matrix representation equivalence is assumed. -/
theorem frameOp_inner (v : V) (i j : FrameIndex (target := target) v) :
    star (F.frameOp v i) * F.frameOp v j = if i = j then F.baseMatrix v else 0 := by
  cases i with
  | none =>
    cases j with
    | none =>
      rw [if_pos rfl]
      change (Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v)).conjTranspose *
        Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v) =
        (Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v) : Matrix (V ⊕ V) (V ⊕ V) A)
      rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same,
        (F.vertex_projection v).isSelfAdjoint.star_eq, (F.vertex_projection v).isIdempotentElem.eq]
    | some e =>
      rw [if_neg (by simp)]
      change (Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v)).conjTranspose *
        Matrix.single (Sum.inr (source e)) (Sum.inl v) (F.edge e) =
        (0 : Matrix (V ⊕ V) (V ⊕ V) A)
      rw [Matrix.conjTranspose_single]
      exact Matrix.single_mul_single_of_ne _ _ _ _ (by simp) _
  | some e =>
    cases j with
    | none =>
      rw [if_neg (by simp)]
      change (Matrix.single (Sum.inr (source e)) (Sum.inl v) (F.edge e)).conjTranspose *
        Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v) =
        (0 : Matrix (V ⊕ V) (V ⊕ V) A)
      rw [Matrix.conjTranspose_single]
      exact Matrix.single_mul_single_of_ne _ _ _ _ (by simp) _
    | some f =>
      by_cases hef : e = f
      · subst f
        rw [if_pos rfl]
        change (Matrix.single (Sum.inr (source e)) (Sum.inl v) (F.edge e)).conjTranspose *
          Matrix.single (Sum.inr (source e)) (Sum.inl v) (F.edge e) =
          (Matrix.single (Sum.inl v) (Sum.inl v) (F.vertex v) : Matrix (V ⊕ V) (V ⊕ V) A)
        rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same, F.initial e, e.property]
      · rw [if_neg (by simpa)]
        change (Matrix.single (Sum.inr (source e)) (Sum.inl v) (F.edge e)).conjTranspose *
          Matrix.single (Sum.inr (source f)) (Sum.inl v) (F.edge f) =
          (0 : Matrix (V ⊕ V) (V ⊕ V) A)
        rw [Matrix.conjTranspose_single]
        by_cases hsrc : source e = source f
        · rw [hsrc, Matrix.single_mul_single_same,
            F.edge_orthogonal e f (fun h => hef (Subtype.ext h)), Matrix.single_zero]
        · exact Matrix.single_mul_single_of_ne _ _ _ _ (by simpa using hsrc) _

theorem frameOp_contractive (v : V) (i : FrameIndex (target := target) v) :
    ‖F.frameOp v i‖ ≤ 1 := by
  apply norm_le_one_of_initial (F.baseMatrix_projection v)
  rw [F.frameOp_inner, if_pos rfl]

/-- The inflated factor's candidate matrix units are concrete matrix products. -/
def frameUnit (v : V) (i j : FrameIndex (target := target) v) :
    CStarMatrix (V ⊕ V) (V ⊕ V) A := F.frameOp v i * star (F.frameOp v j)

omit [DecidableEq E] in
@[simp] theorem frameUnit_star (v : V) (i j : FrameIndex (target := target) v) :
    star (F.frameUnit v i j) = F.frameUnit v j i := by
  simp only [frameUnit, star_mul, star_star]

/-- The proposed F1 units satisfy the complete multiplication relations. -/
theorem frameUnit_mul (v : V) (i j k l : FrameIndex (target := target) v) :
    F.frameUnit v i j * F.frameUnit v k l = if j = k then F.frameUnit v i l else 0 := by
  change (F.frameOp v i * star (F.frameOp v j)) *
    (F.frameOp v k * star (F.frameOp v l)) = _
  rw [mul_assoc, ← mul_assoc (star (F.frameOp v j)), F.frameOp_inner]
  by_cases hjk : j = k
  · rw [if_pos hjk, if_pos hjk, ← mul_assoc]
    have hs : star (F.frameOp v i) * F.frameOp v i = F.baseMatrix v := by
      rw [F.frameOp_inner, if_pos rfl]
    rw [support_of_initial (F.baseMatrix_projection v) hs]
    rfl
  · rw [if_neg hjk, if_neg hjk, zero_mul, mul_zero]

end InflatedFrame

end Family
end Suzuki.GraphRelations

import Suzuki.GraphRelations
import Suzuki.FreeSelfAdjoint
import Suzuki.UniversalCStarRelations

/-!
# Constructing a finite graph C⋆-algebra

The universal algebra is constructed from all concrete Cuntz--Krieger families
in a specified carrier universe. Its supremum seminorm is finite by the free
self-adjoint polynomial estimate. The quotient and norm completion are actual
constructions. This does not yet prove vertex nonzeroness, graph simplicity,
nuclearity, K-theory, or the manuscript's finite-amalgam identification.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Suzuki.GraphUniversal

open GraphRelations

universe u v w

variable {V : Type v} {E : Type w} [Fintype V] [Fintype E] [DecidableEq V]
  (source target : E → V)

/-- All genuine graph representations in the specified target universe. -/
structure Representation where
  Carrier : Type u
  algebra : CStarAlgebra Carrier
  family : letI := algebra; Family source target Carrier

attribute [instance] Representation.algebra

instance representationNonempty : Nonempty (Representation.{u} source target) :=
  ⟨⟨ZeroAlgebra.{u}, inferInstance, zeroModel source target⟩⟩

abbrev Polynomial := FreeSelfAdjoint.Algebra (V ⊕ (E ⊕ E))

def polynomialVertex (v : V) : Polynomial (V := V) (E := E) :=
  FreeSelfAdjoint.generator _ (Sum.inl v)

def polynomialEdge (e : E) : Polynomial (V := V) (E := E) :=
  FreeSelfAdjoint.generator _ (Sum.inr (Sum.inl e)) +
    Complex.I • FreeSelfAdjoint.generator _ (Sum.inr (Sum.inr e))

def polynomialEvaluation (R : Representation.{u} source target) :
    Polynomial (V := V) (E := E) →⋆ₐ[ℂ] R.Carrier :=
  FreeSelfAdjoint.evaluate (fun i => (R.family.selfAdjointGenerator i : R.Carrier))
    (fun i => (R.family.selfAdjointGenerator i).property)

@[simp] theorem evaluation_vertex (R : Representation.{u} source target) (v : V) :
    polynomialEvaluation source target R (polynomialVertex v) = R.family.vertex v := by
  exact FreeSelfAdjoint.evaluate_generator _ _ _

@[simp] theorem evaluation_edge (R : Representation.{u} source target) (e : E) :
    polynomialEvaluation source target R (polynomialEdge e) = R.family.edge e := by
  simp only [polynomialEdge, map_add, map_smul, polynomialEvaluation,
    FreeSelfAdjoint.evaluate_generator]
  exact R.family.edge_from_selfAdjointGenerators e

/-- All representation norms are bounded by a bound proved from their generator
contractions, uniformly across the entire representation universe. -/
def boundedFamily : UniversalCStar.BoundedFamily (Polynomial (V := V) (E := E)) :=
  FreeSelfAdjoint.boundedFamily (fun R : Representation.{u} source target => R.Carrier)
    (fun R i => (R.family.selfAdjointGenerator i : R.Carrier))
    (fun R i => (R.family.selfAdjointGenerator i).property)
    (fun R i => R.family.selfAdjointGenerator_contractive i)

/-- The actual separated and completed graph algebra. -/
abbrev Algebra := UniversalCStar.Envelope (boundedFamily.{u} source target)

instance graphCStarAlgebra : CStarAlgebra (Algebra.{u} source target) := inferInstance

def inclusion : Polynomial (V := V) (E := E) →⋆ₐ[ℂ] Algebra.{u} source target :=
  UniversalCStar.inclusion (boundedFamily.{u} source target)

def vertex (v : V) : Algebra.{u} source target := inclusion.{u} source target (polynomialVertex v)
def edge (e : E) : Algebra.{u} source target := inclusion.{u} source target (polynomialEdge e)

/-- An equation true in every concrete family holds in the constructed algebra. -/
theorem equation (a b : Polynomial (V := V) (E := E))
    (h : ∀ R : Representation.{u} source target,
      polynomialEvaluation source target R a = polynomialEvaluation source target R b) :
    inclusion.{u} source target a = inclusion.{u} source target b :=
  (UniversalCStar.inclusion_eq_iff (boundedFamily.{u} source target) a b).mpr h

theorem vertex_projection (v : V) : IsStarProjection (vertex.{u} source target v) := by
  refine ⟨?_, ?_⟩
  · change inclusion.{u} source target (polynomialVertex v) *
      inclusion.{u} source target (polynomialVertex v) = inclusion.{u} source target (polynomialVertex v)
    rw [← map_mul]
    apply equation.{u}
    intro R
    simpa only [map_mul, evaluation_vertex] using (R.family.vertex_projection v).isIdempotentElem.eq
  · change star (inclusion.{u} source target (polynomialVertex v)) =
      inclusion.{u} source target (polynomialVertex v)
    rw [← map_star]
    exact congrArg (inclusion.{u} source target) (FreeSelfAdjoint.star_generator _ _)

theorem vertex_orthogonal (v w : V) (h : v ≠ w) :
    vertex.{u} source target v * vertex.{u} source target w = 0 := by
  change inclusion.{u} source target (polynomialVertex v) * inclusion.{u} source target (polynomialVertex w) = 0
  rw [← map_mul, ← map_zero (inclusion.{u} source target)]
  apply equation.{u}
  intro R
  simpa only [map_mul, map_zero, evaluation_vertex] using R.family.vertex_orthogonal v w h

theorem vertex_sum : ∑ v, vertex.{u} source target v = 1 := by
  change ∑ v, inclusion.{u} source target (polynomialVertex v) = 1
  rw [← map_sum, ← map_one (inclusion.{u} source target)]
  apply equation.{u}
  intro R
  simpa only [map_sum, map_one, evaluation_vertex] using R.family.vertex_sum

theorem initial (e : E) :
    star (edge.{u} source target e) * edge.{u} source target e = vertex.{u} source target (target e) := by
  change star (inclusion.{u} source target (polynomialEdge e)) * inclusion.{u} source target (polynomialEdge e) = _
  rw [← map_star, ← map_mul]
  apply equation.{u}
  intro R
  simpa only [map_mul, map_star, evaluation_vertex, evaluation_edge] using R.family.initial e

theorem edge_orthogonal (e f : E) (h : e ≠ f) :
    star (edge.{u} source target e) * edge.{u} source target f = 0 := by
  change star (inclusion.{u} source target (polynomialEdge e)) * inclusion.{u} source target (polynomialEdge f) = 0
  rw [← map_star, ← map_mul, ← map_zero (inclusion.{u} source target)]
  apply equation.{u}
  intro R
  simpa only [map_mul, map_star, map_zero, evaluation_edge] using R.family.edge_orthogonal e f h

theorem outgoing (v : V) (hv : ∃ e, source e = v) :
    ∑ e ∈ Finset.univ.filter (fun e => source e = v),
      edge.{u} source target e * star (edge.{u} source target e) = vertex.{u} source target v := by
  change ∑ e ∈ Finset.univ.filter (fun e => source e = v),
      inclusion.{u} source target (polynomialEdge e) * star (inclusion.{u} source target (polynomialEdge e)) = _
  simp only [← map_star, ← map_mul, ← map_sum]
  apply equation.{u}
  intro R
  simpa only [map_sum, map_mul, map_star, evaluation_edge, evaluation_vertex] using R.family.outgoing v hv

/-- The constructed elements satisfy the actual finite graph relations. -/
def family : Family source target (Algebra.{u} source target) where
  vertex := vertex.{u} source target
  edge := edge.{u} source target
  vertex_projection := vertex_projection source target
  vertex_orthogonal := vertex_orthogonal source target
  vertex_sum := vertex_sum source target
  initial := initial source target
  edge_orthogonal := edge_orthogonal source target
  outgoing := outgoing source target

variable {B : Type u} [CStarAlgebra B]

/-- Every concrete family in the chosen universe receives an actual unital
complex star homomorphism from the completed graph algebra. -/
def lift (F : Family source target B) : Algebra.{u} source target →⋆ₐ[ℂ] B :=
  UniversalCStar.representation (boundedFamily.{u} source target) ⟨B, inferInstance, F⟩

@[simp] theorem lift_vertex (F : Family source target B) (v : V) :
    lift source target F (vertex.{u} source target v) = F.vertex v :=
  (UniversalCStar.representation_inclusion _ _ _).trans (evaluation_vertex _ _ _ _)

@[simp] theorem lift_edge (F : Family source target B) (e : E) :
    lift source target F (edge.{u} source target e) = F.edge e :=
  (UniversalCStar.representation_inclusion _ _ _).trans (evaluation_edge _ _ _ _)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem polynomial_realPart (e : E) :
    (realPart (polynomialEdge (V := V) e) : Polynomial (V := V) (E := E)) =
      FreeSelfAdjoint.generator _ (Sum.inr (Sum.inl e)) := by
  have ha : IsSelfAdjoint (FreeSelfAdjoint.generator (V ⊕ (E ⊕ E)) (Sum.inr (Sum.inl e))) :=
    FreeSelfAdjoint.star_generator _ _
  have hb : IsSelfAdjoint (FreeSelfAdjoint.generator (V ⊕ (E ⊕ E)) (Sum.inr (Sum.inr e))) :=
    FreeSelfAdjoint.star_generator _ _
  calc
    _ = (realPart (FreeSelfAdjoint.generator (V ⊕ (E ⊕ E)) (Sum.inr (Sum.inl e))) :
        Polynomial (V := V) (E := E)) := by
      congr 1
      simp only [polynomialEdge, map_add, realPart_I_smul, hb.imaginaryPart, neg_zero, add_zero]
    _ = _ := ha.coe_realPart

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem polynomial_imaginaryPart (e : E) :
    (imaginaryPart (polynomialEdge (V := V) e) : Polynomial (V := V) (E := E)) =
      FreeSelfAdjoint.generator _ (Sum.inr (Sum.inr e)) := by
  have ha : IsSelfAdjoint (FreeSelfAdjoint.generator (V ⊕ (E ⊕ E)) (Sum.inr (Sum.inl e))) :=
    FreeSelfAdjoint.star_generator _ _
  have hb : IsSelfAdjoint (FreeSelfAdjoint.generator (V ⊕ (E ⊕ E)) (Sum.inr (Sum.inr e))) :=
    FreeSelfAdjoint.star_generator _ _
  calc
    _ = (realPart (FreeSelfAdjoint.generator (V ⊕ (E ⊕ E)) (Sum.inr (Sum.inr e))) :
        Polynomial (V := V) (E := E)) := by
      congr 1
      simp only [polynomialEdge, map_add, imaginaryPart_I_smul, ha.imaginaryPart, zero_add]
    _ = _ := hb.coe_realPart

/-- Agreement on the actual vertices and edges determines a map out of the
constructed completion. Density and algebraic freeness are both proved inputs. -/
theorem hom_ext {φ ψ : Algebra.{u} source target →⋆ₐ[ℂ] B}
    (hv : ∀ v, φ (vertex.{u} source target v) = ψ (vertex.{u} source target v))
    (he : ∀ e, φ (edge.{u} source target e) = ψ (edge.{u} source target e)) : φ = ψ := by
  apply UniversalCStar.hom_ext (boundedFamily.{u} source target)
  have h : φ.comp (inclusion.{u} source target) = ψ.comp (inclusion.{u} source target) := by
    apply FreeSelfAdjoint.hom_ext
    intro i
    rcases i with v | (e | e)
    · exact hv v
    · rw [← polynomial_realPart, map_realPart, map_realPart]
      exact congrArg (fun b : B => (realPart b : B)) (he e)
    · rw [← polynomial_imaginaryPart, map_imaginaryPart, map_imaginaryPart]
      exact congrArg (fun b : B => (imaginaryPart b : B)) (he e)
  intro a
  exact DFunLike.congr_fun h a

/-- The full unital universal property for all concrete CK families in the
chosen carrier universe. No candidate universal algebra is supplied as input. -/
theorem existsUnique_lift (F : Family source target B) :
    ∃! φ : Algebra.{u} source target →⋆ₐ[ℂ] B,
      (∀ v, φ (vertex.{u} source target v) = F.vertex v) ∧
      (∀ e, φ (edge.{u} source target e) = F.edge e) := by
  refine ⟨lift source target F, ⟨lift_vertex source target F, lift_edge source target F⟩, ?_⟩
  intro φ hφ
  apply hom_ext source target
  · intro v
    rw [hφ.1 v, lift_vertex]
  · intro e
    rw [hφ.2 e, lift_edge]

/-- A concrete nonzero vertex survives in the constructed universal algebra. -/
theorem vertex_ne_zero_of_representation (F : Family source target B) (v : V)
    (hv : F.vertex v ≠ 0) : vertex.{u} source target v ≠ 0 := by
  intro h
  apply hv
  rw [← lift_vertex source target F v, h, map_zero]

end Suzuki.GraphUniversal

import Suzuki.GraphPathRepresentation

/-! Nonzero universal graph generators for any supplied decision instance.
The path representation's classical instance is transported by proof
irrelevance, without changing the chosen representation universe. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Suzuki.GraphNonzero

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [d : DecidableEq V] (source target : E → V)

theorem universal_vertex_ne_zero (h : GraphRelations.NoSinks source) (vtx : V) :
    GraphUniversal.vertex.{v} source target vtx ≠ 0 := by
  let d' : DecidableEq V := fun a b => Classical.propDecidable (a = b)
  have hd : d = d' := Subsingleton.elim _ _
  let P (dec : DecidableEq V) : Prop :=
    letI : DecidableEq V := dec
    GraphUniversal.vertex.{v} source target vtx ≠ 0
  exact Eq.mpr (congrArg P hd)
    (GraphPathRepresentation.universal_vertex_ne_zero source target h vtx)

theorem universal_vertex_norm_one (h : GraphRelations.NoSinks source) (vtx : V) :
    ‖GraphUniversal.vertex.{v} source target vtx‖ = 1 := by
  let d' : DecidableEq V := fun a b => Classical.propDecidable (a = b)
  have hd : d = d' := Subsingleton.elim _ _
  let P (dec : DecidableEq V) : Prop :=
    letI : DecidableEq V := dec
    ‖GraphUniversal.vertex.{v} source target vtx‖ = 1
  exact Eq.mpr (congrArg P hd)
    (GraphPathRepresentation.universal_vertex_norm_one source target h vtx)

theorem universal_edge_ne_zero (h : GraphRelations.NoSinks source) (e : E) :
    GraphUniversal.edge.{v} source target e ≠ 0 := by
  let d' : DecidableEq V := fun a b => Classical.propDecidable (a = b)
  have hd : d = d' := Subsingleton.elim _ _
  let P (dec : DecidableEq V) : Prop :=
    letI : DecidableEq V := dec
    GraphUniversal.edge.{v} source target e ≠ 0
  exact Eq.mpr (congrArg P hd)
    (GraphPathRepresentation.universal_edge_ne_zero source target h e)

theorem universal_edge_norm_one (h : GraphRelations.NoSinks source) (e : E) :
    ‖GraphUniversal.edge.{v} source target e‖ = 1 := by
  have hc := CStarRing.norm_star_mul_self (x := GraphUniversal.edge.{v} source target e)
  rw [GraphUniversal.initial, universal_vertex_norm_one source target h] at hc
  nlinarith [norm_nonneg (GraphUniversal.edge.{v} source target e)]

theorem nontrivial [Nonempty V] (h : GraphRelations.NoSinks source) :
    Nontrivial (GraphUniversal.Algebra.{v} source target) :=
  nontrivial_of_ne (GraphUniversal.vertex.{v} source target (Classical.choice inferInstance)) 0
    (universal_vertex_ne_zero source target h _)

end Suzuki.GraphNonzero

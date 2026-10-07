import Suzuki.GraphUniversal
import Mathlib.Topology.Algebra.Module.Basic

/-! The constructed graph algebra is generated in norm by its vertices and
edges and is separable. The proof uses the actual completed envelope topology. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Suzuki.GraphDensity

open scoped Pointwise TensorProduct
open GraphRelations GraphUniversal

theorem countable_monoid_closure {A : Type*} [Monoid A] {s : Set A} (hs : s.Countable) :
    (Submonoid.closure s : Set A).Countable := by
  let : Countable s := hs.to_subtype
  have h : (Submonoid.closure s : Set A) ⊆
      Set.range (fun l : List s => (l.map Subtype.val).prod) := by
    intro a ha
    induction ha using Submonoid.closure_induction with
    | mem a ha => exact ⟨[⟨a, ha⟩], by simp⟩
    | one => exact ⟨[], rfl⟩
    | mul a b _ _ ha hb =>
      obtain ⟨la, rfl⟩ := ha
      obtain ⟨lb, rfl⟩ := hb
      exact ⟨la ++ lb, by simp⟩
  exact (Set.countable_range _).mono h

theorem closed_adjoin_separable {A : Type*} [CStarAlgebra A]
    {s : Set A} (hs : s.Countable) :
    TopologicalSpace.IsSeparable ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set A) := by
  have hstar : (star s).Countable := by simpa using hs.image (star : A → A)
  have hc := countable_monoid_closure (hs.union hstar)
  have hspan := hc.isSeparable.span (R := ℂ)
  have hsep : TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
    change TopologicalSpace.IsSeparable ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
    simpa only [← StarAlgebra.adjoin_eq_span] using hspan
  exact hsep.closure

universe u v w
variable {V : Type v} {E : Type w} [Fintype V] [Fintype E] [DecidableEq V]
  (source target : E → V)

private theorem realPart_mem (S : StarSubalgebra ℂ (Algebra.{u} source target))
    {x : Algebra.{u} source target} (hx : x ∈ S) : (realPart x : Algebra.{u} source target) ∈ S := by
  rw [realPart_apply_coe, ← Complex.coe_smul]
  have hs : star x ∈ S := star_mem hx
  exact S.smul_mem (S.add_mem hx hs) _

private theorem imaginaryPart_mem (S : StarSubalgebra ℂ (Algebra.{u} source target))
    {x : Algebra.{u} source target} (hx : x ∈ S) : (imaginaryPart x : Algebra.{u} source target) ∈ S := by
  rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
  have hs : star x ∈ S := star_mem hx
  exact S.smul_mem (S.smul_mem (S.sub_mem hx hs) _) _

theorem polynomial_inclusion_mem (S : StarSubalgebra ℂ (Algebra.{u} source target))
    (hv : ∀ v, vertex.{u} source target v ∈ S)
    (he : ∀ e, edge.{u} source target e ∈ S)
    (a : Polynomial (V := V) (E := E)) : inclusion.{u} source target a ∈ S := by
  have hgen : ∀ i, inclusion.{u} source target (FreeSelfAdjoint.generator (V ⊕ (E ⊕ E)) i) ∈ S := by
    intro i
    rcases i with v | (e | e)
    · exact hv v
    · rw [← polynomial_realPart, map_realPart]
      exact realPart_mem source target S (he e)
    · rw [← polynomial_imaginaryPart, map_imaginaryPart]
      exact imaginaryPart_mem source target S (he e)
  let g : FreeAlgebra ℝ (V ⊕ (E ⊕ E)) →ₐ[ℝ] Algebra.{u} source target :=
    ((inclusion.{u} source target).toAlgHom.restrictScalars ℝ).comp
      Algebra.TensorProduct.includeRight
  have hg : ∀ a, g a ∈ S := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 r =>
      rw [g.commutes]
      exact (S.toSubalgebra.restrictScalars ℝ).algebraMap_mem r
    | grade1 i => exact hgen i
    | add a b ha hb => rw [map_add]; exact S.add_mem ha hb
    | mul a b ha hb => rw [map_mul]; exact S.mul_mem ha hb
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact S.zero_mem
  | tmul z a =>
    have ht : (z ⊗ₜ[ℝ] a : Polynomial (V := V) (E := E)) = z • (1 ⊗ₜ[ℝ] a) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul]
    exact S.smul_mem (hg a) z
  | add a b ha hb => rw [map_add]; exact S.add_mem ha hb

/-- The specified vertices and edges generate the entire actual norm completion. -/
theorem generated_eq_top : (family.{u} source target).generated = ⊤ := by
  let S := (family.{u} source target).generated
  have hr : Set.range (inclusion.{u} source target) ⊆ (S : Set (Algebra.{u} source target)) := by
    rintro _ ⟨a, rfl⟩
    exact polynomial_inclusion_mem source target S
      (family.{u} source target).vertex_mem_generated
      (family.{u} source target).edge_mem_generated a
  have hd : DenseRange (inclusion.{u} source target) :=
    CStarSeminorm.inclusion_denseRange (A := UniversalCStar.Model (boundedFamily.{u} source target))
  have htop : Set.univ ⊆ (S : Set (Algebra.{u} source target)) := by
    rw [← hd.closure_range]
    exact closure_minimal hr (family.{u} source target).generated_closed
  apply top_unique
  intro a _
  exact htop (Set.mem_univ a)

instance separable : TopologicalSpace.SeparableSpace (Algebra.{u} source target) := by
  have hs : ((family.{u} source target).generators).Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  have h := closed_adjoin_separable hs
  change TopologicalSpace.IsSeparable ((family.{u} source target).generated :
    Set (Algebra.{u} source target)) at h
  rw [generated_eq_top] at h
  exact TopologicalSpace.isSeparable_univ_iff.mp h

end Suzuki.GraphDensity

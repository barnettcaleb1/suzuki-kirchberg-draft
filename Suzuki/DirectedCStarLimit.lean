import Suzuki.CStarCompletion
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# Concrete limits of injective directed C⋆-algebra systems

The algebraic direct limit is given its stage norm, which is well-defined
because the connecting star homomorphisms are injective and therefore isometric.
Its metric completion is an actual C⋆-algebra.
-/

noncomputable section

namespace Suzuki.DirectedCStarLimit

universe u v

variable {I : Type v} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (A : I → Type u) [∀ i, CStarAlgebra (A i)]
variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (fun i j h => f i j h)]
variable [hfi : Fact (∀ i j h, Function.Injective (f i j h))]

/-- The concrete quotient of stage elements by eventual equality. -/
abbrev Algebraic := DirectLimit A f

/-- Norm on the algebraic direct limit, using injectivity of the actual maps. -/
def stageNorm : Algebraic A f → ℝ :=
  DirectLimit.lift f (fun _ a => ‖a‖)
    (fun i j h a => (NonUnitalStarAlgHom.norm_map (f i j h) (hfi.out i j h) a).symm)

omit [Nonempty I] in
@[simp] theorem stageNorm_mk (i : I) (a : A i) :
    stageNorm A f ⟦⟨i, a⟩⟧ = ‖a‖ := rfl

def algebraicRingNorm : RingNorm (Algebraic A f) where
  toFun := stageNorm A f
  map_zero' := by
    rw [DirectLimit.zero_def (Classical.arbitrary I), stageNorm_mk, norm_zero]
  add_le' := DirectLimit.induction₂ f fun i a b => by
    simpa only [DirectLimit.add_def, stageNorm_mk] using norm_add_le a b
  mul_le' := DirectLimit.induction₂ f fun i a b => by
    simpa only [DirectLimit.mul_def, stageNorm_mk] using norm_mul_le a b
  neg' := DirectLimit.induction f fun i a => by
    simp only [DirectLimit.neg_def, stageNorm_mk, norm_neg]
  eq_zero_of_map_eq_zero' := DirectLimit.induction f fun i a ha => by
    have h : a = 0 := norm_eq_zero.mp ha
    subst a
    exact (DirectLimit.zero_def i).symm

instance algebraicNormedRing : NormedRing (Algebraic A f) :=
  (algebraicRingNorm A f).toNormedRing

@[simp] theorem norm_mk (i : I) (a : A i) :
    ‖(⟦⟨i, a⟩⟧ : Algebraic A f)‖ = ‖a‖ := rfl

instance algebraicNormedAlgebra : NormedAlgebra ℂ (Algebraic A f) where
  norm_smul_le z := DirectLimit.induction f fun i a => by
    simp only [DirectLimit.smul_def, norm_mk]
    exact norm_smul_le z a

instance algebraicCStarRing : CStarRing (Algebraic A f) where
  norm_mul_self_le := DirectLimit.induction f fun i a => by
    simpa only [DirectLimit.star_def, DirectLimit.mul_def, norm_mk] using
      CStarRing.norm_mul_self_le a

/-- The canonical algebraic inclusion of a stage. -/
def algebraicStage (i : I) : A i →⋆ₐ[ℂ] Algebraic A f where
  __ := DirectLimit.Algebra.of A f i
  map_star' _ := (DirectLimit.star_def _ _).symm

omit hfi in
@[simp] theorem algebraicStage_apply (i : I) (a : A i) :
    algebraicStage A f i a = ⟦⟨i, a⟩⟧ := rfl

theorem algebraicStage_isometry (i : I) : Isometry (algebraicStage A f i) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_mk A f i)

/-- The norm-completed direct limit. -/
abbrev Limit := UniformSpace.Completion (Algebraic A f)

instance limitCStarAlgebra : CStarAlgebra (Limit A f) := inferInstance

/-- Each original stage embeds isometrically in the completed algebra. -/
def stage (i : I) : A i →⋆ₐ[ℂ] Limit A f :=
  (CStarCompletion.inclusion : Algebraic A f →⋆ₐ[ℂ] Limit A f).comp
    (algebraicStage A f i)

theorem stage_isometry (i : I) : Isometry (stage A f i) :=
  CStarCompletion.inclusion_isometry.comp (algebraicStage_isometry A f i)

theorem stage_injective (i : I) : Function.Injective (stage A f i) :=
  (stage_isometry A f i).injective

theorem stage_commutes (i j : I) (h : i ≤ j) :
    (stage A f j).comp (f i j h) = stage A f i := by
  apply StarAlgHom.ext
  intro a
  exact congrArg (fun x : Algebraic A f => (x : Limit A f))
    (DirectLimit.mk_apply i j a h)

/-- The union of the actual stage images is norm dense in the completion. -/
theorem dense_stage_union : Dense (⋃ i, Set.range (stage A f i)) := by
  apply (UniformSpace.Completion.denseRange_coe (α := Algebraic A f)).mono
  rintro x ⟨a, rfl⟩
  obtain ⟨i, b, rfl⟩ := DirectLimit.exists_eq_mk f a
  exact Set.mem_iUnion.mpr ⟨i, b, rfl⟩

-- Use the norm topology, not the unrelated quotient topology on the raw set quotient.
local instance algebraicTopology : TopologicalSpace (Algebraic A f) :=
  (inferInstance : MetricSpace (Algebraic A f)).toUniformSpace.toTopologicalSpace

instance algebraicSeparable [Countable I] [∀ i, TopologicalSpace.SeparableSpace (A i)] :
    TopologicalSpace.SeparableSpace (Algebraic A f) := by
  let g : (Σ i, A i) → Algebraic A f := fun x => algebraicStage A f x.1 x.2
  have hc : Continuous g := continuous_sigma (fun i => (algebraicStage_isometry A f i).continuous)
  have hs : Function.Surjective g := by
    intro x
    obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk f x
    exact ⟨⟨i, a⟩, rfl⟩
  exact hs.denseRange.separableSpace hc

instance limitSeparable [Countable I] [∀ i, TopologicalSpace.SeparableSpace (A i)] :
    TopologicalSpace.SeparableSpace (Limit A f) := inferInstance

variable {B : Type*} [CStarAlgebra B]

/-- Compatible stage maps give an algebraic star homomorphism. -/
def algebraicLift (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ i j h a, g j (f i j h a) = g i a) : Algebraic A f →⋆ₐ[ℂ] B where
  __ := DirectLimit.Algebra.lift A f B (fun i => (g i).toAlgHom) hg
  map_star' := DirectLimit.lift_star g (fun i j h a => (hg i j h a).symm)

omit hfi in
@[simp] theorem algebraicLift_mk (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ i j h a, g j (f i j h a) = g i a) (i : I) (a : A i) :
    algebraicLift A f g hg ⟦⟨i, a⟩⟧ = g i a := rfl

theorem algebraicLift_contractive (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ i j h a, g j (f i j h a) = g i a) (x : Algebraic A f) :
    ‖algebraicLift A f g hg x‖ ≤ ‖x‖ := by
  induction x using DirectLimit.induction with
  | ih i a =>
    rw [algebraicLift_mk, norm_mk]
    exact NonUnitalStarAlgHom.norm_apply_le (g i) a

/-- The actual completion extension of compatible stage maps. -/
def lift (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ i j h a, g j (f i j h a) = g i a) : Limit A f →⋆ₐ[ℂ] B :=
  CStarCompletion.lift (algebraicLift A f g hg) (algebraicLift_contractive A f g hg)

@[simp] theorem lift_stage_apply (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ i j h a, g j (f i j h a) = g i a) (i : I) (a : A i) :
    lift A f g hg (stage A f i a) = g i a :=
  CStarCompletion.lift_coe _ _ _

/-- Maps from the completed limit are determined by their stage restrictions. -/
theorem hom_ext {g k : Limit A f →⋆ₐ[ℂ] B}
    (h : ∀ i a, g (stage A f i a) = k (stage A f i a)) : g = k := by
  apply CStarCompletion.hom_ext
  intro x
  induction x using DirectLimit.induction with
  | ih i a => exact h i a

theorem lift_unique (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ i j h a, g j (f i j h a) = g i a)
    (k : Limit A f →⋆ₐ[ℂ] B) (hk : ∀ i a, k (stage A f i a) = g i a) :
    k = lift A f g hg := by
  apply hom_ext
  intro i a
  rw [hk, lift_stage_apply]

end Suzuki.DirectedCStarLimit

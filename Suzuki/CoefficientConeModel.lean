import Suzuki.UnitizationRFD
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# A concrete RFD mapping cone

The cone consists of continuous paths on the compact interval, vanishing at
one, paired with an element of the ideal whose image is the initial value.
It carries the inherited genuine Cstar norm. For an injective inclusion into
an RFD algebra its actual point evaluations separate points by finite matrices.

This does not assume or prove nuclearity, semisplit exactness, the mapping-cone
KK equivalence or Bott periodicity. Those remain explicit separate obligations;
in particular the coefficient-model conclusion is not an input here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Suzuki.CoefficientConeModel
open scoped CStarAlgebra

abbrev Interval := Set.Icc (0 : ℝ) 1

def initial : Interval := ⟨0, le_rfl, zero_le_one⟩
def terminal : Interval := ⟨1, zero_le_one, le_rfl⟩

variable {I H : Type*} [NonUnitalCStarAlgebra I] [NonUnitalCStarAlgebra H]
variable (θ : I →⋆ₙₐ[ℂ] H)

/-- The actual mapping-cone equations inside the path algebra times the ideal. -/
def subalgebra : NonUnitalStarSubalgebra ℂ (C(Interval, H) × I) where
  carrier := {a | a.1 terminal = 0 ∧ a.1 initial = θ a.2}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    constructor
    · change a.1 terminal + b.1 terminal = 0
      rw [ha.1, hb.1, add_zero]
    · change a.1 initial + b.1 initial = θ (a.2+b.2)
      rw [ha.2, hb.2, map_add]
  mul_mem' := by
    intro a b ha hb
    constructor
    · change a.1 terminal * b.1 terminal = 0
      rw [ha.1, zero_mul]
    · change a.1 initial * b.1 initial = θ (a.2*b.2)
      rw [ha.2, hb.2, map_mul]
  smul_mem' := by
    intro z a ha
    constructor
    · change z • a.1 terminal = 0
      rw [ha.1, smul_zero]
    · change z • a.1 initial = θ (z • a.2)
      rw [ha.2, map_smul]
  star_mem' := by
    intro a ha
    constructor
    · change star (a.1 terminal) = 0
      rw [ha.1, star_zero]
    · change star (a.1 initial) = θ (star a.2)
      rw [ha.2, map_star]

instance closed : IsClosed (subalgebra θ : Set (C(Interval, H) × I)) := by
  change IsClosed {a : C(Interval, H) × I | a.1 terminal = 0 ∧ a.1 initial = θ a.2}
  apply IsClosed.inter
  · exact isClosed_eq ((continuous_eval_const terminal).comp continuous_fst)
      continuous_const
  · exact isClosed_eq ((continuous_eval_const initial).comp continuous_fst)
      ((map_continuous θ).comp continuous_snd)

abbrev Cone := subalgebra θ

instance coneCStarAlgebra : NonUnitalCStarAlgebra (Cone θ) := inferInstance

instance coneSeparable [TopologicalSpace.SeparableSpace I]
    [TopologicalSpace.SeparableSpace H] : TopologicalSpace.SeparableSpace (Cone θ) :=
  inferInstance

/-- The cone projection to the ideal coordinate. -/
def projection : Cone θ →⋆ₙₐ[ℂ] I where
  toFun a := a.val.2
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- Every ideal element is the endpoint of an explicit vanishing path. -/
theorem projection_surjective : Function.Surjective (projection θ) := by
  intro x
  let f : C(Interval, H) := ⟨fun t => (1 - (t : ℝ)) • θ x, by fun_prop⟩
  refine ⟨⟨(f, x), ?_⟩, rfl⟩
  constructor <;> simp [f, initial, terminal]

/-- Evaluation is a concrete complex nonunital star homomorphism. -/
def evaluation (t : Interval) : Cone θ →⋆ₙₐ[ℂ] H where
  toFun a := a.val.1 t
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- For an injective ideal inclusion a nonzero cone element has a nonzero
path value. This supplies the representation used in residual separation. -/
theorem exists_nonzero_evaluation (hθ : Function.Injective θ) (a : Cone θ) (ha : a ≠ 0) :
    ∃ t : Interval, evaluation θ t a ≠ 0 := by
  by_contra! hz
  have hf : a.val.1 = 0 := ContinuousMap.ext hz
  have hx : a.val.2 = 0 := hθ (by
    rw [map_zero]
    exact a.property.2.symm.trans (by rw [hf]; rfl))
  apply ha
  exact Subtype.ext (Prod.ext hf hx)

/-- The actual mapping cone of an injective map into an RFD algebra is RFD. -/
theorem rfd (hθ : Function.Injective θ) (hH : UnitizationRFD.IsRFD H) :
    UnitizationRFD.IsRFD (Cone θ) := by
  intro a ha
  obtain ⟨t, ht⟩ := exists_nonzero_evaluation θ hθ a ha
  obtain ⟨ρ, hρ⟩ := hH (evaluation θ t a) ht
  exact ⟨⟨ρ.dimension, ρ.positive_dimension, ρ.hom.comp (evaluation θ t)⟩, hρ⟩

/-- External unitization preserves the cone's proved residual separation. -/
theorem unitization_rfd (hθ : Function.Injective θ) (hH : UnitizationRFD.IsRFD H) :
    ResidualRepresentations.IsRFD (Unitization ℂ (Cone θ)) :=
  UnitizationRFD.unitization_rfd _ (rfd θ hθ hH)

/-- Separable ideal and extension algebra give actual unital matrix
representations of the cone unitization whose every tail separates points. -/
theorem exists_separating_tails [TopologicalSpace.SeparableSpace I]
    [TopologicalSpace.SeparableSpace H] (hθ : Function.Injective θ)
    (hH : UnitizationRFD.IsRFD H) :
    ∃ ρ : ℕ → ResidualRepresentations.Representation (Unitization ℂ (Cone θ)),
      ResidualRepresentations.SeparatingTails (Unitization ℂ (Cone θ)) ρ :=
  UnitizationRFD.exists_separating_tails _ (rfd θ hθ hH)

end Suzuki.CoefficientConeModel

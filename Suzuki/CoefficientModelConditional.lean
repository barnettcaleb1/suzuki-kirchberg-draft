import Suzuki.CoefficientConeModel
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# The concrete cone extension

The suspension here is the actual closed nonunital star subalgebra of
continuous paths on [0,1] vanishing at both endpoints, with the supremum
Cstar norm. It identifies isometrically with the closed two-sided kernel of
the actual cone projection. An explicit completely positive contractive
section proves this actual sequence semisplit. No nuclearity, tensor-product,
KK, or UCT input is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Suzuki.CoefficientModelConditional
open scoped CStarAlgebra
open CoefficientConeModel

variable (H : Type*) [NonUnitalCStarAlgebra H]

/-- Continuous paths vanishing at both endpoints. -/
def suspensionSubalgebra : NonUnitalStarSubalgebra ℂ C(Interval, H) where
  carrier := {f | f initial = 0 ∧ f terminal = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor <;> simp only [ContinuousMap.add_apply, hf.1, hf.2, hg.1, hg.2, add_zero]
  mul_mem' := by
    intro f g hf hg
    constructor <;> simp only [ContinuousMap.mul_apply, hf.1, hf.2, hg.1, hg.2, zero_mul]
  smul_mem' := by
    intro z f hf
    constructor <;> simp only [ContinuousMap.smul_apply, hf.1, hf.2, smul_zero]
  star_mem' := by
    intro f hf
    constructor <;> simp only [ContinuousMap.star_apply, hf.1, hf.2, star_zero]

instance suspensionClosed : IsClosed (suspensionSubalgebra H : Set C(Interval, H)) :=
  (isClosed_eq (continuous_eval_const initial) continuous_const).inter
    (isClosed_eq (continuous_eval_const terminal) continuous_const)

abbrev Suspension := suspensionSubalgebra H

instance suspensionCStarAlgebra : NonUnitalCStarAlgebra (Suspension H) := inferInstance
instance suspensionSeparable [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.SeparableSpace (Suspension H) := inferInstance

variable {H} {I : Type*} [NonUnitalCStarAlgebra I] (θ : I →⋆ₙₐ[ℂ] H)

/-- The suspension inclusion sends f to (f,0). -/
def inclusion : Suspension H →⋆ₙₐ[ℂ] Cone θ where
  toFun f := ⟨(f.val, 0), by exact ⟨f.property.2, f.property.1.trans (map_zero θ).symm⟩⟩
  map_zero' := rfl
  map_add' _ _ := by apply Subtype.ext; exact Prod.ext rfl (add_zero 0).symm
  map_mul' _ _ := by apply Subtype.ext; exact Prod.ext rfl (zero_mul 0).symm
  map_smul' _ _ := by apply Subtype.ext; exact Prod.ext rfl (smul_zero _).symm
  map_star' _ := by apply Subtype.ext; exact Prod.ext rfl (star_zero I).symm

@[simp] theorem projection_inclusion (f : Suspension H) :
    projection θ (inclusion θ f) = 0 := rfl

/-- Injectivity is literal equality of the path coordinates. -/
theorem inclusion_injective : Function.Injective (inclusion θ) := by
  intro f g h
  exact Subtype.ext (congrArg (fun a : Cone θ => a.val.1) h)

/-- The actual Cstar norms agree under the inclusion. -/
theorem inclusion_isometry : Isometry (inclusion θ) :=
  NonUnitalStarAlgHom.isometry (inclusion θ) (inclusion_injective θ)

/-- The actual kernel as a closed nonunital star subalgebra of the cone. -/
def projectionKernel : NonUnitalStarSubalgebra ℂ (Cone θ) :=
  NonUnitalStarAlgHom.equalizer (projection θ) (0 : Cone θ →⋆ₙₐ[ℂ] I)

instance projectionKernelClosed : IsClosed (projectionKernel θ : Set (Cone θ)) :=
  isClosed_eq (map_continuous (projection θ)) continuous_const

instance kernelCStarAlgebra : NonUnitalCStarAlgebra (projectionKernel θ) := inferInstance

/-- The inverse kernel map forgets the zero ideal coordinate. -/
def fromKernel : projectionKernel θ →⋆ₙₐ[ℂ] Suspension H where
  toFun a := ⟨a.val.val.1, by
    constructor
    · have hz : a.val.val.2 = 0 := a.property
      rw [a.val.property.2, hz, map_zero]
    · exact a.val.property.1⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- The concrete star algebra equivalence with the kernel. -/
def kernelEquiv : Suspension H ≃⋆ₐ[ℂ] projectionKernel θ where
  toFun f := ⟨inclusion θ f, rfl⟩
  invFun := fromKernel θ
  left_inv _ := rfl
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (show 0 = a.val.val.2 from a.property.symm)
  map_add' f g := by apply Subtype.ext; exact map_add (inclusion θ) f g
  map_mul' f g := by apply Subtype.ext; exact map_mul (inclusion θ) f g
  map_smul' z f := by apply Subtype.ext; exact map_smul (inclusion θ) z f
  map_star' f := by apply Subtype.ext; exact map_star (inclusion θ) f

/-- The kernel equivalence is isometric in the inherited Cstar norms. -/
theorem kernelEquiv_isometry : Isometry (kernelEquiv θ) :=
  NonUnitalStarAlgHom.isometry (kernelEquiv θ) (kernelEquiv θ).injective

/-- Exactness stated directly for the actual maps. -/
theorem inclusion_range_eq_kernel (a : Cone θ) :
    (∃ f : Suspension H, inclusion θ f = a) ↔ projection θ a = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    rfl
  · intro ha
    refine ⟨fromKernel θ ⟨a, ha⟩, ?_⟩
    exact congrArg Subtype.val ((kernelEquiv θ).apply_symm_apply ⟨a, ha⟩)

/-- The subalgebra kernel is the actual two-sided ideal kernel as a set. -/
theorem kernel_eq_ideal : (projectionKernel θ : Set (Cone θ)) =
    (TwoSidedIdeal.ker (projection θ) : Set (Cone θ)) := by
  ext a
  exact (TwoSidedIdeal.mem_ker (projection θ)).symm

theorem kernelIdeal_closed : IsClosed
    (TwoSidedIdeal.ker (projection θ) : Set (Cone θ)) := by
  rw [← kernel_eq_ideal]
  exact projectionKernelClosed θ

/-- The image of f ↦ (f,0) is exactly the closed two-sided ideal kernel. -/
theorem inclusion_range_eq_ideal : Set.range (inclusion θ) =
    (TwoSidedIdeal.ker (projection θ) : Set (Cone θ)) := by
  ext a
  exact (inclusion_range_eq_kernel θ a).trans (TwoSidedIdeal.mem_ker (projection θ)).symm

/-- The short exact cone sequence, without an injectivity assumption on theta. -/
theorem shortExact : Function.Injective (inclusion θ) ∧
    (∀ a : Cone θ, (∃ f : Suspension H, inclusion θ f = a) ↔ projection θ a = 0) ∧
    Function.Surjective (projection θ) :=
  ⟨inclusion_injective θ, inclusion_range_eq_kernel θ, projection_surjective θ⟩

/-- An explicit lift of an ideal element along the straight-line path. -/
def ramp (x : I) : Cone θ :=
  ⟨(⟨fun t => (1 - (t : ℝ)) • θ x, by fun_prop⟩, x), by
    constructor <;> simp [initial, terminal]⟩

@[simp] theorem projection_ramp (x : I) : projection θ (ramp θ x) = x := rfl

@[simp] theorem evaluation_ramp (t : Interval) (x : I) :
    evaluation θ t (ramp θ x) = (1 - (t : ℝ)) • θ x := rfl

/-- The path part of the lift is contractive in the supremum norm. -/
theorem ramp_path_norm_le (x : I) : ‖(ramp θ x).val.1‖ ≤ ‖x‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
  intro t
  change ‖(1 - (t : ℝ)) • θ x‖ ≤ ‖x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.property.2)]
  exact (mul_le_of_le_one_left (norm_nonneg (θ x)) (by linarith [t.property.1])).trans
    (NonUnitalStarAlgHom.norm_apply_le θ x)

/-- The lift is isometric because its second coordinate is the original element. -/
theorem ramp_norm (x : I) : ‖ramp θ x‖ = ‖x‖ := by
  change max ‖(ramp θ x).val.1‖ ‖x‖ = ‖x‖
  exact max_eq_right (ramp_path_norm_le θ x)

/-- The straight-line lift is complex linear. -/
def rampLinear : I →ₗ[ℂ] Cone θ where
  toFun := ramp θ
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · ext t
      exact (congrArg ((1 - (t : ℝ)) • ·) (map_add θ x y)).trans (smul_add ..)
    · rfl
  map_smul' z x := by
    apply Subtype.ext
    apply Prod.ext
    · ext t
      exact (congrArg ((1 - (t : ℝ)) • ·) (map_smul θ z x)).trans (smul_comm ..)
    · rfl

/-- A concrete isometric continuous linear section of the cone projection.
This is a Banach-space splitting; no multiplicativity or complete positivity
is claimed by this definition. -/
def linearSection : I →ₗᵢ[ℂ] Cone θ where
  toLinearMap := rampLinear θ
  norm_map' := ramp_norm θ

@[simp] theorem projection_linearSection (x : I) :
    projection θ (linearSection θ x) = x := rfl

/-- Removing the lifted endpoint gives the unique suspension coordinate. -/
def suspensionPart (a : Cone θ) : Suspension H :=
  fromKernel θ ⟨a - linearSection θ (projection θ a), by
    change projection θ (a - linearSection θ (projection θ a)) = 0
    rw [map_sub, projection_linearSection, sub_self]⟩

theorem decomposition (a : Cone θ) :
    inclusion θ (suspensionPart θ a) + linearSection θ (projection θ a) = a := by
  have h : inclusion θ (suspensionPart θ a) = a - linearSection θ (projection θ a) := by
    exact congrArg Subtype.val ((kernelEquiv θ).apply_symm_apply
      ⟨a - linearSection θ (projection θ a), by
        change projection θ (a - linearSection θ (projection θ a)) = 0
        rw [map_sub, projection_linearSection, sub_self]⟩)
  rw [h, sub_add_cancel]

/-- The two coordinates in the explicit Banach-space decomposition are unique. -/
theorem decomposition_unique (a : Cone θ) (f : Suspension H) (x : I)
    (h : inclusion θ f + linearSection θ x = a) :
    x = projection θ a ∧ f = suspensionPart θ a := by
  have hx : x = projection θ a := by
    have he := congrArg (projection θ) h
    simpa only [map_add, projection_inclusion, projection_linearSection, zero_add] using he
  refine ⟨hx, inclusion_injective θ ?_⟩
  apply add_right_cancel (b := linearSection θ (projection θ a))
  rw [decomposition, ← hx, h]

/-- The square-root ramp supplies actual square witnesses for positivity. -/
def sqrtRamp (x : I) : Cone θ :=
  ⟨(⟨fun t => Real.sqrt (1 - (t : ℝ)) • θ x, by fun_prop⟩, x), by
    constructor <;> simp [initial, terminal]⟩

/-- The ramp sends every product x* y to an actual product in the cone. -/
theorem sqrtRamp_star_mul (x y : I) :
    star (sqrtRamp θ x) * sqrtRamp θ y = ramp θ (star x * y) := by
  apply Subtype.ext
  apply Prod.ext
  · ext t
    change star (Real.sqrt (1 - (t : ℝ)) • θ x) *
      (Real.sqrt (1 - (t : ℝ)) • θ y) = (1 - (t : ℝ)) • θ (star x * y)
    simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul,
      Real.mul_self_sqrt (sub_nonneg.mpr t.property.2), map_mul, map_star]
  · rfl

/-- The entrywise section preserves positivity at every finite matrix level
by explicit square-root ramp factorization. -/
theorem ramp_matrix_square {n : Type*} [Fintype n] (M : CStarMatrix n n I) :
    (star M * M).map (ramp θ) = star (M.map (sqrtRamp θ)) * M.map (sqrtRamp θ) := by
  apply CStarMatrix.ext
  intro i j
  simp only [CStarMatrix.map_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply]
  change (rampLinear θ) (∑ k, star (M k i) * M k j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact (sqrtRamp_star_mul θ _ _).symm

/-- The canonical Cstar order on the cone. -/
instance conePartialOrder : PartialOrder (Cone θ) := CStarAlgebra.spectralOrder _
instance coneStarOrderedRing : StarOrderedRing (Cone θ) := CStarAlgebra.spectralOrderedRing _

/-- The explicit linear section is completely positive, with the canonical
Cstar matrix orders. Its norm-preserving property was proved above. -/
def completelyPositiveSection [PartialOrder I] [StarOrderedRing I] : I →CP Cone θ where
  toLinearMap := rampLinear θ
  map_cstarMatrix_nonneg' k M hM := by
    obtain ⟨N, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    change 0 ≤ (star N * N).map (ramp θ)
    rw [ramp_matrix_square]
    exact star_mul_self_nonneg _

@[simp] theorem projection_completelyPositiveSection [PartialOrder I] [StarOrderedRing I]
    (x : I) : projection θ (completelyPositiveSection θ x) = x := rfl

theorem completelyPositiveSection_norm [PartialOrder I] [StarOrderedRing I] (x : I) :
    ‖completelyPositiveSection θ x‖ = ‖x‖ := ramp_norm θ x

/-- The concrete short exact sequence admits an actual completely positive
contractive section. This theorem proves semisplitness of the cone extension;
it does not assume semisplitness, nuclearity, or a KK-model conclusion. -/
theorem semisplit [PartialOrder I] [StarOrderedRing I] :
    Function.Injective (inclusion θ) ∧
    (Set.range (inclusion θ) = (TwoSidedIdeal.ker (projection θ) : Set (Cone θ))) ∧
    Function.Surjective (projection θ) ∧
    ∃ σ : I →CP Cone θ, Function.RightInverse σ (projection θ) ∧
      ∀ x, ‖σ x‖ ≤ ‖x‖ := by
  refine ⟨inclusion_injective θ, inclusion_range_eq_ideal θ, projection_surjective θ,
    completelyPositiveSection θ, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    exact (completelyPositiveSection_norm θ x).le

section QuotientMap
variable {Q : Type*} [NonUnitalCStarAlgebra Q] (q : H →⋆ₙₐ[ℂ] Q)
variable (hqθ : ∀ x : I, q (θ x) = 0)

/-- The specific quotient-induced map from the inclusion cone to the
suspension of the quotient. For a quotient `Q = Suspension B`, its target
is literally the double suspension used in the coefficient argument. -/
def quotientSuspensionMap : Cone θ →⋆ₙₐ[ℂ] Suspension Q where
  toFun a := ⟨⟨fun t => q (a.val.1 t), (map_continuous q).comp a.val.1.continuous⟩, by
    constructor
    · change q (a.val.1 initial) = 0
      rw [a.property.2, hqθ]
    · change q (a.val.1 terminal) = 0
      rw [a.property.1, map_zero]⟩
  map_zero' := by apply Subtype.ext; ext t; exact map_zero q
  map_add' a b := by apply Subtype.ext; ext t; exact map_add q _ _
  map_mul' a b := by apply Subtype.ext; ext t; exact map_mul q _ _
  map_smul' z a := by apply Subtype.ext; ext t; exact map_smul q z _
  map_star' a := by apply Subtype.ext; ext t; exact map_star q _

@[simp] theorem quotientSuspensionMap_apply (a : Cone θ) (t : Interval) :
    (quotientSuspensionMap θ q hqθ a).val t = q (a.val.1 t) := rfl

theorem quotientSuspensionMap_contracts (a : Cone θ) :
    ‖quotientSuspensionMap θ q hqθ a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le (quotientSuspensionMap θ q hqθ) a

/-- A continuous linear section of the original quotient lifts each
vanishing path to the extension algebra, with zero ideal coordinate. -/
def quotientPathLift (σ : Q →L[ℂ] H) (f : Suspension Q) : Cone θ :=
  ⟨(⟨fun t => σ (f.val t), σ.continuous.comp f.val.continuous⟩, 0), by
    constructor
    · change σ (f.val terminal) = 0
      rw [f.property.2, map_zero]
    · change σ (f.val initial) = θ 0
      rw [f.property.1, map_zero, map_zero]⟩

/-- The displayed path lift is a right inverse of the quotient-induced cone map. -/
theorem quotientSuspensionMap_pathLift (σ : Q →L[ℂ] H)
    (hσ : Function.RightInverse σ q) (f : Suspension Q) :
    quotientSuspensionMap θ q hqθ (quotientPathLift θ σ f) = f := by
  apply Subtype.ext
  ext t
  exact hσ (f.val t)

/-- Surjectivity follows from an actual bounded linear splitting of the
original extension; no desired KK conclusion is a premise. -/
theorem quotientSuspensionMap_surjective (σ : Q →L[ℂ] H)
    (hσ : Function.RightInverse σ q) :
    Function.Surjective (quotientSuspensionMap θ q hqθ) := by
  intro f
  exact ⟨quotientPathLift θ σ f, quotientSuspensionMap_pathLift θ q hqθ σ hσ f⟩

/-- In particular the actual CPC data of a semisplit original extension
provide the bounded linear section needed for the path-lifting proof. -/
theorem quotientSuspensionMap_surjective_of_cpc
    [PartialOrder Q] [StarOrderedRing Q] [PartialOrder H] [StarOrderedRing H]
    (σ : Q →CP H) (hσ : Function.RightInverse σ q)
    (hσnorm : ∀ x, ‖σ x‖ ≤ ‖x‖) :
    Function.Surjective (quotientSuspensionMap θ q hqθ) := by
  let s : Q →L[ℂ] H := σ.toLinearMap.mkContinuous 1 (by
    intro x
    change ‖σ x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact hσnorm x)
  exact quotientSuspensionMap_surjective θ q hqθ s hσ

end QuotientMap
end Suzuki.CoefficientModelConditional

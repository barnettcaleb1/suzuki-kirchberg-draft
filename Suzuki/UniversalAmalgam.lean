import Suzuki.WeightedFreeSelfAdjoint
import Suzuki.UniversalCStarRelations
import Suzuki.GraphRelations
import Suzuki.CStarAmalgam

/-! Construction of the full unital Cstar amalgam. Its norm is the supremum
over all compatible pairs of actual star homomorphisms. No injectivity of the
input or output maps is asserted. The zero Cstar algebra is allowed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace Suzuki.UniversalAmalgam
universe u
variable {D A₀ A₁ : Type u} [CStarAlgebra D] [CStarAlgebra A₀] [CStarAlgebra A₁]
variable (i₀ : D →⋆ₐ[ℂ] A₀) (i₁ : D →⋆ₐ[ℂ] A₁)

structure Representation where
  Carrier : Type u
  algebra : CStarAlgebra Carrier
  left : letI := algebra; A₀ →⋆ₐ[ℂ] Carrier
  right : letI := algebra; A₁ →⋆ₐ[ℂ] Carrier
  commutes : letI := algebra; left.comp i₀ = right.comp i₁

attribute [instance] Representation.algebra

private def zeroHom (A : Type u) [CStarAlgebra A] : A →⋆ₐ[ℂ] GraphRelations.ZeroAlgebra.{u} where
  toFun := fun _ _ => 0
  map_zero' := Subsingleton.elim _ _
  map_one' := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _
  map_star' _ := Subsingleton.elim _ _

instance representationNonempty : Nonempty (Representation i₀ i₁) :=
  ⟨⟨GraphRelations.ZeroAlgebra.{u}, inferInstance, zeroHom A₀, zeroHom A₁,
    StarAlgHom.ext (fun _ => Subsingleton.elim _ _)⟩⟩

abbrev Generator := selfAdjoint A₀ ⊕ selfAdjoint A₁
abbrev Polynomial := FreeSelfAdjoint.Algebra (Generator (A₀ := A₀) (A₁ := A₁))

def representationGenerator (R : Representation i₀ i₁) : Generator (A₀ := A₀) (A₁ := A₁) → R.Carrier
  | Sum.inl a => R.left a
  | Sum.inr a => R.right a

theorem representationGenerator_selfAdjoint (R : Representation i₀ i₁) (g) :
    IsSelfAdjoint (representationGenerator i₀ i₁ R g) := by
  cases g with
  | inl a => exact a.property.map R.left
  | inr a => exact a.property.map R.right

def generatorBound : Generator (A₀ := A₀) (A₁ := A₁) → ℝ
  | Sum.inl a => ‖(a : A₀)‖
  | Sum.inr a => ‖(a : A₁)‖

theorem representationGenerator_bound (R : Representation i₀ i₁) (g) :
    ‖representationGenerator i₀ i₁ R g‖ ≤ generatorBound g := by
  cases g with
  | inl a => exact NonUnitalStarAlgHom.norm_apply_le R.left (a : A₀)
  | inr a => exact NonUnitalStarAlgHom.norm_apply_le R.right (a : A₁)

def evaluation (R : Representation i₀ i₁) : Polynomial (A₀ := A₀) (A₁ := A₁) →⋆ₐ[ℂ] R.Carrier :=
  FreeSelfAdjoint.evaluate (representationGenerator i₀ i₁ R)
    (representationGenerator_selfAdjoint i₀ i₁ R)

def boundedFamily : UniversalCStar.BoundedFamily (Polynomial (A₀ := A₀) (A₁ := A₁)) :=
  WeightedFreeSelfAdjoint.boundedFamily (fun R : Representation i₀ i₁ => R.Carrier)
    (representationGenerator i₀ i₁) (representationGenerator_selfAdjoint i₀ i₁)
    generatorBound (representationGenerator_bound i₀ i₁)

abbrev Algebra := UniversalCStar.Envelope (boundedFamily i₀ i₁)

def inclusion : Polynomial (A₀ := A₀) (A₁ := A₁) →⋆ₐ[ℂ] Algebra i₀ i₁ :=
  UniversalCStar.inclusion (boundedFamily i₀ i₁)

theorem equation (a b : Polynomial (A₀ := A₀) (A₁ := A₁))
    (h : ∀ R : Representation i₀ i₁, evaluation i₀ i₁ R a = evaluation i₀ i₁ R b) :
    inclusion i₀ i₁ a = inclusion i₀ i₁ b :=
  (UniversalCStar.inclusion_eq_iff (boundedFamily i₀ i₁) a b).mpr h

variable {i₀ i₁}
def polynomialLeft (a : A₀) : Polynomial (A₀ := A₀) (A₁ := A₁) :=
  FreeSelfAdjoint.generator _ (Sum.inl (realPart a)) +
    Complex.I • FreeSelfAdjoint.generator _ (Sum.inl (imaginaryPart a))
def polynomialRight (a : A₁) : Polynomial (A₀ := A₀) (A₁ := A₁) :=
  FreeSelfAdjoint.generator _ (Sum.inr (realPart a)) +
    Complex.I • FreeSelfAdjoint.generator _ (Sum.inr (imaginaryPart a))

@[simp] theorem evaluation_left (R : Representation i₀ i₁) (a : A₀) :
    evaluation i₀ i₁ R (polynomialLeft a) = R.left a := by
  simp only [polynomialLeft, map_add, map_smul, evaluation, FreeSelfAdjoint.evaluate_generator,
    representationGenerator]
  rw [← map_smul, ← map_add, realPart_add_I_smul_imaginaryPart]

@[simp] theorem evaluation_right (R : Representation i₀ i₁) (a : A₁) :
    evaluation i₀ i₁ R (polynomialRight a) = R.right a := by
  simp only [polynomialRight, map_add, map_smul, evaluation, FreeSelfAdjoint.evaluate_generator,
    representationGenerator]
  rw [← map_smul, ← map_add, realPart_add_I_smul_imaginaryPart]

variable (i₀ i₁)

def left : A₀ →⋆ₐ[ℂ] Algebra i₀ i₁ where
  toFun a := inclusion i₀ i₁ (polynomialLeft a)
  map_zero' := by rw [← map_zero (inclusion i₀ i₁)]; apply equation; intro R; simp
  map_one' := by rw [← map_one (inclusion i₀ i₁)]; apply equation; intro R; simp
  map_add' a b := by rw [← map_add]; apply equation; intro R; simp
  map_mul' a b := by rw [← map_mul]; apply equation; intro R; simp
  commutes' z := by rw [← (inclusion i₀ i₁).commutes]; apply equation; intro R; simp only [evaluation_left, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
  map_star' a := by rw [← map_star]; apply equation; intro R; simp only [map_star, evaluation_left]

def right : A₁ →⋆ₐ[ℂ] Algebra i₀ i₁ where
  toFun a := inclusion i₀ i₁ (polynomialRight a)
  map_zero' := by rw [← map_zero (inclusion i₀ i₁)]; apply equation; intro R; simp
  map_one' := by rw [← map_one (inclusion i₀ i₁)]; apply equation; intro R; simp
  map_add' a b := by rw [← map_add]; apply equation; intro R; simp
  map_mul' a b := by rw [← map_mul]; apply equation; intro R; simp
  commutes' z := by rw [← (inclusion i₀ i₁).commutes]; apply equation; intro R; simp only [evaluation_right, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
  map_star' a := by rw [← map_star]; apply equation; intro R; simp only [map_star, evaluation_right]

@[simp] theorem left_apply (a : A₀) : left i₀ i₁ a = inclusion i₀ i₁ (polynomialLeft a) := rfl
@[simp] theorem right_apply (a : A₁) : right i₀ i₁ a = inclusion i₀ i₁ (polynomialRight a) := rfl

theorem commutes : (left i₀ i₁).comp i₀ = (right i₀ i₁).comp i₁ := by
  apply StarAlgHom.ext
  intro d
  apply equation
  intro R
  simpa using DFunLike.congr_fun R.commutes d

variable {B : Type u} [CStarAlgebra B]

def lift (f₀ : A₀ →⋆ₐ[ℂ] B) (f₁ : A₁ →⋆ₐ[ℂ] B)
    (hf : f₀.comp i₀ = f₁.comp i₁) : Algebra i₀ i₁ →⋆ₐ[ℂ] B :=
  UniversalCStar.representation (boundedFamily i₀ i₁) ⟨B, inferInstance, f₀, f₁, hf⟩

@[simp] theorem lift_left (f₀ : A₀ →⋆ₐ[ℂ] B) (f₁ : A₁ →⋆ₐ[ℂ] B)
    (hf : f₀.comp i₀ = f₁.comp i₁) (a : A₀) : lift i₀ i₁ f₀ f₁ hf (left i₀ i₁ a) = f₀ a := by
  change UniversalCStar.representation (boundedFamily i₀ i₁) ⟨B, inferInstance, f₀, f₁, hf⟩
    (UniversalCStar.inclusion (boundedFamily i₀ i₁) (polynomialLeft a)) = _
  rw [UniversalCStar.representation_inclusion]
  exact evaluation_left ⟨B, inferInstance, f₀, f₁, hf⟩ a

@[simp] theorem lift_right (f₀ : A₀ →⋆ₐ[ℂ] B) (f₁ : A₁ →⋆ₐ[ℂ] B)
    (hf : f₀.comp i₀ = f₁.comp i₁) (a : A₁) : lift i₀ i₁ f₀ f₁ hf (right i₀ i₁ a) = f₁ a := by
  change UniversalCStar.representation (boundedFamily i₀ i₁) ⟨B, inferInstance, f₀, f₁, hf⟩
    (UniversalCStar.inclusion (boundedFamily i₀ i₁) (polynomialRight a)) = _
  rw [UniversalCStar.representation_inclusion]
  exact evaluation_right ⟨B, inferInstance, f₀, f₁, hf⟩ a

/-- Every free generator is an element of one of the actual factor images. -/
theorem inclusion_generator_left (a : selfAdjoint A₀) :
    inclusion i₀ i₁ (FreeSelfAdjoint.generator _ (Sum.inl a)) = left i₀ i₁ a := by
  apply equation
  intro R
  simp only [evaluation, FreeSelfAdjoint.evaluate_generator, representationGenerator]
  exact (evaluation_left R a).symm

theorem inclusion_generator_right (a : selfAdjoint A₁) :
    inclusion i₀ i₁ (FreeSelfAdjoint.generator _ (Sum.inr a)) = right i₀ i₁ a := by
  apply equation
  intro R
  simp only [evaluation, FreeSelfAdjoint.evaluate_generator, representationGenerator]
  exact (evaluation_right R a).symm

theorem hom_ext {φ ψ : Algebra i₀ i₁ →⋆ₐ[ℂ] B}
    (h₀ : φ.comp (left i₀ i₁) = ψ.comp (left i₀ i₁))
    (h₁ : φ.comp (right i₀ i₁) = ψ.comp (right i₀ i₁)) : φ = ψ := by
  apply UniversalCStar.hom_ext (boundedFamily i₀ i₁)
  have h : φ.comp (inclusion i₀ i₁) = ψ.comp (inclusion i₀ i₁) := by
    apply FreeSelfAdjoint.hom_ext
    intro g
    cases g with
    | inl a =>
      change φ (inclusion i₀ i₁ _) = ψ (inclusion i₀ i₁ _)
      rw [inclusion_generator_left]
      exact DFunLike.congr_fun h₀ (a : A₀)
    | inr a =>
      change φ (inclusion i₀ i₁ _) = ψ (inclusion i₀ i₁ _)
      rw [inclusion_generator_right]
      exact DFunLike.congr_fun h₁ (a : A₁)
  exact fun a => DFunLike.congr_fun h a

/-- Existence of the full amalgam is proved, with its actual complete norm. -/
theorem isFullAmalgam : CStarAmalgam.IsFullAmalgam i₀ i₁ (left i₀ i₁) (right i₀ i₁) where
  commutes := commutes i₀ i₁
  extension f₀ f₁ hf := by
    refine ⟨lift i₀ i₁ f₀ f₁ hf, ⟨StarAlgHom.ext (lift_left i₀ i₁ f₀ f₁ hf),
      StarAlgHom.ext (lift_right i₀ i₁ f₀ f₁ hf)⟩, ?_⟩
    intro φ hφ
    apply hom_ext i₀ i₁
    · exact hφ.1.trans (StarAlgHom.ext (lift_left i₀ i₁ f₀ f₁ hf)).symm
    · exact hφ.2.trans (StarAlgHom.ext (lift_right i₀ i₁ f₀ f₁ hf)).symm

end Suzuki.UniversalAmalgam

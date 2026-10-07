import Suzuki.IdempotentSystems
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Conditional KK calculation for the new idempotent-limit argument

A preadditive category is an explicit interface for degree-zero Kasparov
classes; composition is left-to-right. This file does not assert that its
objects/morphisms are actual Cstar algebras/KK groups. That correspondence,
including suspension and the analytic Milnor input below, is external.

The split-idempotent inverse-limit argument and the representing invertible
class are proved here. No UCT condition is imposed on any object.
-/

noncomputable section
namespace Suzuki.ConditionalKK
open CategoryTheory
open CategoryTheory.Preadditive

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A split scalar summand produces the reduced coefficient idempotent. -/
theorem reduced_idempotent {E K : C} (ε : E ⟶ K) (η : K ⟶ E)
    (h : η ≫ ε = 𝟙 K) :
    (𝟙 E - ε ≫ η) ≫ (𝟙 E - ε ≫ η) = 𝟙 E - ε ≫ η := by
  simp only [sub_comp, comp_sub, Category.id_comp, Category.comp_id]
  have he : (ε ≫ η) ≫ ε ≫ η = ε ≫ η := by
    rw [Category.assoc, ← Category.assoc η ε η, h, Category.id_comp]
  rw [he]
  abel

/-- Purely categorical split data, to be supplied by the checked channel
calculation and the published split exactness/biproduct inputs. -/
structure Splitting (F X : C) where
  j : F ⟶ X
  s : X ⟶ F
  retract : j ≫ s = 𝟙 F

namespace Splitting
variable {F X : C} (R : Splitting F X)

def f : X ⟶ X := R.s ≫ R.j

omit [Preadditive C] in
theorem idempotent : R.f ≫ R.f = R.f := by
  simp only [f, Category.assoc]
  rw [← Category.assoc R.j R.s R.j, R.retract, Category.id_comp]

omit [Preadditive C] in
theorem j_f : R.j ≫ R.f = R.j := by
  rw [f, ← Category.assoc, R.retract, Category.id_comp]

omit [Preadditive C] in
theorem f_s : R.f ≫ R.s = R.s := by
  rw [f, Category.assoc, R.retract, Category.comp_id]

/-- Precomposition on an actual additive Hom group of the supplied category. -/
def precompose (Z : C) : (X ⟶ Z) →+ (X ⟶ Z) := leftComp Z R.f

theorem precompose_idempotent (Z : C) (x : X ⟶ Z) :
    R.precompose Z (R.precompose Z x) = R.precompose Z x := by
  change R.f ≫ R.f ≫ x = R.f ≫ x
  rw [← Category.assoc, R.idempotent]

/-- This vanishing calculation has no countability assumption on Hom groups. -/
theorem coboundary_surjective (Z : C) :
    Function.Surjective (fun a : ℕ → (X ⟶ Z) =>
      fun n => a n - R.f ≫ a (n+1)) :=
  IdempotentSystems.one_sub_shift_surjective (R.precompose Z)
    (R.precompose_idempotent Z)

variable {L : C} (stage : ℕ → (X ⟶ L)) (hstage : ∀ n, R.f ≫ stage (n+1) = stage n)

include hstage in
/-- The transition relations and idempotence force the stage classes to be constant. -/
theorem stages_constant : ∀ n, stage n = stage 0 :=
  ((IdempotentSystems.compatible_iff_constant_fixed (R.precompose L)
    (R.precompose_idempotent L) stage).mp hstage).2

include hstage in
theorem stage_fixed (n : ℕ) : R.f ≫ stage n = stage n := by
  have hc := R.stages_constant stage hstage
  rw [hc n]
  exact ((IdempotentSystems.compatible_iff_constant_fixed (R.precompose L)
    (R.precompose_idempotent L) stage).mp hstage).1

def beta : F ⟶ L := R.j ≫ stage 0

include hstage in
theorem stage_eq_s_beta (n : ℕ) : stage n = R.s ≫ R.beta stage := by
  rw [beta, ← Category.assoc]
  change stage n = R.f ≫ stage 0
  rw [R.stage_fixed stage hstage 0, R.stages_constant stage hstage n]

end Splitting

/-- EXTERNAL INPUT: a usable presentation of the analytic Milnor exact
sequence after transporting all stages to X and all bonding classes to f.

The boundary is the composite from the product of degree-one groups through
coker(1-shift). `boundary_coboundary` records its descent to that quotient;
`kernel` is exactness at KK(L,Z); `onto` is surjectivity onto compatible
families. An actual KK instantiation must establish the separable/nuclear
system hypotheses and transport this published sequence. None of these
hypotheses or transport checks is discharged by this interface alone. -/
structure MilnorInput (S : C → C) {X L : C} (f : X ⟶ X)
    (stage : ℕ → (X ⟶ L)) where
  boundary : ∀ Z : C, (ℕ → (X ⟶ S Z)) →+ (L ⟶ Z)
  boundary_coboundary : ∀ (Z : C) (a : ℕ → (X ⟶ S Z)),
    boundary Z (fun n => a n - f ≫ a (n+1)) = 0
  kernel : ∀ (Z : C) (a : L ⟶ Z), (∀ n, stage n ≫ a = 0) →
    ∃ b : ℕ → (X ⟶ S Z), boundary Z b = a
  onto : ∀ (Z : C) (x : ℕ → (X ⟶ Z)), (∀ n, f ≫ x (n+1) = x n) →
    ∃ a : L ⟶ Z, ∀ n, stage n ≫ a = x n

namespace Splitting
variable {F X L : C} (R : Splitting F X) (S : C → C)
variable (stage : ℕ → (X ⟶ L)) (hstage : ∀ n, R.f ≫ stage (n+1) = stage n)
variable (M : MilnorInput S R.f stage)

/-- The external Milnor boundary vanishes by the proved 1-shift surjectivity. -/
theorem boundary_zero (Z : C) (b : ℕ → (X ⟶ S Z)) : M.boundary Z b = 0 := by
  obtain ⟨a, ha⟩ := R.coboundary_surjective (S Z) b
  rw [← ha]
  exact M.boundary_coboundary Z a

include M in
theorem restriction_injective (Z : C) {a b : L ⟶ Z}
    (h : ∀ n, stage n ≫ a = stage n ≫ b) : a = b := by
  have hz : ∀ n, stage n ≫ (a-b) = 0 := by
    intro n
    rw [comp_sub, h n, sub_self]
  obtain ⟨c, hc⟩ := M.kernel Z (a-b) hz
  have he : a-b = 0 := hc.symm.trans (R.boundary_zero S stage M Z c)
  exact sub_eq_zero.mp he

include hstage M in
/-- The explicit beta induces a bijection on every Hom group. -/
theorem beta_precompose_bijective (Z : C) :
    Function.Bijective (fun a : L ⟶ Z => R.beta stage ≫ a) := by
  constructor
  · intro a b hab
    change R.beta stage ≫ a = R.beta stage ≫ b at hab
    apply R.restriction_injective S stage M Z
    intro n
    rw [R.stage_eq_s_beta stage hstage n, Category.assoc, Category.assoc, hab]
  · intro y
    have hx : ∀ n : ℕ, R.f ≫ (R.s ≫ y) = R.s ≫ y := by
      intro n
      rw [← Category.assoc, R.f_s]
    obtain ⟨a, ha⟩ := M.onto Z (fun _ => R.s ≫ y) hx
    refine ⟨a, ?_⟩
    change R.beta stage ≫ a = y
    rw [beta, Category.assoc, ha 0, ← Category.assoc, R.retract, Category.id_comp]

/-- The new idempotent/Milnor argument yields an explicit categorical
isomorphism F ≅ L, conditional only on the stated Milnor interface and split
stage data. An actual KK equivalence requires the external correspondence. -/
def iso : F ≅ L := by
  let α := Classical.choose ((R.beta_precompose_bijective S stage hstage M F).surjective (𝟙 F))
  have hα : R.beta stage ≫ α = 𝟙 F := Classical.choose_spec
    ((R.beta_precompose_bijective S stage hstage M F).surjective (𝟙 F))
  refine ⟨R.beta stage, α, hα, ?_⟩
  apply (R.beta_precompose_bijective S stage hstage M L).injective
  change R.beta stage ≫ (α ≫ R.beta stage) = R.beta stage ≫ 𝟙 L
  rw [← Category.assoc, hα, Category.id_comp, Category.comp_id]

/-- The inverse class has exactly the prescribed stage restrictions; this is
the information needed later for the common corner's unit class. -/
theorem inverse_stage (n : ℕ) : stage n ≫ (R.iso S stage hstage M).inv = R.s := by
  rw [R.stage_eq_s_beta stage hstage n, Category.assoc]
  change R.s ≫ (R.iso S stage hstage M).hom ≫ (R.iso S stage hstage M).inv = R.s
  rw [Iso.hom_inv_id, Category.comp_id]

/-- An initial reduced coefficient class is retained exactly by the inverse.
The actual projection-to-class correspondence is still a separate obligation. -/
theorem retained_class {Z : C} (u : Z ⟶ F) (n : ℕ) :
    (u ≫ R.j ≫ stage n) ≫ (R.iso S stage hstage M).inv = u := by
  simp only [Category.assoc, R.inverse_stage S stage hstage M n,
    R.retract, Category.comp_id]

end Splitting

/-- Coordinates for the retained coefficient summand. There is no UCT
hypothesis: this is an additive category calculation. -/
structure FirstCoordinate (E X : C) where
  inclusion : E ⟶ X
  projection : X ⟶ E
  retract : inclusion ≫ projection = 𝟙 E

namespace FirstCoordinate
variable {F E X : C} (Q : FirstCoordinate E X)
variable (i : F ⟶ E) (r : E ⟶ F) (hi : i ≫ r = 𝟙 F)

/-- Split exactness followed by the first-coordinate inclusion gives j and s. -/
def splitting : Splitting F X where
  j := i ≫ Q.inclusion
  s := Q.projection ≫ r
  retract := by
    rw [Category.assoc, ← Category.assoc Q.inclusion Q.projection r,
      Q.retract, Category.id_comp, hi]

variable {K : C} (ε : E ⟶ K) (η : K ⟶ E)

/-- The sum of the prescribed +, - and zero channel classes equals the
split idempotent. Identifying the actual homomorphism classes with these
three expressions remains a new-construction obligation. -/
theorem three_channel_sum (hr : r ≫ i = 𝟙 E - ε ≫ η) :
    (Q.projection ≫ Q.inclusion) +
      (-(Q.projection ≫ ε ≫ η ≫ Q.inclusion)) + 0 =
        (Q.splitting i r hi).f := by
  change _ = (Q.projection ≫ r) ≫ (i ≫ Q.inclusion)
  rw [Category.assoc, ← Category.assoc r i Q.inclusion, hr,
    sub_comp, Category.id_comp, comp_sub]
  simp only [Category.assoc, add_zero, sub_eq_add_neg]

end FirstCoordinate
end Suzuki.ConditionalKK

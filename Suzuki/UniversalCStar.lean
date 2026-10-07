import Suzuki.CStarSeminorm
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# The C⋆-envelope of a pointwise bounded family of representations

This constructs the supremum seminorm, separates it, and completes it. The
carrier stays in the universe of the input algebra, even when the family of
representations lives in a larger universe. All representations in the supplied
family extend uniquely. The bounded family itself is explicit input: graph
presentations and their polynomial bounds are separate constructions.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Suzuki.UniversalCStar

universe u v w

variable (A : Type u) [Ring A] [StarRing A] [Algebra ℂ A]

set_option linter.checkUnivs false in
/-- Actual complex star representations with a pointwise finite norm bound.
The index is nonempty; zero representations into the zero algebra are allowed. -/
structure BoundedFamily where
  Index : Type w
  index_nonempty : Nonempty Index
  target : Index → Type v
  targetAlgebra : ∀ i, CStarAlgebra (target i)
  hom : letI := targetAlgebra; ∀ i, A →⋆ₐ[ℂ] target i
  bounded : letI := targetAlgebra; ∀ a, BddAbove (Set.range fun i => ‖hom i a‖)

attribute [instance] BoundedFamily.index_nonempty BoundedFamily.targetAlgebra

variable {A} (R : BoundedFamily.{u,v,w} A)

def supNorm (a : A) : ℝ := ⨆ i, ‖R.hom i a‖

theorem norm_le_supNorm (i : R.Index) (a : A) : ‖R.hom i a‖ ≤ supNorm R a :=
  le_ciSup (R.bounded a) i

theorem supNorm_nonneg (a : A) : 0 ≤ supNorm R a :=
  (norm_nonneg (R.hom (Classical.choice R.index_nonempty) a)).trans
    (norm_le_supNorm R _ a)

@[simp] theorem supNorm_zero : supNorm R 0 = 0 := by simp [supNorm]

@[simp] theorem supNorm_neg (a : A) : supNorm R (-a) = supNorm R a := by
  simp only [supNorm, map_neg, norm_neg]

@[simp] theorem supNorm_star (a : A) : supNorm R (star a) = supNorm R a := by
  simp only [supNorm, map_star, norm_star]

theorem supNorm_add_le (a b : A) : supNorm R (a+b) ≤ supNorm R a + supNorm R b := by
  apply ciSup_le
  intro i
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add (norm_le_supNorm R i a) (norm_le_supNorm R i b))

theorem supNorm_mul_le (a b : A) : supNorm R (a*b) ≤ supNorm R a * supNorm R b := by
  apply ciSup_le
  intro i
  rw [map_mul]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (norm_le_supNorm R i a) (norm_le_supNorm R i b)
      (norm_nonneg _) (supNorm_nonneg R a))

theorem supNorm_smul_le (z : ℂ) (a : A) : supNorm R (z • a) ≤ ‖z‖ * supNorm R a := by
  apply ciSup_le
  intro i
  rw [map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_le_supNorm R i a) (norm_nonneg z)

theorem supNorm_one_le : supNorm R 1 ≤ 1 := by
  apply ciSup_le
  intro i
  rw [map_one]
  exact (IsStarProjection.one (R.target i)).norm_le

/-- The C⋆-identity's lower inequality survives the supremum. -/
theorem supNorm_mul_self_le (a : A) :
    supNorm R a * supNorm R a ≤ supNorm R (star a * a) := by
  have hs := Real.sq_sqrt (supNorm_nonneg R (star a * a))
  have hr := Real.sqrt_nonneg (supNorm R (star a * a))
  have hle : supNorm R a ≤ Real.sqrt (supNorm R (star a * a)) := by
    apply ciSup_le
    intro i
    have h := norm_le_supNorm R i (star a * a)
    rw [map_mul, map_star, CStarRing.norm_star_mul_self] at h
    have hn := norm_nonneg (R.hom i a)
    nlinarith
  have hn := supNorm_nonneg R a
  nlinarith

/-- The actual submultiplicative seminorm, not an assumed universal norm. -/
def ringSeminorm : RingSeminorm A where
  toFun := supNorm R
  map_zero' := supNorm_zero R
  add_le' := supNorm_add_le R
  neg' := supNorm_neg R
  mul_le' := supNorm_mul_le R

variable [StarModule ℂ A]

/-- A type copy keeps this family's norm distinct from any other norm on A. -/
def Model (_R : BoundedFamily.{u,v,w} A) : Type u := A

instance modelRing : Ring (Model R) := inferInstanceAs (Ring A)
instance modelStarRing : StarRing (Model R) := inferInstanceAs (StarRing A)
instance modelAlgebra : Algebra ℂ (Model R) := inferInstanceAs (Algebra ℂ A)
instance modelStarModule : StarModule ℂ (Model R) := inferInstanceAs (StarModule ℂ A)
instance modelSeminormedRing : SeminormedRing (Model R) := (ringSeminorm R).toSeminormedRing
instance modelNormedStarGroup : NormedStarGroup (Model R) where
  norm_star_le a := (supNorm_star R a).le
instance modelNormedAlgebra : NormedAlgebra ℂ (Model R) where
  norm_smul_le := supNorm_smul_le R
instance modelCStarInequality : Fact (∀ a : Model R, ‖a‖ * ‖a‖ ≤ ‖star a * a‖) :=
  ⟨supNorm_mul_self_le R⟩

/-- The original algebra as the family's seminormed type copy. -/
def toModel : A →⋆ₐ[ℂ] Model R := StarAlgHom.id ℂ A

/-- The concrete complete C⋆-algebra, with carrier universe unchanged. -/
abbrev Envelope := CStarSeminorm.Envelope (Model R)

instance envelopeCStarAlgebra : CStarAlgebra (Envelope R) := inferInstance

def inclusion : A →⋆ₐ[ℂ] Envelope R := CStarSeminorm.inclusion.comp (toModel R)

omit [StarModule ℂ A] in
@[simp] theorem norm_inclusion (a : A) : ‖inclusion R a‖ = supNorm R a :=
  CStarSeminorm.norm_inclusion (toModel R a)

def modelRepresentation (i : R.Index) : Model R →⋆ₐ[ℂ] R.target i := R.hom i

/-- Every representation in the family extends by its proved supremum bound. -/
def representation (i : R.Index) : Envelope R →⋆ₐ[ℂ] R.target i :=
  CStarSeminorm.lift (modelRepresentation R i) (norm_le_supNorm R i)

omit [StarModule ℂ A] in
@[simp] theorem representation_inclusion (i : R.Index) (a : A) :
    representation R i (inclusion R a) = R.hom i a :=
  CStarSeminorm.lift_inclusion _ _ _

variable {B : Type*} [CStarAlgebra B]

theorem hom_ext {f g : Envelope R →⋆ₐ[ℂ] B}
    (h : ∀ a : A, f (inclusion R a) = g (inclusion R a)) : f = g :=
  CStarSeminorm.hom_ext h

theorem representation_unique (i : R.Index) (f : Envelope R →⋆ₐ[ℂ] R.target i)
    (hf : ∀ a, f (inclusion R a) = R.hom i a) : f = representation R i := by
  apply hom_ext R
  intro a
  rw [hf, representation_inclusion]

end Suzuki.UniversalCStar

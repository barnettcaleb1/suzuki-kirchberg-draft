import Suzuki.UniversalCStar
import Mathlib.Algebra.Star.Free
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# A free complex star algebra on self-adjoint generators

Complexifying the real free algebra gives the genuine algebraic star
presentation used below. The representation bound is proved from bounded
generators by algebraic induction; no norm or C⋆-completion is assumed here.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Suzuki.FreeSelfAdjoint

open scoped TensorProduct

variable (ι : Type*)

instance realFreeStarModule : StarModule ℝ (FreeAlgebra ℝ ι) where
  star_smul r a := by
    rw [Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap]
    simp only [star_trivial]
    exact (Algebra.commutes r (star a)).symm

/-- The algebraic complexification of the real free algebra. -/
abbrev Algebra := ℂ ⊗[ℝ] FreeAlgebra ℝ ι

instance complexStarModule : StarModule ℂ (Algebra ι) where
  star_smul z a := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp only [TensorProduct.smul_tmul', TensorProduct.star_tmul, star_smul]
    | add a b ha hb => simp only [smul_add, star_add, ha, hb]

def generator (i : ι) : Algebra ι := 1 ⊗ₜ[ℝ] FreeAlgebra.ι ℝ i

@[simp] theorem star_generator (i : ι) : star (generator ι i) = generator ι i := by
  simp only [generator, TensorProduct.star_tmul, star_one, FreeAlgebra.star_ι]

variable {ι} {B : Type*} [CStarAlgebra B]

theorem realLift_star (f : ι → B) (hf : ∀ i, IsSelfAdjoint (f i)) (a : FreeAlgebra ℝ ι) :
    FreeAlgebra.lift ℝ f (star a) = star (FreeAlgebra.lift ℝ f a) := by
  induction a using FreeAlgebra.induction with
  | grade0 r => simp [Algebra.algebraMap_eq_smul_one, star_smul]
  | grade1 i => simpa only [FreeAlgebra.star_ι, FreeAlgebra.lift_ι_apply] using (hf i).star_eq.symm
  | add a b ha hb => simp only [star_add, map_add, ha, hb]
  | mul a b ha hb => simp only [star_mul, map_mul, ha, hb]

/-- Evaluation in a genuine C⋆-algebra of any self-adjoint generator family. -/
def evaluate (f : ι → B) (hf : ∀ i, IsSelfAdjoint (f i)) : Algebra ι →⋆ₐ[ℂ] B where
  __ := AlgHom.liftEquiv ℝ ℂ (FreeAlgebra ℝ ι) B (FreeAlgebra.lift ℝ f)
  map_star' a := by
    change (AlgHom.liftEquiv ℝ ℂ (FreeAlgebra ℝ ι) B (FreeAlgebra.lift ℝ f)) (star a) =
      star ((AlgHom.liftEquiv ℝ ℂ (FreeAlgebra ℝ ι) B (FreeAlgebra.lift ℝ f)) a)
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul z a => simp only [TensorProduct.star_tmul, AlgHom.liftEquiv_tmul,
        star_smul, realLift_star f hf]
    | add a b ha hb => simp only [star_add, map_add, ha, hb]

@[simp] theorem evaluate_tmul (f : ι → B) (hf : ∀ i, IsSelfAdjoint (f i))
    (z : ℂ) (a : FreeAlgebra ℝ ι) :
    evaluate f hf (z ⊗ₜ[ℝ] a) = z • FreeAlgebra.lift ℝ f a := rfl

@[simp] theorem evaluate_generator (f : ι → B) (hf : ∀ i, IsSelfAdjoint (f i)) (i : ι) :
    evaluate f hf (generator ι i) = f i := by
  simp only [generator, evaluate_tmul, FreeAlgebra.lift_ι_apply, one_smul]

/-- The real free-polynomial evaluations have a bound uniform over all
contractive choices of generators in the given family of target algebras. -/
theorem real_polynomial_bound {J : Type*} (C : J → Type*) [∀ j, CStarAlgebra (C j)]
    (f : ∀ j, ι → C j) (hf : ∀ j i, ‖f j i‖ ≤ 1) (a : FreeAlgebra ℝ ι) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j, ‖FreeAlgebra.lift ℝ (f j) a‖ ≤ M := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨‖r‖, norm_nonneg _, ?_⟩
    intro j
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg r) (IsStarProjection.one (C j)).norm_le
  | grade1 i => exact ⟨1, zero_le_one, fun j => by simpa using hf j i⟩
  | add a b ha hb =>
    obtain ⟨M, hM, hMa⟩ := ha
    obtain ⟨N, hN, hNb⟩ := hb
    refine ⟨M+N, add_nonneg hM hN, fun j => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hMa j) (hNb j))
  | mul a b ha hb =>
    obtain ⟨M, hM, hMa⟩ := ha
    obtain ⟨N, hN, hNb⟩ := hb
    refine ⟨M*N, mul_nonneg hM hN, fun j => ?_⟩
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (hMa j) (hNb j) (norm_nonneg _) hM)

theorem polynomial_bound {J : Type*} (C : J → Type*) [∀ j, CStarAlgebra (C j)]
    (f : ∀ j, ι → C j) (hsa : ∀ j i, IsSelfAdjoint (f j i))
    (hf : ∀ j i, ‖f j i‖ ≤ 1) (a : Algebra ι) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j, ‖evaluate (f j) (hsa j) a‖ ≤ M := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, le_rfl, fun j => by simp⟩
  | tmul z a =>
    obtain ⟨M, hM, hMa⟩ := real_polynomial_bound C f hf a
    refine ⟨‖z‖*M, mul_nonneg (norm_nonneg _) hM, fun j => ?_⟩
    rw [evaluate_tmul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hMa j) (norm_nonneg z)
  | add a b ha hb =>
    obtain ⟨M, hM, hMa⟩ := ha
    obtain ⟨N, hN, hNb⟩ := hb
    refine ⟨M+N, add_nonneg hM hN, fun j => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hMa j) (hNb j))

/-- The representation family satisfies the analytic envelope's boundedness
requirement by the preceding polynomial estimate. -/
def boundedFamily {J : Type*} [Nonempty J] (C : J → Type*) [∀ j, CStarAlgebra (C j)]
    (f : ∀ j, ι → C j) (hsa : ∀ j i, IsSelfAdjoint (f j i))
    (hf : ∀ j i, ‖f j i‖ ≤ 1) : UniversalCStar.BoundedFamily (Algebra ι) where
  Index := J
  index_nonempty := inferInstance
  target := C
  targetAlgebra := inferInstance
  hom j := evaluate (f j) (hsa j)
  bounded a := by
    obtain ⟨M, _, hM⟩ := polynomial_bound C f hsa hf a
    exact ⟨M, fun _ ⟨j, hj⟩ => hj ▸ hM j⟩

/-- Complex algebra homomorphisms are determined by the real free generators. -/
theorem hom_ext {φ ψ : Algebra ι →⋆ₐ[ℂ] B}
    (h : ∀ i, φ (generator ι i) = ψ (generator ι i)) : φ = ψ := by
  have he : φ.toAlgHom = ψ.toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    apply FreeAlgebra.hom_ext
    funext i
    exact h i
  exact StarAlgHom.ext (fun a => DFunLike.congr_fun he a)

end Suzuki.FreeSelfAdjoint

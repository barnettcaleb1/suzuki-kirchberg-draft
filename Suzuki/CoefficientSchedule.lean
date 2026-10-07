import Suzuki.CoefficientModelFromExtension
import Suzuki.TensorEvaluationPaths
import Suzuki.RecursiveGraphSequence

/-! The coefficient model's actual separating sequence fixes the noise sizes
in the recursive finite diagrams. The universe lift changes only the finite
matrix index set. No independently supplied schedule or recursive existence
hypothesis is introduced. -/
noncomputable section
namespace Suzuki.CoefficientSchedule
open TensorCoefficientChannels
open scoped CStarAlgebra ComplexOrder
universe u
abbrev Coefficient := CoefficientModelFromExtension.Algebra.{u}

variable (F : Coefficient.{u})

def E : Algebra.{u} := ⟨Unitization ℂ F, inferInstance⟩

def quotient : E F →⋆ₐ[ℂ] ℂ := CoefficientModelFromExtension.scalarQuotient F

def sectionMap : ℂ →⋆ₐ[ℂ] E F := CoefficientModelFromExtension.scalarSection F

@[simp] theorem quotient_section (z : ℂ) : quotient F (sectionMap F z) = z := rfl

structure Schedule where
  representation : ℕ → ResidualRepresentations.Representation (E F)
  tails : ResidualRepresentations.SeparatingTails (E F) representation

/-- Countability and repeated tails are already proved for the actual unitization. -/
def schedule (hF : UnitizationRFD.IsRFD F) : Schedule F :=
  let h := UnitizationRFD.exists_separating_tails F hF
  ⟨Classical.choose h, Classical.choose_spec h⟩

namespace Schedule
variable {F} (R : Schedule F)

def dimension (n : ℕ) : ℕ := (R.representation n).dimension

theorem dimension_pos (n : ℕ) : 0 < R.dimension n :=
  (R.representation n).positive_dimension

/-- The actual sigma used by spatial tensor/matrix identification. -/
def sigma (n : ℕ) : E F →⋆ₐ[ℂ] matrixAlgebra.{u} (R.dimension n) :=
  (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ulift.symm : Fin (R.dimension n) ≃ ULift.{u} (Fin (R.dimension n)))).toStarAlgHom.comp
    (R.representation n).hom

theorem sigma_tails (N : ℕ) (e : E F) (he : e ≠ 0) :
    ∃ j, N ≤ j ∧ R.sigma j e ≠ 0 := by
  obtain ⟨j, hj, hd⟩ := R.tails N e he
  refine ⟨j,hj,fun hz => hd ?_⟩
  apply (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ulift.symm : Fin (R.dimension j) ≃ ULift.{u} (Fin (R.dimension j)))).injective
  exact hz.trans (map_zero _).symm

/-- Balanced initial weights dictated by the stabilized common projection. -/
def recursive (n : ℕ) : RecursiveGraphSequence.System R.dimension
    (fun _ => n+1) (fun _ => 1) :=
  RecursiveGraphSequence.construct R.dimension R.dimension_pos
    (fun _ => n+1) (fun _ => 1) (fun _ => Nat.zero_lt_succ n) (fun _ => by decide)

theorem recursive_initial (n : ℕ) :
    (R.recursive n).stage 0 = RecursiveGraphSequence.Stage.initial
      (fun _ => n+1) (fun _ => 1) (fun _ => Nat.zero_lt_succ n) (fun _ => by decide) :=
  rfl
end Schedule
end Suzuki.CoefficientSchedule

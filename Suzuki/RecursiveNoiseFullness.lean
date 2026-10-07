import Suzuki.RecursiveGraphSequence
import Suzuki.OrthogonalNoiseFullness

/-! Actual recursive noise images are full in every finite target constituent.
The proof uses the retained multiplicity certificates and the exact canonical
aggregation maps. No full-image or simplicity assertion is an external input. -/
noncomputable section
namespace Suzuki.RecursiveNoiseFullness
open Matrix MultiplicityEmbeddings FiniteDiagram OrthogonalFiniteDiagrams
open PositiveMultiplicityFullness OrthogonalNoiseFullness RecursiveGraphSequence
open scoped CStarAlgebra ComplexOrder
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Stack
variable {C n m : Type*} [Fintype C] [Fintype n] [Fintype m]
  [DecidableEq C] [DecidableEq n] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
theorem canonicalFactor_nonzero (w : C → n → ℕ) (D : n → ℕ) (hD : total w = D)
    (H : Matrix m n ℕ) (d : C → m → ℕ) (hd : ∀ c, targetSize (w c) H = d c)
    (f : m → ℕ) (hf : targetSize D H = f) (c : C) (v : m)
    (a : Blocks (d c)) (ha : a v ≠ 0) :
    channel (B := Blocks f) (fun c => Blocks (d c)) (canonicalFactor w D hD H d hd f hf) c a v ≠ 0 := by
  subst D
  have hd' : (fun c => targetSize (w c) H) = d := funext hd
  subst d
  subst f
  exact factor_channel_block_ne_zero w H c v ha
end Stack

namespace Lift
variable {P : Stage} {q : ℕ} (D : RecursiveGraphSequence.Lift P q)

theorem common_nonzero (c : Channel)
    (a : Blocks (Sum.elim (P.scaledK q c) (P.scaledL q c))) (ha : a ≠ 0)
    (v : Vertex ⊕ Vertex) : D.diagram.common c a v ≠ 0 := by
  rw [Lift.aggregate_common]
  exact stackInto_channel_block_ne_zero (commonWeights D.K D.L)
    (Sum.elim (total D.K) (total D.L)) (total_commonWeights D.K D.L) c v
    (image_block_ne_zero _ _ _ _ (D.realization c).common_multiplicity
      (D.natural_positive c) ha v)

theorem left_nonzero (c : Channel) (a : Blocks (P.scaledK q c + P.scaledL q c))
    (ha : a ≠ 0) (v : Vertex) : D.diagram.left c a v ≠ 0 := by
  rw [Lift.aggregate_left]
  apply canonicalFactor_nonzero (commonWeights D.K D.L)
    (Sum.elim (total D.K) (total D.L)) (total_commonWeights D.K D.L)
    firstMultiplicity (fun c => D.K c + D.L c)
    (fun c => first_targetSize (D.K c) (D.L c)) (total D.K + total D.L)
    (first_targetSize (total D.K) (total D.L)) c v
  exact image_block_ne_zero _ _ _ _ (D.realization c).left_multiplicity
    (natMatrix_positive _ (D.S_pos c)) ha v

theorem right_nonzero (c : Channel) (a : Blocks (P.scaledK q c + P.A *ᵥ P.scaledL q c))
    (ha : a ≠ 0) (v : Vertex) : D.diagram.right c a v ≠ 0 := by
  rw [Lift.aggregate_right]
  apply canonicalFactor_nonzero (commonWeights D.K D.L)
    (Sum.elim (total D.K) (total D.L)) (total_commonWeights D.K D.L)
    (secondMultiplicity D.next.A) (fun c => D.K c + D.next.A *ᵥ D.L c)
    (fun c => second_targetSize D.next.A (D.K c) (D.L c))
    (total D.K + D.next.A *ᵥ total D.L)
    (second_targetSize D.next.A (total D.K) (total D.L)) c v
  exact image_block_ne_zero _ _ _ _ (D.realization c).right_multiplicity
    (natMatrix_positive _ (D.R_pos c)) ha v

variable {I : Type*} [Fintype I] [DecidableEq I] (eI : I ≃ Fin q)

theorem noiseCommon_nonzero
    (a : CStarMatrix I I (Blocks (Sum.elim P.k P.l))) (ha : a ≠ 0)
    (v : Vertex ⊕ Vertex) : D.noiseCommon eI a v ≠ 0 := by
  apply common_nonzero D 2 ((tripleAmplification P eI).common a)
  exact fun h => ha ((tripleAmplification P eI).common.injective
    (h.trans (map_zero _).symm))

theorem noiseLeft_nonzero
    (a : CStarMatrix I I (Blocks (P.k + P.l))) (ha : a ≠ 0)
    (v : Vertex) : D.noiseLeft eI a v ≠ 0 := by
  apply left_nonzero D 2 ((tripleAmplification P eI).left a)
  exact fun h => ha ((tripleAmplification P eI).left.injective
    (h.trans (map_zero _).symm))

theorem noiseRight_nonzero
    (a : CStarMatrix I I (Blocks (P.k + P.A *ᵥ P.l))) (ha : a ≠ 0)
    (v : Vertex) : D.noiseRight eI a v ≠ 0 := by
  apply right_nonzero D 2 ((tripleAmplification P eI).right a)
  exact fun h => ha ((tripleAmplification P eI).right.injective
    (h.trans (map_zero _).symm))

theorem noiseCommon_full
    (a : CStarMatrix I I (Blocks (Sum.elim P.k P.l))) (ha : a ≠ 0)
    (J : TwoSidedIdeal (Blocks (Sum.elim D.next.k D.next.l)))
    (hJ : D.noiseCommon eI a ∈ J) : J = ⊤ :=
  ideal_eq_top_of_blocks _ J hJ (noiseCommon_nonzero D eI a ha)

theorem noiseLeft_full
    (a : CStarMatrix I I (Blocks (P.k + P.l))) (ha : a ≠ 0)
    (J : TwoSidedIdeal (Blocks (D.next.k + D.next.l)))
    (hJ : D.noiseLeft eI a ∈ J) : J = ⊤ :=
  ideal_eq_top_of_blocks _ J hJ (noiseLeft_nonzero D eI a ha)

theorem noiseRight_full
    (a : CStarMatrix I I (Blocks (P.k + P.A *ᵥ P.l))) (ha : a ≠ 0)
    (J : TwoSidedIdeal (Blocks (D.next.k + D.next.A *ᵥ D.next.l)))
    (hJ : D.noiseRight eI a ∈ J) : J = ⊤ :=
  ideal_eq_top_of_blocks _ J hJ (noiseRight_nonzero D eI a ha)
end Lift
end Suzuki.RecursiveNoiseFullness

import Suzuki.GraphCanonicalUnits
import Suzuki.GraphCornerIdentification

/-!
# Graph extension for actual finite-factor homomorphisms

The matrix-unit input in the graph inverse is now constructed from the given
factor homomorphisms. Only the displayed finite P/Q common-entry equations are
assumed. Their diagonal consequences, CK relations, norm generation and inverse
identities are derived. The manuscript's specific common inclusions still have
to supply these entry equations and the forward common-map equality.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace Suzuki.GraphFiniteAmalgam
open GraphRelations WeightedGraphAmalgam GraphAmalgamInverse GraphCornerIdentification
universe u
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {source target : E → V}
  (k l : V → ℕ) (hk : ∀ v, 0 < k v) (hl : ∀ v, 0 < l v)
  {C : Type u} [CStarAlgebra C]
  (f₀ : FirstFactor k l →⋆ₐ[ℂ] C)
  (f₁ : Factor (source := source) (target := target) k l →⋆ₐ[ℂ] C)

abbrev firstUnits := GraphCanonicalUnits.ofHom (coordVertex k l) f₀
abbrev secondUnits := GraphCanonicalUnits.ofHom (indexVertex (source := source) (target := target) k l) f₁

/-- These are exactly finite matrix-entry equations in the actual factor maps,
not assumed graph relations, KK data, or inverse maps. -/
structure CommonEntries : Prop where
  P_entry : ∀ (v : V) (a b : Fin (k v)),
    f₀ (GraphCanonicalUnits.scalarUnit (coordVertex k l) (pCoord k l v a) (pCoord k l v b)) =
    f₁ (GraphCanonicalUnits.scalarUnit (indexVertex (source := source) (target := target) k l)
      (pIndex k l v a) (pIndex k l v b))
  Q_entry : ∀ (w : V) (a b : Fin (l w)),
    f₀ (GraphCanonicalUnits.scalarUnit (coordVertex k l) (qCoord k l w a) (qCoord k l w b)) =
    ∑ e : {e : E // source e = w},
      f₁ (GraphCanonicalUnits.scalarUnit (indexVertex (source := source) (target := target) k l)
        (outIndex k l w a e) (outIndex k l w b e))

variable (h : CommonEntries k l f₀ f₁)
include h in
/-- The full common relations of the inverse construction follow from the
actual finite factor equations; no diagonal relation is added as an input. -/
theorem allCommon : AllCommon k l hk hl (firstUnits k l f₀) (secondUnits k l f₁) where
  P_diag v := h.P_entry v ⟨0, hk v⟩ ⟨0, hk v⟩
  Q_diag w := by
    change f₀ (GraphCanonicalUnits.scalarUnit (coordVertex k l) (qCoord k l w ⟨0, hl w⟩) (qCoord k l w ⟨0, hl w⟩)) = _
    rw [h.Q_entry]
    change (∑ e : {e : E // source e = w},
      (secondUnits k l f₁).unit (outIndex k l w ⟨0, hl w⟩ e) (outIndex k l w ⟨0, hl w⟩ e)) = _
    simp only [outIndex_zero]
    exact (Finset.sum_subtype (Finset.univ.filter (fun e => source e = w))
      (by simp) (fun e => (secondUnits k l f₁).unit (FQ k l hl e) (FQ k l hl e))).symm
  P_all := h.P_entry
  Q_all := h.Q_entry

local instance graphOrder : PartialOrder (GraphUniversal.Algebra.{u} source target) := CStarAlgebra.spectralOrder _
local instance graphOrderedRing : StarOrderedRing (GraphUniversal.Algebra.{u} source target) := CStarAlgebra.spectralOrderedRing _

include h hl in
/-- Actual finite-factor maps with the precise common entry equations extend
uniquely to the completed weighted graph corner. -/
theorem existsUnique_extension (hns : NoSinks source) :
    ∃! φ : graphCorner.{u} (source := source) (target := target) k l →⋆ₐ[ℂ] C,
      φ.comp (firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l) = f₀ ∧
      φ.comp (factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns) = f₁ := by
  have hp := existsUnique_factor_extension k l hk hl (firstUnits k l f₀) (secondUnits k l f₁)
    (allCommon k l hk hl f₀ f₁ h) hns
  simpa only [firstUnits, secondUnits, GraphCanonicalUnits.representation_ofHom] using hp


omit [DecidableEq E] in
/-- Exact coordinate image of a canonical first-factor matrix unit. -/
theorem graph_firstUnit (v : V) (i j : FirstBlockIndex k l v) :
    firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l
      (GraphCanonicalUnits.scalarUnit (coordVertex k l) i.val j.val) =
      firstBlockUnit (graphFamily.{u} (source := source) (target := target)) k l v i j := by
  rw [GraphCanonicalUnits.scalarUnit_single _ v i j, firstFactor_single, one_smul]

/-- Exact coordinate image of a canonical second-factor matrix unit. -/
theorem graph_secondUnit (hns : NoSinks source) (v : V)
    (i j : BlockIndex (source := source) (target := target) k l v) :
    factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns
      (GraphCanonicalUnits.scalarUnit (indexVertex (source := source) (target := target) k l) i.val j.val) =
      blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk v i j := by
  rw [GraphCanonicalUnits.scalarUnit_single _ v i j, secondFactor_single, one_smul]

/-- The constructed graph-corner factor maps themselves satisfy every common
matrix-entry equation, including the complete outgoing sum for Q. -/
theorem graph_commonEntries (hns : NoSinks source) :
    CommonEntries k l
      (firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l)
      (factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns) where
  P_entry v a b := by
    rw [graph_firstUnit (source := source) (target := target) k l v
      ⟨pCoord k l v a, rfl⟩ ⟨pCoord k l v b, rfl⟩,
      graph_secondUnit k l hk hns v ⟨pIndex k l v a, rfl⟩ ⟨pIndex k l v b, rfl⟩]
    apply Subtype.ext
    exact (common_P (graphFamily.{u} (source := source) (target := target)) k l hk v a b).symm
  Q_entry w a b := by
    rw [graph_firstUnit (source := source) (target := target) k l w
      ⟨qCoord k l w a, rfl⟩ ⟨qCoord k l w b, rfl⟩]
    have he (e : {e : E // source e = w}) :
        factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns
          (GraphCanonicalUnits.scalarUnit (indexVertex (source := source) (target := target) k l)
            (outIndex k l w a e) (outIndex k l w b e)) =
        blockUnit (graphFamily.{u} (source := source) (target := target)) k l hk (target e)
          ⟨outIndex k l w a e, rfl⟩ ⟨outIndex k l w b e, rfl⟩ :=
      graph_secondUnit (source := source) (target := target) k l hk hns (target e)
        ⟨outIndex k l w a e, rfl⟩ ⟨outIndex k l w b e, rfl⟩
    simp only [he]
    apply Subtype.ext
    simp only [CommonCorner.coe_sum, firstBlockUnit_coe, blockUnit_coe]
    exact (common_Q_units (graphFamily.{u} (source := source) (target := target)) k l hk hns w a b).symm

section Identification
variable {D P₀ : Type} [CStarAlgebra D] [CStarAlgebra P₀]
  (g₀ : FirstFactor k l →⋆ₐ[ℂ] P₀)
  (g₁ : Factor (source := source) (target := target) k l →⋆ₐ[ℂ] P₀)
  (hg : CommonEntries k l g₀ g₁)
  (i₀ : D →⋆ₐ[ℂ] FirstFactor k l)
  (i₁ : D →⋆ₐ[ℂ] Factor (source := source) (target := target) k l)
  (hP : CStarAmalgam.IsFullAmalgam i₀ i₁ g₀ g₁)
  (hns : NoSinks source)
  (hc : (firstFactorHom (graphFamily.{0} (source := source) (target := target)) k l).comp i₀ =
    (factorHom (graphFamily.{0} (source := source) (target := target)) k l hk hns).comp i₁)

/-- The actual graph/amalgam equivalence with canonical matrix units derived
from g₀ and g₁. The finite input obligations are exactly CommonEntries and hc;
these are not licensed as external published theorems. -/
def identify : P₀ ≃⋆ₐ[ℂ] graphCorner.{0} (source := source) (target := target) k l :=
  GraphCornerIdentification.amalgamEquivCorner k l hk hl (firstUnits k l g₀) (secondUnits k l g₁)
    (allCommon k l hk hl g₀ g₁ hg) i₀ i₁
    (by simpa only [firstUnits, secondUnits, GraphCanonicalUnits.representation_ofHom] using hP) hns hc

end Identification
end Suzuki.GraphFiniteAmalgam

import Suzuki.CommonCorner
import Suzuki.FiniteCPApproximation
import Suzuki.CornerFiniteness
import Suzuki.CornerSimplicity

/-!
# Completely positive approximation for projection corners

Compression into the concrete projection corner is proved completely positive
at every matrix level and contractive in the inherited norm. Composing with
the nonunital inclusion transfers the exact target CP approximation property.
-/

noncomputable section

namespace Suzuki.CornerCPApproximation

open CommonCorner FiniteCPApproximation
open scoped CStarAlgebra ComplexOrder

section Reflection

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [PartialOrder B] [StarOrderedRing A] [StarOrderedRing B]

/-- Positivity is reflected by an actual injective nonunital star homomorphism.
Unitization reduces the assertion to the unital spectral theorem. -/
theorem nonneg_of_injective_nonunital (f : A →⋆ₙₐ[ℂ] B) (hf : Function.Injective f)
    {a : A} (ha : 0 ≤ f a) : 0 ≤ a := by
  let : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing _
  let : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
  apply Unitization.inr_nonneg_iff.mp
  apply nonneg_of_injective_hom (Unitization.starMap f) (Unitization.starMap_injective hf)
  simpa only [Unitization.starMap_inr] using
    (Unitization.inr_nonneg_iff.mpr ha : 0 ≤ (Unitization.inr (f a) : Unitization ℂ B))

end Reflection

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {p : A} (hp : IsStarProjection p)

/-- The actual nonunital inclusion of the corner, regarded as a CP map. -/
def inclusionCP : Corner hp →CP A :=
  CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (inclusion hp)

/-- Compression by a projection is completely positive into its own corner. -/
def compressionCP : A →CP Corner hp where
  toLinearMap := compress hp
  map_cstarMatrix_nonneg' k M hM := by
    let f := CStarMatrix.mapₙₐ (inclusion hp) (n := Fin k)
    have hf : Function.Injective f := by
      intro a b h
      ext i j
      exact congrArg (fun m : CStarMatrix (Fin k) (Fin k) A => m i j) h
    apply nonneg_of_injective_nonunital f hf
    let d := CStarMatrix.ofMatrix (Matrix.diagonal fun _ : Fin k => p)
    have hd := star_left_conjugate_nonneg hM d
    convert hd using 1
    ext i j
    change p * M i j * p = (star d * M * d) i j
    rw [amplified_conjugation_entry, hp.isSelfAdjoint.star_eq]

@[simp] theorem inclusionCP_apply (a : Corner hp) : inclusionCP hp a = (a : A) := rfl

@[simp] theorem compressionCP_apply (a : A) : compressionCP hp a = compress hp a := rfl

/-- Compression is a contraction, including the zero-projection case. -/
theorem compression_contractive (a : A) : ‖compressionCP hp a‖ ≤ ‖a‖ := by
  change ‖p * a * p‖ ≤ ‖a‖
  have hpbound : ‖p‖ ≤ 1 := hp.norm_le p
  calc
    _ ≤ ‖p * a‖ * ‖p‖ := norm_mul_le _ _
    _ ≤ (‖p‖ * ‖a‖) * ‖p‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖a‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hpbound (norm_nonneg _)) hpbound (norm_nonneg _)
      (by positivity)
    _ = ‖a‖ := by simp

/-- Projection corners inherit the exact finite-matrix CP approximation
property used in the target statement. -/
theorem hasCPApproximation (B : Target.UnitalAlgebra) (hB : Target.HasCPApproximation B)
    {q : B} (hq : IsStarProjection q) :
    Target.HasCPApproximation ⟨Corner hq, inferInstance⟩ := by
  classical
  intro s ε hε
  obtain ⟨n, hn, φ, ψ, hφ, hψ, happ⟩ := hB (s.image (inclusion hq)) ε hε
  refine ⟨n, hn, cpComp φ (inclusionCP hq), cpComp (compressionCP hq) ψ, ?_, ?_, ?_⟩
  · intro a
    exact hφ (a : B)
  · intro m
    exact (compression_contractive hq (ψ m)).trans (hψ m)
  · intro a ha
    have h := happ (a : B) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    change ‖compress hq (ψ (φ (a : B))) - a‖ < ε
    calc
      _ = ‖compress hq (ψ (φ (a : B)) - (a : B))‖ := by
        rw [map_sub, compress_coe]
      _ ≤ ‖ψ (φ (a : B)) - (a : B)‖ := compression_contractive hq _
      _ < ε := h

/-- Every nonzero projection corner of a finite constituent has all four
properties required by the exact target statement. -/
theorem isFiniteConstituent (B : Target.UnitalAlgebra) (hB : Target.IsFiniteConstituent B)
    {q : B} (hq : IsStarProjection q) (hne : q ≠ 0) :
    Target.IsFiniteConstituent ⟨Corner hq, inferInstance⟩ := by
  let : TopologicalSpace.SeparableSpace B := hB.1
  exact ⟨CornerFiniteness.corner_separable hq,
    hasCPApproximation B hB.2.1 hq,
    CornerSimplicity.isSimple B hB.2.2.1 hq hne,
    CornerFiniteness.corner_stablyFinite_of hq hB.2.2.2⟩

end Suzuki.CornerCPApproximation

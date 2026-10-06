import Suzuki.Target
import Mathlib.Data.Matrix.Block

/-!
# Concrete completely positive approximation foundations

The completely positive maps in this file use the actual matrix order and
C⋆-norm. `HasCPApproximation` is precisely the proposition in `Suzuki.Target`.
The finite-product theorem uses block-diagonal inclusion and principal-block
compression, with complete positivity, norm bounds, and retraction proved here.
It also covers empty products and zero-size blocks. CP approximation is preserved
by actual star equivalences and by completely positive contractive retracts.

This proves the finite-stage CP approximation ingredient only. It does not prove
CP approximation for inductive limits, classify finite-dimensional C⋆-algebras,
or prove `Target.MainClaim`. No nuclearity classification or unproved positivity
convention is assumed.
-/

noncomputable section

namespace Suzuki.FiniteCPApproximation

open scoped CStarAlgebra ComplexOrder Matrix

universe u

section CPMaps

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable [PartialOrder A] [PartialOrder B] [PartialOrder C]
variable [StarOrderedRing A] [StarOrderedRing B] [StarOrderedRing C]

/-- Composition of genuine completely positive maps. -/
def cpComp (g : B →CP C) (f : A →CP B) : A →CP C where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    have h := g.map_cstarMatrix_nonneg (M.map f) (f.map_cstarMatrix_nonneg M hM)
    convert h using 1
    ext i j
    rfl

@[simp] theorem cpComp_apply (g : B →CP C) (f : A →CP B) (a : A) :
    cpComp g f a = g (f a) := rfl

/-- Star homomorphisms are used as CP maps via Mathlib's theorem proving
positivity at every matrix level. -/
def homCP (f : A →⋆ₐ[ℂ] B) : A →CP B :=
  CompletelyPositiveMapClass.toCompletelyPositiveLinearMap f

@[simp] theorem homCP_apply (f : A →⋆ₐ[ℂ] B) (a : A) : homCP f a = f a := rfl

/-- Positivity is reflected by an injective unital star homomorphism. -/
theorem nonneg_of_injective_hom (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f)
    {a : A} (ha : 0 ≤ f a) : 0 ≤ a := by
  have hself : IsSelfAdjoint a := by
    apply hf
    simpa only [map_star] using (IsSelfAdjoint.of_nonneg ha).star_eq
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) a hself).mpr
  intro t ht
  apply spectrum_nonneg_of_nonneg ha
  rwa [hself.map_spectrum_real f hf]

/-- Entrywise amplification of an actual star homomorphism. -/
def amplifyHom (k : ℕ) (f : A →⋆ₐ[ℂ] B) :
    CStarMatrix (Fin k) (Fin k) A →⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) B where
  __ := CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom
  map_one' := Matrix.map_one _ (map_zero f) (map_one f)
  commutes' z := by
    ext i j
    change f (if i = j then algebraMap ℂ A z else 0) =
      if i = j then algebraMap ℂ B z else 0
    split_ifs
    · exact f.commutes z
    · exact map_zero f

omit [PartialOrder A] [PartialOrder B] [StarOrderedRing A] [StarOrderedRing B] in
theorem amplifyHom_injective (k : ℕ) (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f) :
    Function.Injective (amplifyHom k f) := by
  intro M N h
  ext i j
  apply hf
  exact congrArg (fun L : CStarMatrix (Fin k) (Fin k) B => L i j) h

omit [PartialOrder A] [StarOrderedRing A] in
/-- Diagonal matrices implement the amplification of conjugation. -/
theorem amplified_conjugation_entry (k : ℕ) (c : A)
    (M : CStarMatrix (Fin k) (Fin k) A) (r s : Fin k) :
    (star (CStarMatrix.ofMatrix (Matrix.diagonal fun _ : Fin k => c)) * M *
      CStarMatrix.ofMatrix (Matrix.diagonal fun _ : Fin k => c)) r s =
      star c * M r s * c := by
  change ((Matrix.diagonal (fun _ : Fin k => c))ᴴ *
    CStarMatrix.ofMatrix.symm M * Matrix.diagonal (fun _ : Fin k => c)) r s = _
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem matrix_sum_entry {η : Type*} [Fintype η] (k : ℕ)
    (f : η → CStarMatrix (Fin k) (Fin k) A) (r s : Fin k) :
    (∑ i, f i) r s = ∑ i, f i r s := by
  let ev : CStarMatrix (Fin k) (Fin k) A →+ A :=
    { toFun := fun M => M r s, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum ev f Finset.univ

/-- The actual zero linear map is completely positive. -/
def cpZero : A →CP B where
  toLinearMap := 0
  map_cstarMatrix_nonneg' k M _ := by
    have hz : M.map (0 : A →ₗ[ℂ] B) = 0 := by ext i j; rfl
    rw [hz]

@[simp] theorem cpZero_apply (a : A) : cpZero (B := B) a = 0 := rfl

end CPMaps

/-- CP approximation is preserved by an actual complex star algebra equivalence.
Both norm bounds follow from C⋆-isometry of the equivalence. -/
theorem hasCPApproximation_of_equiv (A B : Target.UnitalAlgebra.{u})
    (e : A ≃⋆ₐ[ℂ] B) (hA : Target.HasCPApproximation A) :
    Target.HasCPApproximation B := by
  classical
  intro s ε hε
  obtain ⟨n, hn, φ, ψ, hφ, hψ, happrox⟩ := hA (s.image e.symm) ε hε
  refine ⟨n, hn, cpComp φ (homCP e.symm.toStarAlgHom),
    cpComp (homCP e.toStarAlgHom) ψ, ?_, ?_, ?_⟩
  · intro b
    change ‖φ (e.symm b)‖ ≤ ‖b‖
    exact (hφ (e.symm b)).trans_eq (NonUnitalStarAlgHom.norm_map e.symm e.symm.injective b)
  · intro m
    change ‖e (ψ m)‖ ≤ ‖m‖
    rw [NonUnitalStarAlgHom.norm_map e e.injective]
    exact hψ m
  · intro b hb
    have ha := happrox (e.symm b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    change ‖e (ψ (φ (e.symm b))) - b‖ < ε
    rw [← e.apply_symm_apply b, ← map_sub, NonUnitalStarAlgHom.norm_map e e.injective]
    simpa only [e.symm_apply_apply] using ha

theorem hasCPApproximation_iff_of_equiv (A B : Target.UnitalAlgebra.{u})
    (e : A ≃⋆ₐ[ℂ] B) : Target.HasCPApproximation A ↔ Target.HasCPApproximation B :=
  ⟨hasCPApproximation_of_equiv A B e, hasCPApproximation_of_equiv B A e.symm⟩

/-- An actual completely positive contractive retract inherits CP approximation. -/
theorem hasCPApproximation_of_retract (A B : Target.UnitalAlgebra.{u})
    (i : A →CP B) (r : B →CP A) (hi : ∀ a, ‖i a‖ ≤ ‖a‖)
    (hr : ∀ b, ‖r b‖ ≤ ‖b‖) (hri : ∀ a, r (i a) = a)
    (hB : Target.HasCPApproximation B) : Target.HasCPApproximation A := by
  classical
  intro s ε hε
  obtain ⟨n, hn, φ, ψ, hφ, hψ, happrox⟩ := hB (s.image i) ε hε
  refine ⟨n, hn, cpComp φ i, cpComp r ψ, ?_, ?_, ?_⟩
  · intro a
    exact (hφ (i a)).trans (hi a)
  · intro m
    exact (hr (ψ m)).trans (hψ m)
  · intro a ha
    have h := happrox (i a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    have hb := hr (ψ (φ (i a)) - i a)
    rw [map_sub, hri] at hb
    exact hb.trans_lt h

/-- The zero algebra is covered too: use zero maps through the one-by-one
complex matrices. -/
theorem hasCPApproximation_of_subsingleton (A : Target.UnitalAlgebra)
    [Subsingleton A] : Target.HasCPApproximation A := by
  intro s ε hε
  refine ⟨1, Nat.zero_lt_one, cpZero, cpZero, ?_, ?_, ?_⟩
  · intro a
    simp only [cpZero_apply, norm_zero]
    exact norm_nonneg a
  · intro M
    simp only [cpZero_apply, norm_zero]
    exact norm_nonneg M
  · intro a _
    have ha : a = 0 := Subsingleton.elim _ _
    simpa only [cpZero_apply, ha, sub_self, norm_zero] using hε

/-- A complex full matrix algebra, with its actual C⋆-norm. -/
def matrixAlgebra (n : ℕ) : Target.UnitalAlgebra where
  Carrier := CStarMatrix (Fin n) (Fin n) ℂ
  algebra := inferInstance

/-- A nonzero-size full matrix algebra has an exact CP approximation through
itself. Both maps are the identity and are completely positive contractions. -/
theorem matrix_hasCPApproximation (n : ℕ) (hn : 0 < n) :
    Target.HasCPApproximation (matrixAlgebra n) := by
  intro s ε hε
  refine ⟨n, hn, homCP (StarAlgHom.id ℂ _), homCP (StarAlgHom.id ℂ _), ?_, ?_, ?_⟩
  · intro a
    exact le_rfl
  · intro a
    exact le_rfl
  · intro a _
    change ‖a - a‖ < ε
    simpa only [sub_self, norm_zero] using hε

section BlockMatrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ)
abbrev Blocks := ∀ i, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ
abbrev TotalMatrix := CStarMatrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℂ

/-- The concrete block-diagonal inclusion, for blocks of varying sizes. -/
def blockInclusion : Blocks n →⋆ₐ[ℂ] TotalMatrix n where
  toFun a := CStarMatrix.ofMatrix (Matrix.blockDiagonal' fun i =>
    CStarMatrix.ofMatrix.symm (a i))
  map_zero' := Matrix.blockDiagonal'_zero
  map_one' := Matrix.blockDiagonal'_one
  map_add' a b := Matrix.blockDiagonal'_add _ _
  map_mul' a b := congrArg CStarMatrix.ofMatrix (Matrix.blockDiagonal'_mul
    (fun i => CStarMatrix.ofMatrix.symm (a i)) (fun i => CStarMatrix.ofMatrix.symm (b i)))
  commutes' z := by
    change Matrix.blockDiagonal' (fun i => Matrix.scalar (Fin (n i)) z) =
      Matrix.scalar (Σ i, Fin (n i)) z
    exact Matrix.blockDiagonal'_diagonal _
  map_star' a := (Matrix.blockDiagonal'_conjTranspose _).symm

/-- Principal diagonal blocks, bundled as a complex linear map. -/
def blockCompression : TotalMatrix n →ₗ[ℂ] Blocks n where
  toFun M i := CStarMatrix.ofMatrix fun r s => M ⟨i, r⟩ ⟨i, s⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem blockCompression_inclusion (a : Blocks n) :
    blockCompression n (blockInclusion n a) = a := by
  funext i
  ext r s
  exact Matrix.blockDiagonal'_apply_eq (fun j => CStarMatrix.ofMatrix.symm (a j)) i r s

theorem blockInclusion_injective : Function.Injective (blockInclusion n) :=
  Function.LeftInverse.injective (blockCompression_inclusion n)

theorem blockInclusion_norm (a : Blocks n) : ‖blockInclusion n a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (blockInclusion n) (blockInclusion_injective n) a

/-- The projection onto the rows and columns of one block. -/
def blockProjection (i : ι) : TotalMatrix n :=
  CStarMatrix.ofMatrix (Matrix.diagonal fun r => if r.1 = i then 1 else 0)

theorem blockProjection_isProjection (i : ι) : IsStarProjection (blockProjection n i) := by
  constructor
  · change CStarMatrix.ofMatrix
      ((Matrix.diagonal fun r : Σ j, Fin (n j) => if r.1 = i then (1 : ℂ) else 0) *
        Matrix.diagonal fun r : Σ j, Fin (n j) => if r.1 = i then (1 : ℂ) else 0) =
      CStarMatrix.ofMatrix (Matrix.diagonal fun r : Σ j, Fin (n j) => if r.1 = i then (1 : ℂ) else 0)
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg CStarMatrix.ofMatrix
    apply congrArg Matrix.diagonal
    funext r
    split_ifs <;> simp_all
  · change (Matrix.diagonal fun r : Σ j, Fin (n j) => if r.1 = i then (1 : ℂ) else 0)ᴴ =
      Matrix.diagonal (fun r : Σ j, Fin (n j) => if r.1 = i then (1 : ℂ) else 0)
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext r
    split_ifs <;> simp_all

/-- A single supported block agrees with compression by its diagonal projection. -/
theorem singleBlock_eq_compression (i : ι) (M : TotalMatrix n) :
    blockInclusion n (Pi.single i (blockCompression n M i)) =
      blockProjection n i * M * blockProjection n i := by
  ext ⟨j, r⟩ ⟨k, s⟩
  change Matrix.blockDiagonal' (fun l => CStarMatrix.ofMatrix.symm
    ((Pi.single i (blockCompression n M i) : Blocks n) l)) ⟨j, r⟩ ⟨k, s⟩ =
    ((Matrix.diagonal (fun t : Σ l, Fin (n l) => if t.1 = i then (1 : ℂ) else 0) *
      CStarMatrix.ofMatrix.symm M) *
      Matrix.diagonal (fun t : Σ l, Fin (n l) => if t.1 = i then (1 : ℂ) else 0)) ⟨j, r⟩ ⟨k, s⟩
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i
    · subst k
      simp only [Matrix.blockDiagonal'_apply_eq, Pi.single_eq_same, ite_true,
        one_mul, mul_one]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hki)]
      simp [hki]
  · by_cases hjk : j = k
    · subst k
      simp [Matrix.blockDiagonal'_apply_eq, hji]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hjk]
      simp [hji]

theorem blockCompression_contract (M : TotalMatrix n) :
    ‖blockCompression n M‖ ≤ ‖M‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg M)).mpr
  intro i
  have hnorm : ‖(Pi.single i (blockCompression n M i) : Blocks n)‖ = ‖blockCompression n M i‖ :=
    Pi.norm_single _
  rw [← hnorm, ← blockInclusion_norm n, singleBlock_eq_compression]
  calc
    ‖blockProjection n i * M * blockProjection n i‖ ≤
      ‖blockProjection n i‖ * ‖M‖ * ‖blockProjection n i‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖M‖ * 1 := by
      gcongr <;> exact IsStarProjection.norm_le _ (blockProjection_isProjection n i)
    _ = ‖M‖ := by simp

/-- Pinching is exactly the sum of the supported block compressions. -/
theorem blockPinching (M : TotalMatrix n) :
    blockInclusion n (blockCompression n M) =
      ∑ i, blockProjection n i * M * blockProjection n i := by
  simp_rw [← singleBlock_eq_compression]
  rw [← map_sum]
  congr 1
  exact (Finset.univ_sum_single (blockCompression n M)).symm

/-- Principal-block compression is completely positive at every matrix level. -/
def blockCompressionCP [PartialOrder (Blocks n)] [StarOrderedRing (Blocks n)] :
    TotalMatrix n →CP Blocks n where
  toLinearMap := blockCompression n
  map_cstarMatrix_nonneg' k M hM := by
    apply nonneg_of_injective_hom (amplifyHom k (blockInclusion n))
      (amplifyHom_injective k _ (blockInclusion_injective n))
    have hpinch : amplifyHom k (blockInclusion n) (M.map (blockCompression n)) =
        ∑ i, star (CStarMatrix.ofMatrix (Matrix.diagonal fun _ : Fin k => blockProjection n i)) *
          M * CStarMatrix.ofMatrix (Matrix.diagonal fun _ : Fin k => blockProjection n i) := by
      ext r s : 1
      change blockInclusion n (blockCompression n (M r s)) = _
      rw [blockPinching]
      rw [matrix_sum_entry]
      apply Finset.sum_congr rfl
      intro i _
      rw [amplified_conjugation_entry, (blockProjection_isProjection n i).isSelfAdjoint.star_eq]
    rw [hpinch]
    exact Finset.sum_nonneg fun i _ => star_left_conjugate_nonneg hM _

/-- The genuine finite product of complex full matrix algebras. -/
def blocksAlgebra : Target.UnitalAlgebra where
  Carrier := Blocks n
  algebra := inferInstance

set_option maxHeartbeats 600000 in
/-- Every finite product with positive total dimension admits an exact CP
approximation through one full complex matrix algebra. The inclusion is block
diagonal and the return map is principal-block compression. -/
theorem blocks_hasCPApproximation (hn : 0 < Fintype.card (Σ i, Fin (n i))) :
    Target.HasCPApproximation (blocksAlgebra n) := by
  let : PartialOrder (Blocks n) := CStarAlgebra.spectralOrder (Blocks n)
  let : StarOrderedRing (Blocks n) := CStarAlgebra.spectralOrderedRing (Blocks n)
  let e : TotalMatrix n ≃⋆ₐ[ℂ]
      CStarMatrix (Fin (Fintype.card (Σ i, Fin (n i))))
        (Fin (Fintype.card (Σ i, Fin (n i)))) ℂ :=
    CStarMatrix.reindexₐ ℂ ℂ (Fintype.equivFin (Σ i, Fin (n i)))
  intro s ε hε
  refine ⟨Fintype.card (Σ i, Fin (n i)), hn,
    cpComp (homCP e.toStarAlgHom) (homCP (blockInclusion n)),
    cpComp (blockCompressionCP n) (homCP e.symm.toStarAlgHom), ?_, ?_, ?_⟩
  · intro a
    change ‖e (blockInclusion n a)‖ ≤ ‖a‖
    rw [NonUnitalStarAlgHom.norm_map e e.injective]
    exact le_of_eq (blockInclusion_norm n a)
  · intro M
    change ‖blockCompression n (e.symm M)‖ ≤ ‖M‖
    exact (blockCompression_contract n _).trans_eq
      (NonUnitalStarAlgHom.norm_map e.symm e.symm.injective M)
  · intro a _
    change ‖blockCompression n (e.symm (e (blockInclusion n a))) - (show Blocks n from a)‖ < ε
    rw [e.symm_apply_apply, blockCompression_inclusion n (show Blocks n from a),
      sub_self, norm_zero]
    exact hε

/-- Every finite product of full complex matrix algebras has the exact target
CP approximation property, including empty products and zero-size blocks. -/
theorem finiteProduct_hasCPApproximation : Target.HasCPApproximation (blocksAlgebra n) := by
  classical
  by_cases hn : 0 < Fintype.card (Σ i, Fin (n i))
  · exact blocks_hasCPApproximation n hn
  · have hzero : Fintype.card (Σ i, Fin (n i)) = 0 := Nat.eq_zero_of_not_pos hn
    let : IsEmpty (Σ i, Fin (n i)) := Fintype.card_eq_zero_iff.mp hzero
    have : Subsingleton (blocksAlgebra n) := ⟨by
      intro a b
      funext i
      apply CStarMatrix.ext
      intro r _
      exact isEmptyElim (⟨i, r⟩ : Σ j, Fin (n j))⟩
    exact hasCPApproximation_of_subsingleton (blocksAlgebra n)

end BlockMatrices

end Suzuki.FiniteCPApproximation

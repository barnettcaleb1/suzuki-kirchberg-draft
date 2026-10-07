import Suzuki.MatrixRetractions
import Suzuki.RFDAmplification

/-!
# Matrix amplification of completely positive approximation

All matrix norms here are the actual C⋆ operator norms. Complete positivity and
amplified norm bounds are proved explicitly; no complete-contractivity or
nuclearity classification axiom is assumed. The file proves the exact target
CP approximation property for every finite matrix algebra and every finite
product of matrix algebras over a coefficient algebra with that property.
Zero-size blocks and empty products are included. The finite block index type
in the final product theorem is in universe zero.

This is a permanence theorem. CPAP of the manuscript's coefficient algebra,
its graph tensor stages, and the full `Target.MainClaim` are not proved here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Suzuki.MatrixCPApproximation

open FiniteCPApproximation
open scoped CStarAlgebra ComplexOrder Matrix

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [PartialOrder A] [PartialOrder B] [StarOrderedRing A] [StarOrderedRing B]

/-- Flatten nested matrices over an arbitrary C⋆ coefficient algebra. -/
def flatten (k m : Type*) [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]
    (A : Type*) [CStarAlgebra A] :
    CStarMatrix k k (CStarMatrix m m A) ≃⋆ₐ[ℂ] CStarMatrix (k × m) (k × m) A where
  __ := Matrix.compRingEquiv k m A
  map_star' _ := rfl
  map_smul' _ _ := rfl

/-- Entrywise amplification is genuinely completely positive, by flattening
both matrix levels and applying the original CP property. -/
def amplify (k : Type*) [Fintype k] [DecidableEq k] (φ : A →CP B) :
    CStarMatrix k k A →CP CStarMatrix k k B where
  toLinearMap := CStarMatrix.mapₗ φ.toLinearMap
  map_cstarMatrix_nonneg' m M hM := by
    have h := φ.map_cstarMatrix_nonneg (flatten (Fin m) k A M)
      (map_nonneg (flatten (Fin m) k A) hM)
    convert map_nonneg (flatten (Fin m) k B).symm h using 1
    ext i j r s
    rfl

@[simp] theorem amplify_apply (k : Type*) [Fintype k] [DecidableEq k]
    (φ : A →CP B) (M : CStarMatrix k k A) (i j : k) : amplify k φ M i j = φ (M i j) := rfl

/-- The positive two-by-two Gram matrix associated to an arbitrary element. -/
def gram (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix ![![star a * a, star a], ![a, 1]]

theorem gram_nonneg (a : A) : 0 ≤ gram a := by
  let X : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix ![![a, 1], ![0, 0]]
  have h := star_mul_self_nonneg X
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, X, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]

/-- Complete positivity implies preservation of the adjoint. -/
theorem cp_map_star (φ : A →CP B) (a : A) : φ (star a) = star (φ a) := by
  have h := IsSelfAdjoint.of_nonneg (φ.map_cstarMatrix_nonneg (gram a) (gram_nonneg a))
  have he := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) B => M 0 1) h.star_eq
  exact he.symm

/-- Schwarz inequality for an actual completely positive subunital map.
The proof uses its positive two-by-two Gram matrix and an explicit compression. -/
theorem schwarz (φ : A →CP B) (hφ : φ 1 ≤ 1) (a : A) :
    star (φ a) * φ a ≤ φ (star a * a) := by
  let Y := (gram a).map φ + MatrixRetractions.singleHom (n := Fin 2) 1 (1 - φ 1)
  have hY : 0 ≤ Y := add_nonneg
    (φ.map_cstarMatrix_nonneg (gram a) (gram_nonneg a))
    (map_nonneg (MatrixRetractions.singleHom (n := Fin 2) 1) (sub_nonneg.mpr hφ))
  let K : CStarMatrix (Fin 2) (Fin 2) B := CStarMatrix.ofMatrix ![![1, 0], ![-φ a, 0]]
  have h := map_nonneg (MatrixRetractions.entryCP (A := B) (0 : Fin 2))
    (star_left_conjugate_nonneg hY K)
  have he : MatrixRetractions.entryCP (0 : Fin 2) (star K * Y * K) =
      φ (star a * a) - star (φ a) * φ a := by
    rw [MatrixRetractions.entryCP_apply]
    simp [Y, K, gram, MatrixRetractions.singleHom, CStarMatrix.mul_apply,
      CStarMatrix.star_apply, Fin.sum_univ_two, cp_map_star]
    noncomm_ring
  rw [he] at h
  exact sub_nonneg.mp h

/-- A CP map whose value at one has norm at most one is contractive. -/
theorem contractive_of_norm_one (φ : A →CP B) (hφ : ‖φ 1‖ ≤ 1) (a : A) :
    ‖φ a‖ ≤ ‖a‖ := by
  have hpos : 0 ≤ φ 1 := map_nonneg φ zero_le_one
  have hsub : φ 1 ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hφ
  have hs := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (star_mul_self_nonneg (φ a)) (schwarz φ hsub a)
  have hb := PositiveLinearMap.norm_apply_le_of_nonneg
    (PositiveLinearMap.ofClass φ) (star a * a) (star_mul_self_nonneg a)
  have hbound := hs.trans (hb.trans (mul_le_mul_of_nonneg_right hφ (norm_nonneg (star a * a))))
  simp only [one_mul, CStarRing.norm_star_mul_self] at hbound
  nlinarith [norm_nonneg (φ a), norm_nonneg a]

/-- The value of an amplified map at one is the diagonal of its value at one. -/
theorem amplify_one (k : Type) [Fintype k] [DecidableEq k] (φ : A →CP B) :
    amplify k φ 1 = MatrixRetractions.diagonalHom (n := k) (φ 1) := by
  ext i j
  change φ (if i = j then 1 else 0) = if i = j then φ 1 else 0
  split_ifs <;> simp

/-- Complete contractivity is a theorem: every matrix amplification of an actual
CP contraction is contractive in the C⋆ matrix norm. -/
theorem amplify_contractive (k : Type) [Fintype k] [DecidableEq k]
    (φ : A →CP B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (M : CStarMatrix k k A) :
    ‖amplify k φ M‖ ≤ ‖M‖ := by
  apply contractive_of_norm_one
  rw [amplify_one]
  exact (NonUnitalStarAlgHom.norm_apply_le (MatrixRetractions.diagonalHom (n := k)) (φ 1)).trans
    ((hφ 1).trans (IsStarProjection.norm_le (1 : A) (IsStarProjection.one A)))


open CStarMatrix WithCStarModule in
/-- A finite entry sum bounds the genuine C⋆ matrix norm. This is an upper
estimate for that norm, not an alternative definition of the matrix norm. -/
theorem norm_le_sum_entries {k : Type*} [Fintype k] (M : CStarMatrix k k A) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [norm_def]
  refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [toCLM_apply_eq_sum, Finset.sum_mul]
  apply pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v j

/-- The actual full matrix algebra over a bundled coefficient algebra. -/
def matrixAlgebra (A : Target.UnitalAlgebra) (n : ℕ) : Target.UnitalAlgebra where
  Carrier := CStarMatrix (Fin n) (Fin n) A
  algebra := inferInstance

/-- CP approximation passes to each positive-size matrix algebra by genuine
entrywise CPC amplification and an isometric flattening to one complex matrix. -/
theorem matrix_hasCPApproximation_pos (A : Target.UnitalAlgebra)
    (hA : Target.HasCPApproximation A) (n : ℕ) (hn : 0 < n) :
    Target.HasCPApproximation (matrixAlgebra A n) := by
  classical
  intro s ε hε
  let C : ℝ := (n : ℝ) * n + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ε / C
  have hδ : 0 < δ := div_pos hε hC
  let t : Finset A := s.biUnion fun M => Finset.univ.biUnion fun i : Fin n =>
    Finset.univ.image fun j : Fin n => M i j
  have hmem (M : matrixAlgebra A n) (hM : M ∈ s) (i j : Fin n) : M i j ∈ t :=
    Finset.mem_biUnion.mpr ⟨M, hM, Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩⟩
  obtain ⟨m, hm, φ, ψ, hφ, hψ, happ⟩ := hA t δ hδ
  let e := (RFDAmplification.flatten (Fin n) (Fin m)).trans
    (CStarMatrix.reindexₐ ℂ ℂ finProdFinEquiv)
  refine ⟨n * m, Nat.mul_pos hn hm,
    cpComp (homCP e.toStarAlgHom) (amplify (Fin n) φ),
    cpComp (amplify (Fin n) ψ) (homCP e.symm.toStarAlgHom), ?_, ?_, ?_⟩
  · intro M
    change ‖e (amplify (Fin n) φ M)‖ ≤ ‖M‖
    rw [NonUnitalStarAlgHom.norm_map e e.injective]
    exact amplify_contractive (Fin n) φ hφ M
  · intro M
    change ‖amplify (Fin n) ψ (e.symm M)‖ ≤ ‖M‖
    exact (amplify_contractive (Fin n) ψ hψ _).trans_eq
      (NonUnitalStarAlgHom.norm_map e.symm e.symm.injective M)
  · intro M hM
    change ‖amplify (Fin n) ψ (e.symm (e (amplify (Fin n) φ M))) -
      (show CStarMatrix (Fin n) (Fin n) A from M)‖ < ε
    rw [e.symm_apply_apply]
    calc
      _ ≤ ∑ j : Fin n, ∑ i : Fin n, ‖ψ (φ (M i j)) - M i j‖ := norm_le_sum_entries _
      _ ≤ ∑ _j : Fin n, ∑ _i : Fin n, δ := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro i _
        exact (happ (M i j) (hmem M hM i j)).le
      _ = (n : ℝ) * n * δ := by simp [mul_assoc]
      _ < ε := by
        have he : δ * C = ε := div_mul_cancel₀ ε (ne_of_gt hC)
        dsimp [C] at he
        nlinarith

/-- Every finite matrix algebra over a coefficient algebra with target CPAP
has target CPAP, including the zero-size algebra. -/
theorem matrix_hasCPApproximation (A : Target.UnitalAlgebra)
    (hA : Target.HasCPApproximation A) (n : ℕ) :
    Target.HasCPApproximation (matrixAlgebra A n) := by
  cases n with
  | zero =>
    have : Subsingleton (matrixAlgebra A 0) := ⟨by
      intro M N
      apply CStarMatrix.ext
      intro i
      exact i.elim0⟩
    exact hasCPApproximation_of_subsingleton _
  | succ n => exact matrix_hasCPApproximation_pos A hA (n + 1) (Nat.succ_pos n)

namespace CoefficientBlocks

variable (A)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ)
abbrev Blocks := ∀ i, CStarMatrix (Fin (n i)) (Fin (n i)) A
abbrev TotalMatrix := CStarMatrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) A

/-- The concrete block-diagonal inclusion, for blocks of varying sizes. -/
def blockInclusion : Blocks A n →⋆ₐ[ℂ] TotalMatrix A n where
  toFun a := CStarMatrix.ofMatrix (Matrix.blockDiagonal' fun i =>
    CStarMatrix.ofMatrix.symm (a i))
  map_zero' := Matrix.blockDiagonal'_zero
  map_one' := Matrix.blockDiagonal'_one
  map_add' a b := Matrix.blockDiagonal'_add _ _
  map_mul' a b := congrArg CStarMatrix.ofMatrix (Matrix.blockDiagonal'_mul
    (fun i => CStarMatrix.ofMatrix.symm (a i)) (fun i => CStarMatrix.ofMatrix.symm (b i)))
  commutes' z := by
    change Matrix.blockDiagonal' (fun i => Matrix.scalar (Fin (n i)) (algebraMap ℂ A z)) =
      Matrix.scalar (Σ i, Fin (n i)) (algebraMap ℂ A z)
    exact Matrix.blockDiagonal'_diagonal _
  map_star' a := (Matrix.blockDiagonal'_conjTranspose _).symm

/-- Principal diagonal blocks, bundled as a complex linear map. -/
def blockCompression : TotalMatrix A n →ₗ[ℂ] Blocks A n where
  toFun M i := CStarMatrix.ofMatrix fun r s => M ⟨i, r⟩ ⟨i, s⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem blockCompression_inclusion (a : Blocks A n) :
    blockCompression A n (blockInclusion A n a) = a := by
  funext i
  ext r s
  exact Matrix.blockDiagonal'_apply_eq (fun j => CStarMatrix.ofMatrix.symm (a j)) i r s

omit [PartialOrder A] [StarOrderedRing A] in
theorem blockInclusion_injective : Function.Injective (blockInclusion A n) :=
  Function.LeftInverse.injective (blockCompression_inclusion A n)

theorem blockInclusion_norm (a : Blocks A n) : ‖blockInclusion A n a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (blockInclusion A n) (blockInclusion_injective A n) a

/-- The projection onto the rows and columns of one block. -/
def blockProjection (i : ι) : TotalMatrix A n :=
  CStarMatrix.ofMatrix (Matrix.diagonal fun r => if r.1 = i then 1 else 0)

omit [PartialOrder A] [StarOrderedRing A] in
theorem blockProjection_isProjection (i : ι) : IsStarProjection (blockProjection A n i) := by
  constructor
  · change CStarMatrix.ofMatrix
      ((Matrix.diagonal fun r : Σ j, Fin (n j) => if r.1 = i then (1 : A) else 0) *
        Matrix.diagonal fun r : Σ j, Fin (n j) => if r.1 = i then (1 : A) else 0) =
      CStarMatrix.ofMatrix (Matrix.diagonal fun r : Σ j, Fin (n j) => if r.1 = i then (1 : A) else 0)
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg CStarMatrix.ofMatrix
    apply congrArg Matrix.diagonal
    funext r
    split_ifs <;> simp_all
  · change (Matrix.diagonal fun r : Σ j, Fin (n j) => if r.1 = i then (1 : A) else 0)ᴴ =
      Matrix.diagonal (fun r : Σ j, Fin (n j) => if r.1 = i then (1 : A) else 0)
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext r
    split_ifs <;> simp_all

omit [PartialOrder A] [StarOrderedRing A] in
/-- A single supported block agrees with compression by its diagonal projection. -/
theorem singleBlock_eq_compression (i : ι) (M : TotalMatrix A n) :
    blockInclusion A n (Pi.single i (blockCompression A n M i)) =
      blockProjection A n i * M * blockProjection A n i := by
  ext ⟨j, r⟩ ⟨k, s⟩
  change Matrix.blockDiagonal' (fun l => CStarMatrix.ofMatrix.symm
    ((Pi.single i (blockCompression A n M i) : Blocks A n) l)) ⟨j, r⟩ ⟨k, s⟩ =
    ((Matrix.diagonal (fun t : Σ l, Fin (n l) => if t.1 = i then (1 : A) else 0) *
      CStarMatrix.ofMatrix.symm M) *
      Matrix.diagonal (fun t : Σ l, Fin (n l) => if t.1 = i then (1 : A) else 0)) ⟨j, r⟩ ⟨k, s⟩
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

theorem blockCompression_contract (M : TotalMatrix A n) :
    ‖blockCompression A n M‖ ≤ ‖M‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg M)).mpr
  intro i
  have hnorm : ‖(Pi.single i (blockCompression A n M i) : Blocks A n)‖ = ‖blockCompression A n M i‖ :=
    Pi.norm_single _
  rw [← hnorm, ← blockInclusion_norm A n, singleBlock_eq_compression]
  calc
    ‖blockProjection A n i * M * blockProjection A n i‖ ≤
      ‖blockProjection A n i‖ * ‖M‖ * ‖blockProjection A n i‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖M‖ * 1 := by
      gcongr <;> exact IsStarProjection.norm_le _ (blockProjection_isProjection A n i)
    _ = ‖M‖ := by simp

omit [PartialOrder A] [StarOrderedRing A] in
/-- Pinching is exactly the sum of the supported block compressions. -/
theorem blockPinching (M : TotalMatrix A n) :
    blockInclusion A n (blockCompression A n M) =
      ∑ i, blockProjection A n i * M * blockProjection A n i := by
  simp_rw [← singleBlock_eq_compression]
  rw [← map_sum]
  congr 1
  exact (Finset.univ_sum_single (blockCompression A n M)).symm

/-- Principal-block compression is completely positive at every matrix level. -/
def blockCompressionCP [PartialOrder (Blocks A n)] [StarOrderedRing (Blocks A n)] :
    TotalMatrix A n →CP Blocks A n where
  toLinearMap := blockCompression A n
  map_cstarMatrix_nonneg' k M hM := by
    apply nonneg_of_injective_hom (amplifyHom k (blockInclusion A n))
      (amplifyHom_injective k _ (blockInclusion_injective A n))
    have hpinch : amplifyHom k (blockInclusion A n) (M.map (blockCompression A n)) =
        ∑ i, star (CStarMatrix.ofMatrix (Matrix.diagonal fun _ : Fin k => blockProjection A n i)) *
          M * CStarMatrix.ofMatrix (Matrix.diagonal fun _ : Fin k => blockProjection A n i) := by
      ext r s : 1
      change blockInclusion A n (blockCompression A n (M r s)) = _
      rw [blockPinching]
      rw [matrix_sum_entry]
      apply Finset.sum_congr rfl
      intro i _
      rw [amplified_conjugation_entry, (blockProjection_isProjection A n i).isSelfAdjoint.star_eq]
    rw [hpinch]
    exact Finset.sum_nonneg fun i _ => star_left_conjugate_nonneg hM _


/-- The genuine finite product of full matrices over one coefficient algebra. -/
def algebra {ι : Type} [Fintype ι] (n : ι → ℕ) : Target.UnitalAlgebra where
  Carrier := ∀ i, CStarMatrix (Fin (n i)) (Fin (n i)) A
  algebra := inferInstance

end CoefficientBlocks

/-- CP approximation passes to every finite product of matrix algebras over
the coefficient algebra. The block inclusion/compression are actual CPC maps
and an exact retraction; empty products and zero-size blocks are included. -/
theorem finiteProduct_hasCPApproximation (A : Target.UnitalAlgebra)
    (hA : Target.HasCPApproximation A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) : Target.HasCPApproximation (CoefficientBlocks.algebra A n) := by
  let : PartialOrder (CoefficientBlocks.Blocks A n) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CoefficientBlocks.Blocks A n) := CStarAlgebra.spectralOrderedRing _
  let e := CStarMatrix.reindexₐ ℂ A (Fintype.equivFin (Σ i, Fin (n i)))
  apply hasCPApproximation_of_retract (CoefficientBlocks.algebra A n)
    (matrixAlgebra A (Fintype.card (Σ i, Fin (n i))))
    (cpComp (homCP e.toStarAlgHom) (homCP (CoefficientBlocks.blockInclusion A n)))
    (cpComp (CoefficientBlocks.blockCompressionCP A n) (homCP e.symm.toStarAlgHom))
  · intro a
    change ‖e (CoefficientBlocks.blockInclusion A n a)‖ ≤ ‖a‖
    rw [NonUnitalStarAlgHom.norm_map e e.injective]
    exact le_of_eq (CoefficientBlocks.blockInclusion_norm A n a)
  · intro M
    change ‖CoefficientBlocks.blockCompression A n (e.symm M)‖ ≤ ‖M‖
    exact (CoefficientBlocks.blockCompression_contract A n _).trans_eq
      (NonUnitalStarAlgHom.norm_map e.symm e.symm.injective M)
  · intro a
    change CoefficientBlocks.blockCompression A n
      (e.symm (e (CoefficientBlocks.blockInclusion A n a))) = a
    rw [e.symm_apply_apply, CoefficientBlocks.blockCompression_inclusion]
  · exact matrix_hasCPApproximation A hA _

end Suzuki.MatrixCPApproximation

import Suzuki.MatrixDiagrams
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic

/-!
# Lifting maps of the actual integer kernels and cokernels

This file formalizes the simultaneous positive lifting lemma in Section 3
of the proposed Suzuki construction. It does not establish the C*-algebra
claims elsewhere in that manuscript. Kernels and cokernels below are the actual submodules and
quotient modules of multiplication by the displayed integer matrices.
-/

namespace Suzuki.PositiveLifting

open LinearMap Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

/-- The kernel of integer matrix multiplication. -/
abbrev Kernel (B : Matrix n n ℤ) := LinearMap.ker B.mulVecLin

/-- The cokernel of integer matrix multiplication. -/
abbrev Cokernel (B : Matrix n n ℤ) := (n → ℤ) ⧸ LinearMap.range B.mulVecLin

/-- The quotient map to the actual cokernel. -/
abbrev quotient (B : Matrix n n ℤ) : (n → ℤ) →ₗ[ℤ] Cokernel B :=
  (LinearMap.range B.mulVecLin).mkQ

/-- The kernel of an integer endomorphism of a finite free module is a direct
summand. The proof splits the surjection onto its free image. -/
theorem exists_kernel_retraction (b : (n → ℤ) →ₗ[ℤ] (n → ℤ)) :
    ∃ r : (n → ℤ) →ₗ[ℤ] LinearMap.ker b,
      ∀ x : LinearMap.ker b, r x = x := by
  classical
  let basis := (LinearMap.range b).basisOfPid (Pi.basisFun ℤ n)
  let : Module.Free ℤ (LinearMap.range b) := Module.Free.of_basis basis.2
  obtain ⟨s, hs⟩ := Module.projective_lifting_property b.rangeRestrict
    (LinearMap.id : LinearMap.range b →ₗ[ℤ] LinearMap.range b)
    b.surjective_rangeRestrict
  have hs' (x : n → ℤ) : b (s (b.rangeRestrict x)) = b x := by
    exact congrArg Subtype.val (DFunLike.congr_fun hs (b.rangeRestrict x))
  let r₀ := LinearMap.id - s.comp b.rangeRestrict
  have hr₀ (x : n → ℤ) : r₀ x ∈ LinearMap.ker b := by
    change b (x - s (b.rangeRestrict x)) = 0
    rw [map_sub, hs', sub_self]
  refine ⟨r₀.codRestrict (LinearMap.ker b) hr₀, ?_⟩
  intro x
  apply Subtype.ext
  have hx : b.rangeRestrict x = 0 := by
    apply Subtype.ext
    exact x.property
  change x.val - s (b.rangeRestrict x) = x.val
  rw [hx, map_zero, sub_zero]

/-- Arbitrary prescribed cokernel and kernel homomorphisms lift simultaneously
to a chain map of the two free integer presentations. No compatible lifts are
assumed in this theorem. -/
theorem exists_compatible_lifts (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (f₀ : Cokernel B →ₗ[ℤ] Cokernel B')
    (f₁ : Kernel B →ₗ[ℤ] Kernel B') :
    ∃ S H : Matrix m n ℤ,
      S * B = B' * H ∧
      (∀ x, quotient B' (S *ᵥ x) = f₀ (quotient B x)) ∧
      (∀ x : Kernel B, H *ᵥ x.val = (f₁ x).val) := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (quotient B')
    (f₀.comp (quotient B)) (LinearMap.range B'.mulVecLin).mkQ_surjective
  have hs' (x : n → ℤ) : quotient B' (s x) = f₀ (quotient B x) :=
    DFunLike.congr_fun hs x
  have hsb (x : n → ℤ) : s (B.mulVecLin x) ∈ LinearMap.range B'.mulVecLin := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change quotient B' (s (B.mulVecLin x)) = 0
    rw [hs']
    have hx : quotient B (B.mulVecLin x) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
    rw [hx, map_zero]
  let sb := (s.comp B.mulVecLin).codRestrict (LinearMap.range B'.mulVecLin) hsb
  obtain ⟨h, hh⟩ := Module.projective_lifting_property B'.mulVecLin.rangeRestrict sb
    B'.mulVecLin.surjective_rangeRestrict
  have hh' (x : n → ℤ) : B'.mulVecLin (h x) = s (B.mulVecLin x) :=
    congrArg Subtype.val (DFunLike.congr_fun hh x)
  obtain ⟨r, hr⟩ := exists_kernel_retraction B.mulVecLin
  let d : Kernel B →ₗ[ℤ] (m → ℤ) :=
    (Kernel B').subtype.comp f₁ - h.comp (Kernel B).subtype
  have hd (x : Kernel B) : B'.mulVecLin (d x) = 0 := by
    change B'.mulVecLin ((f₁ x).val - h x.val) = 0
    rw [map_sub, (f₁ x).property, hh', x.property, map_zero, sub_zero]
  let h' := h + d.comp r
  have hc : s.comp B.mulVecLin = B'.mulVecLin.comp h' := by
    apply LinearMap.ext
    intro x
    have he : B'.mulVecLin (h' x) = s (B.mulVecLin x) := by
      change B'.mulVecLin (h x + d (r x)) = s (B.mulVecLin x)
      rw [map_add, hh', hd, add_zero]
    exact he.symm
  refine ⟨LinearMap.toMatrix' s, LinearMap.toMatrix' h', ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
      Matrix.toLin'_toMatrix']
    exact hc
  · intro x
    simpa only [LinearMap.toMatrix'_mulVec] using hs' x
  · intro x
    rw [LinearMap.toMatrix'_mulVec]
    change h x.val + d (r x.val) = (f₁ x).val
    rw [hr]
    change h x.val + ((f₁ x).val - h x.val) = (f₁ x).val
    abel

/-- Strict entrywise positivity, rather than positive definiteness. -/
def Positive (M : Matrix m n ℤ) : Prop := ∀ i j, 0 < M i j

/-- Adding one sufficiently large constant homotopy makes both lift matrices
strictly positive. This works even when the source index type is empty. -/
theorem exists_positive_homotopy (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (hB : Positive B) (hB' : Positive B') (S H : Matrix m n ℤ) :
    ∃ W : Matrix m n ℤ, Positive (S + B' * W) ∧ Positive (H + W * B) := by
  classical
  obtain ⟨M, hM⟩ := Finite.exists_le (fun p : m × n => max (-S p.1 p.2) (-H p.1 p.2))
  let t := max 0 M + 1
  have ht : 0 < t := by dsimp [t]; omega
  refine ⟨fun _ _ => t, ?_, ?_⟩
  · intro i j
    have hbound : -S i j < t := by
      have := le_trans (le_max_left (-S i j) (-H i j)) (hM (i, j))
      dsimp [t]; omega
    have hsum : t ≤ ∑ k, B' i k * t := by
      have hd : t ≤ B' i i * t := by have := hB' i i; nlinarith
      exact hd.trans (Finset.single_le_sum (fun k _ => mul_nonneg (le_of_lt (hB' i k)) ht.le)
        (Finset.mem_univ i))
    change 0 < S i j + ∑ k, B' i k * t
    omega
  · intro i j
    have hbound : -H i j < t := by
      have := le_trans (le_max_right (-S i j) (-H i j)) (hM (i, j))
      dsimp [t]; omega
    have hsum : t ≤ ∑ k, t * B k j := by
      have hd : t ≤ t * B j j := by have := hB j j; nlinarith
      exact hd.trans (Finset.single_le_sum (fun k _ => mul_nonneg ht.le (le_of_lt (hB k j)))
        (Finset.mem_univ j))
    change 0 < H i j + ∑ k, t * B k j
    omega

/-- The homotopy preserves the actual cokernel class. -/
theorem homotopy_cokernel (B' : Matrix m m ℤ) (S W : Matrix m n ℤ) (x : n → ℤ) :
    quotient B' ((S + B' * W) *ᵥ x) = quotient B' (S *ᵥ x) := by
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, map_add]
  have h : quotient B' (B' *ᵥ (W *ᵥ x)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨W *ᵥ x, rfl⟩
  rw [h, add_zero]

/-- Arbitrary maps on the actual integer kernels and cokernels admit strictly
positive compatible lift matrices, before the final diagram block adjustment. -/
theorem exists_positive_compatible_lifts (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (hB : Positive B) (hB' : Positive B')
    (f₀ : Cokernel B →ₗ[ℤ] Cokernel B')
    (f₁ : Kernel B →ₗ[ℤ] Kernel B') :
    ∃ S H : Matrix m n ℤ,
      Positive S ∧ Positive H ∧ S * B = B' * H ∧
      (∀ x, quotient B' (S *ᵥ x) = f₀ (quotient B x)) ∧
      (∀ x : Kernel B, H *ᵥ x.val = (f₁ x).val) := by
  obtain ⟨S, H, hc, h₀, h₁⟩ := exists_compatible_lifts B B' f₀ f₁
  obtain ⟨W, hS, hH⟩ := exists_positive_homotopy B B' hB hB' S H
  refine ⟨S + B' * W, H + W * B, hS, hH, ?_, ?_, ?_⟩
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hc]
  · intro x
    rw [homotopy_cokernel, h₀]
  · intro x
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, show B *ᵥ x.val = 0 from x.property]
    simpa using h₁ x

/-- A nonnegative integer matrix of determinant one can have every row sum
larger than any prescribed integer, in every finite dimension at least two.
The construction uses row additions, and also keeps the matrix above the identity. -/
theorem exists_large_unimodular [DecidableEq m] [Nontrivial m] (N : ℤ) :
    ∃ U : Matrix m m ℤ, U.det = 1 ∧
      (∀ i j, (1 : Matrix m m ℤ) i j ≤ U i j) ∧
      (∀ i, N < ∑ j, U i j) := by
  classical
  let c := max 0 N + 1
  have hc : 0 < c := by dsimp [c]; omega
  have build (s : Finset m) : ∃ U : Matrix m m ℤ, U.det = 1 ∧
      (∀ i j, (1 : Matrix m m ℤ) i j ≤ U i j) ∧
      (∀ i ∈ s, N < ∑ j, U i j) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, Matrix.det_one, fun _ _ => le_rfl, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨U, hdet, hU, hrows⟩ := ih
      obtain ⟨j, hji⟩ := exists_ne i
      have hU0 (k l : m) : 0 ≤ U k l := by
        have h := hU k l
        have hI : 0 ≤ (1 : Matrix m m ℤ) k l := by simp [Matrix.one_apply]; split_ifs <;> omega
        exact hI.trans h
      have hsum (k : m) : 1 ≤ ∑ l, U k l := by
        have h := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset m)) => hU k l)
        simpa [Matrix.one_apply] using h
      let V := Matrix.transvection i j c * U
      have hVU (k l : m) : U k l ≤ V k l := by
        by_cases hki : k = i
        · subst k
          change U i l ≤ (Matrix.transvection i j c * U) i l
          rw [Matrix.transvection_mul_apply_same]
          exact le_add_of_nonneg_right (mul_nonneg hc.le (hU0 j l))
        · change U k l ≤ (Matrix.transvection i j c * U) k l
          rw [Matrix.transvection_mul_apply_of_ne i j k l hki]
      refine ⟨V, ?_, fun k l => (hU k l).trans (hVU k l), ?_⟩
      · dsimp [V]
        rw [Matrix.det_mul, Matrix.det_transvection_of_ne i j hji.symm, hdet, one_mul]
      · intro k hk
        rcases Finset.mem_insert.mp hk with hki | hk
        · subst k
          change N < ∑ l, (Matrix.transvection i j c * U) i l
          simp only [Matrix.transvection_mul_apply_same, Finset.sum_add_distrib, ← Finset.mul_sum]
          have hi := hsum i
          have hj := hsum j
          have hN : N < c := by dsimp [c]; omega
          nlinarith
        · exact lt_of_lt_of_le (hrows k hk) (Finset.sum_le_sum (fun l _ => hVU k l))
  obtain ⟨U, hd, hU, hrows⟩ := build Finset.univ
  exact ⟨U, hd, hU, fun i => hrows i (Finset.mem_univ i)⟩

omit [Fintype n] in
/-- A row sum is a lower bound for multiplication of a nonnegative integer
matrix by a strictly positive integer matrix. -/
theorem row_sum_le_mul (U : Matrix m m ℤ) (S : Matrix m n ℤ)
    (hU : ∀ i j, 0 ≤ U i j) (hS : Positive S) (i : m) (j : n) :
    ∑ k, U i k ≤ (U * S) i j := by
  apply Finset.sum_le_sum
  intro k _
  have hSk : 1 ≤ S k j := hS k j
  nlinarith [hU i k]

/-- The actual integral change of coordinates associated to a unimodular matrix. -/
noncomputable def coordinateEquiv [DecidableEq m] (U : Matrix m m ℤ) (hU : IsUnit U) :
    (m → ℤ) ≃ₗ[ℤ] (m → ℤ) :=
  LinearEquiv.ofBijective U.mulVecLin
    ⟨Matrix.mulVec_injective_of_isUnit hU, Matrix.mulVec_surjective_iff_isUnit.mpr hU⟩

/-- The induced equivalence of actual cokernels when the presentation matrix
is multiplied on the left by a unimodular integer matrix. -/
noncomputable def targetCokernelEquiv [DecidableEq m]
    (B' U : Matrix m m ℤ) (hU : IsUnit U) : Cokernel B' ≃ₗ[ℤ] Cokernel (U * B') :=
  Submodule.Quotient.equiv _ _ (coordinateEquiv U hU) (by
    change (LinearMap.range B'.mulVecLin).map U.mulVecLin = LinearMap.range (U * B').mulVecLin
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp])

@[simp]
theorem targetCokernelEquiv_quotient [DecidableEq m]
    (B' U : Matrix m m ℤ) (hU : IsUnit U) (x : m → ℤ) :
    targetCokernelEquiv B' U hU (quotient B' x) = quotient (U * B') (U *ᵥ x) := rfl

/-- Left multiplication by a unimodular matrix leaves the actual kernel
submodule unchanged, not merely abstractly isomorphic. -/
theorem kernel_left_unimodular [DecidableEq m]
    (B' U : Matrix m m ℤ) (hU : IsUnit U) : Kernel (U * B') = Kernel B' := by
  ext x
  change (U * B') *ᵥ x = 0 ↔ B' *ᵥ x = 0
  rw [← Matrix.mulVec_mulVec]
  constructor
  · intro h
    apply Matrix.mulVec_injective_of_isUnit hU
    simpa using h
  · intro h
    rw [h, Matrix.mulVec_zero]

/-- Simultaneous positive lifting for a finite family of arbitrary graded maps.

The target has at least two coordinates (`Nontrivial m`). The source is any
finite type. The matrices act on column vectors; positivity is entrywise.
The output uses the same nonnegative determinant-one target change in every
channel. The cokernel equation uses its actual induced linear equivalence;
the kernel submodule is unchanged. The block matrix is exactly equation (1)
of Section 3, and its companion multiplicity is `S + (U * B') * Z`.
-/
theorem simultaneous_positive_lifting [DecidableEq n] [DecidableEq m] [Nontrivial m]
    {C : Type*} [Fintype C]
    (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (hB : Positive B) (hB' : Positive B')
    (f₀ : C → Cokernel B →ₗ[ℤ] Cokernel B')
    (f₁ : C → Kernel B →ₗ[ℤ] Kernel B') :
    ∃ (U : Matrix m m ℤ) (hU : IsUnit U),
      U.det = 1 ∧ (∀ i j, 0 ≤ U i j) ∧ Positive (U * B') ∧
      Kernel (U * B') = Kernel B' ∧
      ∃ (S H Z : C → Matrix m n ℤ), ∀ c,
        S c * B = (U * B') * H c ∧
        Positive (S c) ∧
        Positive (MatrixDiagrams.diagram B (S c) (H c) (Z c)) ∧
        Positive (S c + (U * B') * Z c) ∧
        (∀ x, quotient (U * B') (S c *ᵥ x) =
          targetCokernelEquiv B' U hU (f₀ c (quotient B x))) ∧
        (∀ x : Kernel B, H c *ᵥ x.val = (f₁ c x).val) := by
  classical
  choose S H hS hH hchain h₀ h₁ using
    fun c => exists_positive_compatible_lifts B B' hB hB' (f₀ c) (f₁ c)
  let J : Matrix m n ℤ := fun _ _ => 1
  let W (c : C) : Matrix m n ℤ := H c + J * (1 + B)
  obtain ⟨M, hM⟩ := Finite.exists_le (fun p : C × m × n => W p.1 p.2.1 p.2.2)
  obtain ⟨U, hdet, hUI, hrows⟩ := exists_large_unimodular (m := m) (max M 1)
  have hU : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr (hdet ▸ isUnit_one)
  have hU0 (i j : m) : 0 ≤ U i j := by
    have hI : 0 ≤ (1 : Matrix m m ℤ) i j := by simp [Matrix.one_apply]; split_ifs <;> omega
    exact hI.trans (hUI i j)
  have hUS (c : C) (i : m) (j : n) : 1 < (U * S c) i j := by
    have hr := hrows i
    have hs := row_sum_le_mul U (S c) hU0 (hS c) i j
    have hm := le_max_right M 1
    omega
  have hUW (c : C) (i : m) (j : n) : W c i j < (U * S c) i j := by
    have hw : W c i j ≤ M := hM (c, i, j)
    have hr := hrows i
    have hs := row_sum_le_mul U (S c) hU0 (hS c) i j
    have hm := le_max_left M 1
    omega
  have hUB : Positive (U * B') := by
    intro i j
    have hr := hrows i
    have hs := row_sum_le_mul U B' hU0 hB' i j
    have hm := le_max_right M 1
    omega
  have hJA (i : m) (j : n) : 0 ≤ (J * (1 + B) : Matrix m n ℤ) i j := by
    apply Finset.sum_nonneg
    intro k _
    have hI : 0 ≤ (1 : Matrix n n ℤ) k j := by simp [Matrix.one_apply]; split_ifs <;> omega
    change 0 ≤ 1 * ((1 : Matrix n n ℤ) k j + B k j)
    have := hB k j
    omega
  have hW (c : C) (i : m) (j : n) : 0 < W c i j := by
    change 0 < H c i j + (J * (1 + B) : Matrix m n ℤ) i j
    exact add_pos_of_pos_of_nonneg (hH c i j) (hJA i j)
  refine ⟨U, hU, hdet, hU0, hUB, kernel_left_unimodular B' U hU,
    fun c => U * S c, H, fun _ => J, ?_⟩
  intro c
  refine ⟨?_, (fun i j => lt_trans (by norm_num) (hUS c i j)), ?_, ?_, ?_, h₁ c⟩
  · rw [Matrix.mul_assoc, hchain c, Matrix.mul_assoc]
  · intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change 0 < (U * S c) i j - 1
        have := hUS c i j
        omega
      | inr j =>
        change 0 < (U * S c) i j - H c i j - (J * (1 + B) : Matrix m n ℤ) i j
        have := hUW c i j
        change H c i j + (J * (1 + B) : Matrix m n ℤ) i j < (U * S c) i j at this
        omega
    | inr i =>
      cases j with
      | inl j => change 0 < (1 : ℤ); norm_num
      | inr j => exact hW c i j
  · intro i j
    change 0 < (U * S c) i j + ((U * B') * J) i j
    apply add_pos_of_pos_of_nonneg (lt_trans (by norm_num) (hUS c i j))
    apply Finset.sum_nonneg
    intro k _
    change 0 ≤ (U * B') i k * 1
    simpa using (hUB i k).le
  · intro x
    rw [← Matrix.mulVec_mulVec, ← targetCokernelEquiv_quotient, h₀]

/-- The positive lifting lemma in finite matrix sizes and for arbitrary
homomorphisms of abelian groups. The hypothesis `2 ≤ r'` is the manuscript's
exact target-size condition; there are `q` prescribed channels. -/
theorem finite_simultaneous_positive_lifting {r r' q : ℕ} (hsize : 2 ≤ r')
    (B : Matrix (Fin r) (Fin r) ℤ) (B' : Matrix (Fin r') (Fin r') ℤ)
    (hB : Positive B) (hB' : Positive B')
    (f₀ : Fin q → Cokernel B →+ Cokernel B')
    (f₁ : Fin q → Kernel B →+ Kernel B') :
    ∃ (U : Matrix (Fin r') (Fin r') ℤ) (hU : IsUnit U),
      U.det = 1 ∧ (∀ i j, 0 ≤ U i j) ∧ Positive (U * B') ∧
      Kernel (U * B') = Kernel B' ∧
      ∃ (S H Z : Fin q → Matrix (Fin r') (Fin r) ℤ), ∀ c,
        S c * B = (U * B') * H c ∧
        Positive (S c) ∧
        Positive (MatrixDiagrams.diagram B (S c) (H c) (Z c)) ∧
        Positive (S c + (U * B') * Z c) ∧
        (∀ x, quotient (U * B') (S c *ᵥ x) =
          targetCokernelEquiv B' U hU (f₀ c (quotient B x))) ∧
        (∀ x : Kernel B, H c *ᵥ x.val = (f₁ c x).val) := by
  let : Nontrivial (Fin r') := Fin.nontrivial_iff_two_le.mpr hsize
  exact simultaneous_positive_lifting B B' hB hB'
    (fun c => (f₀ c).toIntLinearMap) (fun c => (f₁ c).toIntLinearMap)

end Suzuki.PositiveLifting

import Suzuki.PositiveLifting

/-!
# The initial graph's actual integer presentation and signed generators

For the two-by-two all-ones matrix B, the cokernel map is (x₀,x₁)↦x₀−x₁,
the kernel generator is (1,−1), and every balanced dimension vector has zero
cokernel class. These are the actual integer kernel and quotient modules used
by positive lifting. Identifying them with graph K-theory is the explicit
published graph-K input; this module does not assume that identification.
-/

namespace Suzuki.InitialGraphPresentation
open Matrix PositiveLifting

def B : Matrix (Fin 2) (Fin 2) ℤ := fun _ _ => 1

theorem positive : PositiveLifting.Positive B := by intro i j; norm_num [B]

theorem mulVec (x : Fin 2 → ℤ) (i : Fin 2) : (B *ᵥ x) i = x 0 + x 1 := by
  simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def difference : (Fin 2 → ℤ) →ₗ[ℤ] ℤ where
  toFun x := x 0 - x 1
  map_add' x y := by simp only [Pi.add_apply]; abel
  map_smul' z x := by simp [mul_sub]

theorem range_le_ker : LinearMap.range B.mulVecLin ≤ LinearMap.ker difference := by
  rintro x ⟨y, rfl⟩
  change (B *ᵥ y) 0 - (B *ᵥ y) 1 = 0
  rw [mulVec, mulVec, sub_self]

def cokernelMap : Cokernel B →ₗ[ℤ] ℤ :=
  (LinearMap.range B.mulVecLin).liftQ difference range_le_ker

@[simp] theorem cokernelMap_quotient (x : Fin 2 → ℤ) :
    cokernelMap (quotient B x) = x 0 - x 1 := rfl

theorem cokernelMap_bijective : Function.Bijective cokernelMap := by
  constructor
  · apply (injective_iff_map_eq_zero cokernelMap).mpr
    intro x
    refine Submodule.Quotient.induction_on (LinearMap.range B.mulVecLin) x ?_
    intro a ha
    change a 0 - a 1 = 0 at ha
    have he : a = B *ᵥ ![a 0,0] := by
      funext i
      rw [mulVec]
      fin_cases i <;> simp_all
      omega
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨![a 0,0], he.symm⟩
  · intro z
    refine ⟨quotient B ![z,0], ?_⟩
    change z - 0 = z
    exact sub_zero z

noncomputable def cokernelEquiv : Cokernel B ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective cokernelMap cokernelMap_bijective

@[simp] theorem cokernelEquiv_quotient (x : Fin 2 → ℤ) :
    cokernelEquiv (quotient B x) = x 0 - x 1 := rfl

theorem first_generator : cokernelEquiv (quotient B ![1,0]) = 1 := by rw [cokernelEquiv_quotient]; norm_num
theorem second_generator : cokernelEquiv (quotient B ![0,1]) = -1 := by rw [cokernelEquiv_quotient]; norm_num

def kernelEquiv : Kernel B ≃ₗ[ℤ] ℤ where
  toFun x := x.val 0
  invFun z := ⟨![z,-z], by
    change B *ᵥ ![z,-z] = 0
    funext i
    simp [mulVec]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := congrFun x.property 0
    change (B *ᵥ x.val) 0 = 0 at hx
    rw [mulVec] at hx
    funext i
    fin_cases i <;> simp_all
    omega
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernel_generator : (kernelEquiv.symm 1).val = ![1,-1] := rfl

theorem balanced_class_zero (a : ℤ) : quotient B ![a,a] = 0 := by
  apply cokernelEquiv.injective
  rw [cokernelEquiv_quotient, map_zero]
  exact sub_self a

/-- Every later unimodularly changed presentation has the same explicit
cokernel convention, transported by its actual quotient equivalence. -/
noncomputable def transportedCokernel (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : IsUnit U) :
    Cokernel (U * B) ≃ₗ[ℤ] ℤ :=
  (targetCokernelEquiv B U hU).symm.trans cokernelEquiv

theorem transportedCokernel_quotient (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : IsUnit U)
    (x : Fin 2 → ℤ) :
    transportedCokernel U hU (quotient (U * B) (U *ᵥ x)) = x 0 - x 1 := by
  rw [← targetCokernelEquiv_quotient B U hU x]
  change cokernelEquiv ((targetCokernelEquiv B U hU).symm
    (targetCokernelEquiv B U hU (quotient B x))) = _
  rw [LinearEquiv.symm_apply_apply, cokernelEquiv_quotient]

noncomputable def transportedKernel (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : IsUnit U) :
    Kernel (U * B) ≃ₗ[ℤ] ℤ := by
  rw [kernel_left_unimodular B U hU]
  exact kernelEquiv

end Suzuki.InitialGraphPresentation

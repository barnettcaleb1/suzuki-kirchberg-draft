import Suzuki.MultiplicityEmbeddings
import Mathlib.Algebra.Star.UnitaryStarAlgAut
/-!
# Exact squares from nonnegative integer multiplicities

The composite block representations are flattened by an explicit equivalence
of matrix coordinates. Their copy counts are the matrix product. Equal
products give an actual permutation unitary, and conjugating a final edge gives
an exact square of unital star homomorphisms. Nonzero columns imply faithfulness.
No classification or unitary-conjugacy hypothesis is used.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Suzuki.MultiplicityEmbeddings
open scoped CStarAlgebra ComplexOrder
open Matrix
variable {ι ν ω : Type*} [Fintype ι] [Fintype ν] [Fintype ω]
  [DecidableEq ι] [DecidableEq ν] [DecidableEq ω]

omit [Fintype ν] [DecidableEq ν] in
theorem multiplicityHom_pullback (k : ι → ℕ) (M : Matrix ν ι ℕ)
    (a : Blocks k) (v : ν) (r s : Slots k M v) :
    multiplicityHom k M a v (slotEquiv k M v r) (slotEquiv k M v s) =
      copyHom k (fun c : Copies M v => c.1) a r s := by
  change copyHom k (fun c : Copies M v => c.1) a
    ((slotEquiv k M v).symm (slotEquiv k M v r))
    ((slotEquiv k M v).symm (slotEquiv k M v s)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

abbrev CompositionCopies (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ) (w : ω) :=
  Σ c : Copies N w, Copies M c.1
abbrev compositionLabel (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ) (w : ω) :
    CompositionCopies M N w → ι := fun c => c.2.1

def compositionEnumeration (k : ι → ℕ) (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ) (w : ω) :
    CopySlots k (compositionLabel M N w) ≃ Fin (targetSize (targetSize k M) N w) :=
  ((Equiv.sigmaAssoc (fun (c : Copies N w) (d : Copies M c.1) => Fin (k d.1))).trans
    (Equiv.sigmaCongrRight (fun c : Copies N w => slotEquiv k M c.1))).trans
    (slotEquiv (targetSize k M) N w)

omit [Fintype ω] [DecidableEq ω] in
theorem composition_normalForm (k : ι → ℕ) (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ)
    (w : ω) (a : Blocks k) :
    CStarMatrix.reindexₐ ℂ ℂ (compositionEnumeration k M N w)
      (copyHom k (compositionLabel M N w) a) =
      multiplicityHom (targetSize k M) N (multiplicityHom k M a) w := by
  let E := compositionEnumeration k M N w
  apply CStarMatrix.ext
  intro r s
  obtain ⟨⟨⟨c, d⟩, i⟩, rfl⟩ := E.surjective r
  obtain ⟨⟨⟨c', d'⟩, j⟩, rfl⟩ := E.surjective s
  change copyHom k (compositionLabel M N w) a
    (E.symm (E ⟨⟨c, d⟩, i⟩)) (E.symm (E ⟨⟨c', d'⟩, j⟩)) =
    multiplicityHom (targetSize k M) N (multiplicityHom k M a) w
      (slotEquiv (targetSize k M) N w ⟨c, slotEquiv k M c.1 ⟨d, i⟩⟩)
      (slotEquiv (targetSize k M) N w ⟨c', slotEquiv k M c'.1 ⟨d', j⟩⟩)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, multiplicityHom_pullback]
  by_cases hc : c = c'
  · subst c'
    rw [copyHom_same, multiplicityHom_pullback]
    by_cases hd : d = d'
    · subst d'
      rw [copyHom_same, copyHom_same]
    · have hp : (⟨c, d⟩ : CompositionCopies M N w) ≠ ⟨c, d'⟩ := by
        simpa only [ne_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hd
      rw [copyHom_different _ _ _ hp, copyHom_different _ _ _ hd]
  · have hp : (⟨c, d⟩ : CompositionCopies M N w) ≠ ⟨c', d'⟩ :=
      fun h => hc (congrArg Sigma.fst h)
    rw [copyHom_different _ _ _ hp, copyHom_different _ _ _ hc]

omit [Fintype ω] [DecidableEq ω] [DecidableEq ν] in
theorem composition_copy_count (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ) (w : ω) (s : ι) :
    Fintype.card {c : CompositionCopies M N w // compositionLabel M N w c = s} =
      (N * M) w s := by
  let e : {c : CompositionCopies M N w // compositionLabel M N w c = s} ≃
      (Σ c : Copies N w, Fin (M c.1 s)) :=
    { toFun := fun z => ⟨z.val.1, Fin.cast (congrArg (M z.val.1.1) z.property) z.val.2.2⟩
      invFun := fun z => ⟨⟨z.1, ⟨s, z.2⟩⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨c, ⟨i, u⟩⟩, hi⟩
        change i = s at hi
        subst i
        rfl
      right_inv := by rintro ⟨c, u⟩; rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_sigma, Copies, Fintype.sum_sigma, Matrix.mul_apply]

variable {η : Type*} [Fintype η] [DecidableEq η]

omit [Fintype ω] [DecidableEq ω] [DecidableEq ι] [DecidableEq ν] [DecidableEq η] in
theorem compositionDimensionEq (k : ι → ℕ) (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ)
    (M' : Matrix η ι ℕ) (N' : Matrix ω η ℕ) (hprod : N * M = N' * M') (w : ω) :
    targetSize (targetSize k M') N' w = targetSize (targetSize k M) N w := by
  rw [targetSize_comp, targetSize_comp, hprod]

omit [Fintype ω] [DecidableEq ω] in
/-- Equality of multiplicity products yields a single actual unitary conjugating
both composite maps, simultaneously for every source element. -/
theorem compositions_unitarily_conjugate (k : ι → ℕ)
    (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ)
    (M' : Matrix η ι ℕ) (N' : Matrix ω η ℕ) (hprod : N * M = N' * M') (w : ω) :
    ∃ U : unitary (CStarMatrix (Fin (targetSize (targetSize k M) N w))
        (Fin (targetSize (targetSize k M) N w)) ℂ),
      ∀ a : Blocks k,
        CStarMatrix.reindexₐ ℂ ℂ
          (finCongr (compositionDimensionEq k M N M' N' hprod w))
          (multiplicityHom (targetSize k M') N' (multiplicityHom k M' a) w) =
        (U : CStarMatrix _ _ ℂ) *
          multiplicityHom (targetSize k M) N (multiplicityHom k M a) w *
          star (U : CStarMatrix _ _ ℂ) := by
  have hcount : ∀ s : ι,
      Fintype.card {c : CompositionCopies M N w // compositionLabel M N w c = s} =
      Fintype.card {c : CompositionCopies M' N' w // compositionLabel M' N' w c = s} := by
    intro s
    rw [composition_copy_count, composition_copy_count, hprod]
  obtain ⟨U, hU⟩ := copies_unitarily_conjugate_of_counts k
    (compositionLabel M N w) (compositionLabel M' N' w) hcount
    (compositionEnumeration k M N w)
    ((compositionEnumeration k M' N' w).trans
      (finCongr (compositionDimensionEq k M N M' N' hprod w)))
  refine ⟨U, fun a => ?_⟩
  have h := hU a
  change CStarMatrix.reindexₐ ℂ ℂ
      (finCongr (compositionDimensionEq k M N M' N' hprod w))
      (CStarMatrix.reindexₐ ℂ ℂ (compositionEnumeration k M' N' w)
        (copyHom k (compositionLabel M' N' w) a)) = _ at h
  simpa only [composition_normalForm] using h


omit [Fintype ω] [DecidableEq ω] in
/-- Correcting the last map of one route by explicit target unitaries produces
an exact commuting square. The corrected map remains a unital star embedding. -/
theorem exists_exact_square (k : ι → ℕ)
    (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ)
    (M' : Matrix η ι ℕ) (N' : Matrix ω η ℕ)
    (hprod : N * M = N' * M') (hN' : ∀ s, ∃ w, 0 < N' w s) :
    ∃ ψ : Blocks (targetSize k M') →⋆ₐ[ℂ] Blocks (targetSize (targetSize k M) N),
      Function.Injective ψ ∧
      ψ.comp (multiplicityHom k M') =
        (multiplicityHom (targetSize k M) N).comp (multiplicityHom k M) := by
  choose U hU using fun w => compositions_unitarily_conjugate k M N M' N' hprod w
  let castRow := fun w => CStarMatrix.reindexₐ ℂ ℂ
    (finCongr (compositionDimensionEq k M N M' N' hprod w))
  let aut := fun w => Unitary.conjStarAlgAut ℂ _ (U w)
  let F := fun w => (aut w).symm.toStarAlgHom.comp
    ((castRow w).toStarAlgHom.comp (rowHom (targetSize k M') N' w))
  let ψ : Blocks (targetSize k M') →⋆ₐ[ℂ] Blocks (targetSize (targetSize k M) N) :=
    { toFun := fun a w => F w a
      map_zero' := by funext w; exact map_zero (F w)
      map_one' := by funext w; exact map_one (F w)
      map_add' := by intro a b; funext w; exact map_add (F w) a b
      map_mul' := by intro a b; funext w; exact map_mul (F w) a b
      commutes' := by intro z; funext w; exact (F w).commutes z
      map_star' := by intro a; funext w; exact map_star (F w) a }
  refine ⟨ψ, ?_, ?_⟩
  · intro a b hab
    apply multiplicityHom_injective (targetSize k M') N' hN'
    funext w
    have h := congrArg (fun z : Blocks (targetSize (targetSize k M) N) => z w) hab
    exact (castRow w).injective ((aut w).symm.injective h)
  · apply StarAlgHom.ext
    intro a
    funext w
    change (aut w).symm ((castRow w)
      (multiplicityHom (targetSize k M') N' (multiplicityHom k M' a) w)) = _
    rw [hU w a]
    change (aut w).symm ((aut w)
      (multiplicityHom (targetSize k M) N (multiplicityHom k M a) w)) = _
    exact (aut w).symm_apply_apply _

omit [DecidableEq ω] in
/-- In the finite direct-sum C*-norms, the corrected map is an isometry. -/
theorem exists_isometric_exact_square (k : ι → ℕ)
    (M : Matrix ν ι ℕ) (N : Matrix ω ν ℕ)
    (M' : Matrix η ι ℕ) (N' : Matrix ω η ℕ)
    (hprod : N * M = N' * M') (hN' : ∀ s, ∃ w, 0 < N' w s) :
    ∃ ψ : Blocks (targetSize k M') →⋆ₐ[ℂ] Blocks (targetSize (targetSize k M) N),
      Isometry ψ ∧
      ψ.comp (multiplicityHom k M') =
        (multiplicityHom (targetSize k M) N).comp (multiplicityHom k M) := by
  obtain ⟨ψ, hψ, hsquare⟩ := exists_exact_square k M N M' N' hprod hN'
  exact ⟨ψ, NonUnitalStarAlgHom.isometry _ hψ, hsquare⟩

end Suzuki.MultiplicityEmbeddings

import Suzuki.CStarAmalgam

/-!
# Full amalgams and sequential C⋆-algebra colimits

All objects here are actual complete unital complex C⋆-algebras, and all maps
are unital complex star algebra homomorphisms. `IsSequentialColimit` specifies
the exact universal property of a supplied C⋆-algebra and supplied cocone.
Its quantifiers range over all C⋆-algebras in the same fixed universe.

The main result proves that compatible sequential colimits preserve the full
amalgam universal property. It is conditional on the four supplied colimit
universal properties. No construction of norm-completed inductive limits,
injectivity, nuclearity, simplicity, stable finiteness or KK-theory is claimed.
-/

namespace Suzuki.InductiveAmalgam

universe u

/-- A sequential system of actual unital complex C⋆-algebras. -/
structure System where
  obj : ℕ → Type u
  algebra : ∀ n, CStarAlgebra (obj n)
  step : ∀ n, obj n →⋆ₐ[ℂ] obj (n + 1)

attribute [instance] System.algebra

namespace System

/-- An actual natural family of unital star homomorphisms between sequences. -/
structure Hom (S T : System.{u}) where
  app : ∀ n, S.obj n →⋆ₐ[ℂ] T.obj n
  naturality : ∀ n, (T.step n).comp (app n) = (app (n + 1)).comp (S.step n)

end System

variable {S : System.{u}} {L : Type u} [CStarAlgebra L]

/-- The sequential colimit property in the category of actual unital complex
C⋆-algebras in universe `u`. Compatible target maps admit exactly one extension. -/
structure IsSequentialColimit (ι : ∀ n, S.obj n →⋆ₐ[ℂ] L) : Prop where
  commutes : ∀ n, (ι (n + 1)).comp (S.step n) = ι n
  extension : ∀ {C : Type u} [CStarAlgebra C]
    (f : ∀ n, S.obj n →⋆ₐ[ℂ] C),
    (∀ n, (f (n + 1)).comp (S.step n) = f n) →
      ∃! φ : L →⋆ₐ[ℂ] C, ∀ n, φ.comp (ι n) = f n

namespace IsSequentialColimit

variable {ι : ∀ n, S.obj n →⋆ₐ[ℂ] L} (h : IsSequentialColimit ι)
variable {C : Type u} [CStarAlgebra C]

/-- The extension supplied by the exact sequential C⋆-colimit property. -/
noncomputable def lift (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ n, (f (n + 1)).comp (S.step n) = f n) : L →⋆ₐ[ℂ] C :=
  (h.extension f hf).choose

@[simp] theorem lift_stage (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ n, (f (n + 1)).comp (S.step n) = f n) (n : ℕ) :
    (h.lift f hf).comp (ι n) = f n :=
  (h.extension f hf).choose_spec.1 n

include h in
/-- Homomorphisms out of the colimit are determined by every stage restriction. -/
theorem hom_ext {φ ψ : L →⋆ₐ[ℂ] C}
    (heq : ∀ n, φ.comp (ι n) = ψ.comp (ι n)) : φ = ψ := by
  have hc : ∀ n, (ψ.comp (ι (n + 1))).comp (S.step n) = ψ.comp (ι n) := by
    intro n
    rw [StarAlgHom.comp_assoc, h.commutes]
  obtain ⟨χ, _, hχ⟩ := h.extension (fun n => ψ.comp (ι n)) hc
  exact (hχ φ heq).trans (hχ ψ (fun _ => rfl)).symm

theorem lift_unique (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ n, (f (n + 1)).comp (S.step n) = f n)
    (φ : L →⋆ₐ[ℂ] C) (hφ : ∀ n, φ.comp (ι n) = f n) : φ = h.lift f hf := by
  apply h.hom_ext
  intro n
  rw [hφ, h.lift_stage]

include h in
/-- Any closed star subalgebra containing every stage image is the whole
colimit. This uses the universal property with an actual closed C⋆-subalgebra. -/
theorem eq_top_of_isClosed (B : StarSubalgebra ℂ L) (hB : IsClosed (B : Set L))
    (hι : ∀ n a, ι n a ∈ B) : B = ⊤ := by
  let : IsClosed (B : Set L) := hB
  let f : ∀ n, S.obj n →⋆ₐ[ℂ] B := fun n => (ι n).codRestrict B (hι n)
  have hf : ∀ n, (f (n + 1)).comp (S.step n) = f n := by
    intro n
    apply StarAlgHom.ext
    intro a
    exact Subtype.ext (DFunLike.congr_fun (h.commutes n) a)
  let φ := h.lift f hf
  have hφ : B.subtype.comp φ = StarAlgHom.id ℂ L := by
    apply h.hom_ext
    intro n
    change B.subtype.comp ((h.lift f hf).comp (ι n)) = _
    rw [h.lift_stage]
    exact StarAlgHom.subtype_comp_codRestrict (ι n) B (hι n)
  apply top_unique
  intro a _
  have ha : (φ a : L) = a := DFunLike.congr_fun hφ a
  exact ha ▸ (φ a).property

include h in
/-- The stage images generate the colimit as a norm-closed star algebra. -/
theorem closure_adjoin_eq_top :
    (StarAlgebra.adjoin ℂ (⋃ n, Set.range (ι n))).topologicalClosure = ⊤ := by
  apply h.eq_top_of_isClosed _ (StarSubalgebra.isClosed_topologicalClosure _)
  intro n a
  apply StarSubalgebra.le_topologicalClosure
  exact StarAlgebra.subset_adjoin _ _ (Set.mem_iUnion.mpr ⟨n, a, rfl⟩)

variable {T : System.{u}} {M : Type u} [CStarAlgebra M]
variable {κ : ∀ n, T.obj n →⋆ₐ[ℂ] M} (hM : IsSequentialColimit κ)

/-- The canonical map on supplied colimits induced by a natural family. -/
noncomputable def map (f : S.Hom T) : L →⋆ₐ[ℂ] M :=
  h.lift (fun n => (κ n).comp (f.app n)) (by
    intro n
    rw [StarAlgHom.comp_assoc, ← f.naturality, ← StarAlgHom.comp_assoc, hM.commutes])

@[simp] theorem map_stage (f : S.Hom T) (n : ℕ) :
    (h.map hM f).comp (ι n) = (κ n).comp (f.app n) := h.lift_stage _ _ n

variable {κ' : ∀ n, S.obj n →⋆ₐ[ℂ] M} (hM' : IsSequentialColimit κ')

theorem lift_comp_lift :
    (hM'.lift ι h.commutes).comp (h.lift κ' hM'.commutes) = StarAlgHom.id ℂ L := by
  apply h.hom_ext
  intro n
  simp only [StarAlgHom.comp_assoc, lift_stage, StarAlgHom.id_comp]

/-- Two supplied colimits of the same actual sequence are canonically
star algebra equivalent. -/
noncomputable def equiv : L ≃⋆ₐ[ℂ] M :=
  StarAlgEquiv.ofBijective (h.lift κ' hM'.commutes) (by
    have hl : Function.LeftInverse (hM'.lift ι h.commutes) (h.lift κ' hM'.commutes) := by
      intro a
      exact DFunLike.congr_fun (h.lift_comp_lift hM') a
    have hr : Function.RightInverse (hM'.lift ι h.commutes) (h.lift κ' hM'.commutes) := by
      intro a
      exact DFunLike.congr_fun (hM'.lift_comp_lift h) a
    exact ⟨hl.injective, hr.surjective⟩)

@[simp] theorem equiv_stage (n : ℕ) (a : S.obj n) : h.equiv hM' (ι n a) = κ' n a :=
  DFunLike.congr_fun (h.lift_stage κ' hM'.commutes n) a

/-- The colimit equivalence preserves the actual C⋆-norm. -/
theorem equiv_isometry : Isometry (h.equiv hM' : L → M) :=
  NonUnitalStarAlgHom.isometry (h.equiv hM') (h.equiv hM').injective

end IsSequentialColimit

section LimitAmalgam

variable {D A₀ A₁ P : System.{u}}
variable (i₀ : D.Hom A₀) (i₁ : D.Hom A₁) (j₀ : A₀.Hom P) (j₁ : A₁.Hom P)
variable (hstage : ∀ n, CStarAmalgam.IsFullAmalgam (i₀.app n) (i₁.app n)
  (j₀.app n) (j₁.app n))
variable {DL AL₀ AL₁ PL : Type u}
variable [CStarAlgebra DL] [CStarAlgebra AL₀] [CStarAlgebra AL₁] [CStarAlgebra PL]
variable {δ : ∀ n, D.obj n →⋆ₐ[ℂ] DL}
variable {α₀ : ∀ n, A₀.obj n →⋆ₐ[ℂ] AL₀} {α₁ : ∀ n, A₁.obj n →⋆ₐ[ℂ] AL₁}
variable {π : ∀ n, P.obj n →⋆ₐ[ℂ] PL}
variable (hD : IsSequentialColimit δ) (h₀ : IsSequentialColimit α₀)
  (h₁ : IsSequentialColimit α₁) (hP : IsSequentialColimit π)
variable {k₀ : DL →⋆ₐ[ℂ] AL₀} {k₁ : DL →⋆ₐ[ℂ] AL₁}
variable {l₀ : AL₀ →⋆ₐ[ℂ] PL} {l₁ : AL₁ →⋆ₐ[ℂ] PL}
variable (hk₀ : ∀ n, k₀.comp (δ n) = (α₀ n).comp (i₀.app n))
  (hk₁ : ∀ n, k₁.comp (δ n) = (α₁ n).comp (i₁.app n))
  (hl₀ : ∀ n, l₀.comp (α₀ n) = (π n).comp (j₀.app n))
  (hl₁ : ∀ n, l₁.comp (α₁ n) = (π n).comp (j₁.app n))

include hstage hD hk₀ hk₁ hl₀ hl₁ in
/-- The two limit-factor embeddings agree on the common limit algebra. -/
theorem limit_commutes : l₀.comp k₀ = l₁.comp k₁ := by
  apply hD.hom_ext
  intro n
  calc
    (l₀.comp k₀).comp (δ n) = l₀.comp ((α₀ n).comp (i₀.app n)) := by
      rw [StarAlgHom.comp_assoc, hk₀]
    _ = ((π n).comp (j₀.app n)).comp (i₀.app n) := by
      rw [← StarAlgHom.comp_assoc, hl₀]
    _ = ((π n).comp (j₁.app n)).comp (i₁.app n) := by
      rw [StarAlgHom.comp_assoc, (hstage n).commutes, ← StarAlgHom.comp_assoc]
    _ = l₁.comp ((α₁ n).comp (i₁.app n)) := by
      rw [← hl₁, StarAlgHom.comp_assoc]
    _ = (l₁.comp k₁).comp (δ n) := by rw [← hk₁, ← StarAlgHom.comp_assoc]

include hstage hD h₀ h₁ hP hk₀ hk₁ hl₀ hl₁ in
/-- Sequential C⋆-algebra colimits preserve the full unital amalgam universal
property. The four colimit properties are hypotheses about supplied complete
C⋆-algebras; the conclusion is the exact full universal property, not just
generation by the limit-factor ranges. -/
theorem isFullAmalgam_of_colimits : CStarAmalgam.IsFullAmalgam k₀ k₁ l₀ l₁ := by
  refine ⟨limit_commutes i₀ i₁ j₀ j₁ hstage hD hk₀ hk₁ hl₀ hl₁, ?_⟩
  intro C instC f₀ f₁ hf
  have hc (n : ℕ) :
      (f₀.comp (α₀ n)).comp (i₀.app n) = (f₁.comp (α₁ n)).comp (i₁.app n) := by
    calc
      (f₀.comp (α₀ n)).comp (i₀.app n) = (f₀.comp k₀).comp (δ n) := by
        rw [StarAlgHom.comp_assoc, ← hk₀, ← StarAlgHom.comp_assoc]
      _ = (f₁.comp k₁).comp (δ n) := by rw [hf]
      _ = (f₁.comp (α₁ n)).comp (i₁.app n) := by
        rw [StarAlgHom.comp_assoc, hk₁, ← StarAlgHom.comp_assoc]
  let g : ∀ n, P.obj n →⋆ₐ[ℂ] C := fun n =>
    (hstage n).lift (f₀.comp (α₀ n)) (f₁.comp (α₁ n)) (hc n)
  have hg₀ (n : ℕ) : (g n).comp (j₀.app n) = f₀.comp (α₀ n) :=
    (hstage n).lift_left _ _ _
  have hg₁ (n : ℕ) : (g n).comp (j₁.app n) = f₁.comp (α₁ n) :=
    (hstage n).lift_right _ _ _
  have hg (n : ℕ) : (g (n + 1)).comp (P.step n) = g n := by
    apply (hstage n).hom_ext
    · calc
        ((g (n + 1)).comp (P.step n)).comp (j₀.app n) =
            (g (n + 1)).comp ((j₀.app (n + 1)).comp (A₀.step n)) := by
          rw [StarAlgHom.comp_assoc, j₀.naturality]
        _ = (f₀.comp (α₀ (n + 1))).comp (A₀.step n) := by
          rw [← StarAlgHom.comp_assoc, hg₀]
        _ = f₀.comp (α₀ n) := by rw [StarAlgHom.comp_assoc, h₀.commutes]
        _ = (g n).comp (j₀.app n) := (hg₀ n).symm
    · calc
        ((g (n + 1)).comp (P.step n)).comp (j₁.app n) =
            (g (n + 1)).comp ((j₁.app (n + 1)).comp (A₁.step n)) := by
          rw [StarAlgHom.comp_assoc, j₁.naturality]
        _ = (f₁.comp (α₁ (n + 1))).comp (A₁.step n) := by
          rw [← StarAlgHom.comp_assoc, hg₁]
        _ = f₁.comp (α₁ n) := by rw [StarAlgHom.comp_assoc, h₁.commutes]
        _ = (g n).comp (j₁.app n) := (hg₁ n).symm
  let φ := hP.lift g hg
  have hφ₀ : φ.comp l₀ = f₀ := by
    apply h₀.hom_ext
    intro n
    calc
      (φ.comp l₀).comp (α₀ n) = φ.comp ((π n).comp (j₀.app n)) := by
        rw [StarAlgHom.comp_assoc, hl₀]
      _ = (g n).comp (j₀.app n) := by
        rw [← StarAlgHom.comp_assoc]
        exact congrArg (fun t => t.comp (j₀.app n)) (hP.lift_stage g hg n)
      _ = f₀.comp (α₀ n) := hg₀ n
  have hφ₁ : φ.comp l₁ = f₁ := by
    apply h₁.hom_ext
    intro n
    calc
      (φ.comp l₁).comp (α₁ n) = φ.comp ((π n).comp (j₁.app n)) := by
        rw [StarAlgHom.comp_assoc, hl₁]
      _ = (g n).comp (j₁.app n) := by
        rw [← StarAlgHom.comp_assoc]
        exact congrArg (fun t => t.comp (j₁.app n)) (hP.lift_stage g hg n)
      _ = f₁.comp (α₁ n) := hg₁ n
  refine ⟨φ, ⟨hφ₀, hφ₁⟩, ?_⟩
  intro ψ hψ
  apply hP.hom_ext
  intro n
  apply (hstage n).hom_ext
  · calc
      (ψ.comp (π n)).comp (j₀.app n) = (ψ.comp l₀).comp (α₀ n) := by
        rw [StarAlgHom.comp_assoc, ← hl₀, ← StarAlgHom.comp_assoc]
      _ = (φ.comp l₀).comp (α₀ n) := by rw [hψ.1, hφ₀]
      _ = (φ.comp (π n)).comp (j₀.app n) := by
        rw [StarAlgHom.comp_assoc, hl₀, ← StarAlgHom.comp_assoc]
  · calc
      (ψ.comp (π n)).comp (j₁.app n) = (ψ.comp l₁).comp (α₁ n) := by
        rw [StarAlgHom.comp_assoc, ← hl₁, ← StarAlgHom.comp_assoc]
      _ = (φ.comp l₁).comp (α₁ n) := by rw [hψ.2, hφ₁]
      _ = (φ.comp (π n)).comp (j₁.app n) := by
        rw [StarAlgHom.comp_assoc, hl₁, ← StarAlgHom.comp_assoc]

include hstage in
/-- The canonical colimit maps induced by the four natural families themselves
form a full amalgam, provided every stage is a full amalgam. -/
theorem isFullAmalgam_canonical :
    CStarAmalgam.IsFullAmalgam (hD.map h₀ i₀) (hD.map h₁ i₁)
      (h₀.map hP j₀) (h₁.map hP j₁) :=
  isFullAmalgam_of_colimits i₀ i₁ j₀ j₁ hstage hD h₀ h₁ hP
    (hD.map_stage h₀ i₀) (hD.map_stage h₁ i₁) (h₀.map_stage hP j₀) (h₁.map_stage hP j₁)

end LimitAmalgam

end Suzuki.InductiveAmalgam

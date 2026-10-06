import Suzuki.DirectedCStarLimit
import Suzuki.InductiveAmalgam

/-!
# Construction of injective sequential C⋆-algebra colimits

This constructs the algebra and proves the universal property used in
`InductiveAmalgam`. The hypothesis is injectivity of each connecting map;
no pre-existing colimit or colimit universal property is supplied.
-/

noncomputable section

namespace Suzuki.SequentialCStarLimit

open InductiveAmalgam

universe u

variable (S : System.{u})

/-- Compose the adjacent connecting maps along a finite interval. -/
def transition (m n : ℕ) (h : m ≤ n) : S.obj m →⋆ₐ[ℂ] S.obj n :=
  Nat.leRecOn h (@fun k g => (S.step k).comp g) (StarAlgHom.id ℂ _)

theorem transition_apply (m n : ℕ) (h : m ≤ n) :
    (transition S m n h : S.obj m → S.obj n) =
      Nat.leRecOn h (@fun k => S.step k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ext x
  induction k with
  | zero => simp [transition, Nat.leRecOn_self]
  | succ k ih =>
    rw [Nat.leRecOn_succ le_self_add, transition, Nat.leRecOn_succ le_self_add,
      ← transition, StarAlgHom.comp_apply, ih]

instance transitionDirectedSystem :
    DirectedSystem S.obj (fun i j h => transition S i j h) where
  map_self i x := by simp [transition_apply, Nat.leRecOn_self]
  map_map i j k hij hjk x := by
    simp only [transition_apply, Nat.leRecOn_trans hij hjk]

@[simp] theorem transition_self (n : ℕ) :
    transition S n n le_rfl = StarAlgHom.id ℂ (S.obj n) := by
  simp [transition, Nat.leRecOn_self]

@[simp] theorem transition_succ (n : ℕ) :
    transition S n (n + 1) (Nat.le_succ n) = S.step n := by
  simp [transition, Nat.leRecOn_succ, Nat.leRecOn_self]

theorem transition_injective (hinj : ∀ n, Function.Injective (S.step n))
    (m n : ℕ) (h : m ≤ n) : Function.Injective (transition S m n h) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simpa [transition, Nat.leRecOn_self] using Function.injective_id
  | succ k ih =>
    rw [transition, Nat.leRecOn_succ le_self_add]
    exact (hinj _).comp (ih _)

variable [hS : Fact (∀ n, Function.Injective (S.step n))]

instance transitionInjective :
    Fact (∀ i j h, Function.Injective (transition S i j h)) :=
  ⟨transition_injective S hS.out⟩

/-- The concrete completed algebraic direct limit of the sequence. -/
abbrev Limit := DirectedCStarLimit.Limit S.obj (transition S)

instance limitCStarAlgebra : CStarAlgebra (Limit S) := inferInstance

def stage (n : ℕ) : S.obj n →⋆ₐ[ℂ] Limit S :=
  DirectedCStarLimit.stage S.obj (transition S) n

theorem stage_isometry (n : ℕ) : Isometry (stage S n) :=
  DirectedCStarLimit.stage_isometry S.obj (transition S) n

theorem stage_injective (n : ℕ) : Function.Injective (stage S n) :=
  (stage_isometry S n).injective

theorem stage_commutes (n : ℕ) : (stage S (n + 1)).comp (S.step n) = stage S n := by
  simpa only [transition_succ, stage] using
    DirectedCStarLimit.stage_commutes S.obj (transition S) n (n + 1) (Nat.le_succ n)

omit hS in
theorem compatible_transition {C : Type*} [CStarAlgebra C]
    (g : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hg : ∀ n, (g (n + 1)).comp (S.step n) = g n)
    (m n : ℕ) (h : m ≤ n) (x : S.obj m) :
    g n (transition S m n h x) = g m x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp only [Nat.add_zero, transition_self]; rfl
  | succ k ih =>
    rw [transition, Nat.leRecOn_succ le_self_add]
    change ((g (m + k + 1)).comp (S.step (m + k)))
      (transition S m (m + k) le_self_add x) = _
    rw [hg]
    exact ih _

/-- The constructed completion satisfies the full sequential universal property. -/
theorem isSequentialColimit : IsSequentialColimit (stage S) where
  commutes := stage_commutes S
  extension g hg := by
    let compat := compatible_transition S g hg
    refine ⟨DirectedCStarLimit.lift S.obj (transition S) g compat, ?_, ?_⟩
    · intro n
      apply StarAlgHom.ext
      intro a
      exact DirectedCStarLimit.lift_stage_apply _ _ _ _ n a
    · intro k hk
      apply DirectedCStarLimit.lift_unique
      intro n a
      exact DFunLike.congr_fun (hk n) a

theorem dense_stage_union : Dense (⋃ n, Set.range (stage S n)) :=
  DirectedCStarLimit.dense_stage_union S.obj (transition S)

instance limitSeparable [∀ n, TopologicalSpace.SeparableSpace (S.obj n)] :
    TopologicalSpace.SeparableSpace (Limit S) := inferInstance

@[simp] theorem norm_stage (n : ℕ) (a : S.obj n) : ‖stage S n a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (stage S n) (stage_injective S n) a

variable (T : System.{u}) [Fact (∀ n, Function.Injective (T.step n))]

/-- A natural family induces the canonical homomorphism between constructed limits. -/
def map (f : S.Hom T) : Limit S →⋆ₐ[ℂ] Limit T :=
  (isSequentialColimit S).map (isSequentialColimit T) f

@[simp] theorem map_stage (f : S.Hom T) (n : ℕ) (a : S.obj n) :
    map S T f (stage S n a) = stage T n (f.app n a) :=
  DFunLike.congr_fun ((isSequentialColimit S).map_stage (isSequentialColimit T) f n) a

open scoped CStarAlgebra in
/-- Stagewise injectivity gives an isometric homomorphism of the actual limits. -/
theorem map_isometry (f : S.Hom T) (hf : ∀ n, Function.Injective (f.app n)) :
    Isometry (map S T f) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_norm.comp (map_continuous (map S T f))) continuous_norm
  | ih a =>
    obtain ⟨n, b, rfl⟩ := DirectLimit.exists_eq_mk (transition S) a
    change ‖map S T f (stage S n b)‖ = ‖stage S n b‖
    rw [map_stage, norm_stage, norm_stage]
    exact NonUnitalStarAlgHom.norm_map (f.app n) (hf n) b

theorem map_injective (f : S.Hom T) (hf : ∀ n, Function.Injective (f.app n)) :
    Function.Injective (map S T f) := (map_isometry S T f hf).injective

section Amalgam

variable {D A₀ A₁ P : System.{u}}
variable [Fact (∀ n, Function.Injective (D.step n))]
variable [Fact (∀ n, Function.Injective (A₀.step n))]
variable [Fact (∀ n, Function.Injective (A₁.step n))]
variable [Fact (∀ n, Function.Injective (P.step n))]

/-- Full amalgamation passes to the constructed injective sequential limits.
Only the stage amalgam universal properties are inputs; all limit algebras and
their universal properties have been constructed and proved above. -/
theorem isFullAmalgam (i₀ : D.Hom A₀) (i₁ : D.Hom A₁)
    (j₀ : A₀.Hom P) (j₁ : A₁.Hom P)
    (hstage : ∀ n, CStarAmalgam.IsFullAmalgam (i₀.app n) (i₁.app n)
      (j₀.app n) (j₁.app n)) :
    CStarAmalgam.IsFullAmalgam (map D A₀ i₀) (map D A₁ i₁)
      (map A₀ P j₀) (map A₁ P j₁) :=
  InductiveAmalgam.isFullAmalgam_canonical i₀ i₁ j₀ j₁ hstage
    (isSequentialColimit D) (isSequentialColimit A₀)
    (isSequentialColimit A₁) (isSequentialColimit P)

end Amalgam

end Suzuki.SequentialCStarLimit

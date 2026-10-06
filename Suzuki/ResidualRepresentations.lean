import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Suzuki.StableFiniteness

/-!
# Countable finite-dimensional representations with separating tails

This file uses actual unital star homomorphisms to complex matrix algebras.
It proves the countable selection and repetition step for a separable unital
RFD algebra. Existence of the nuclear RFD KK model is a separate obligation.
-/

noncomputable section

namespace Suzuki.ResidualRepresentations

open scoped CStarAlgebra ComplexOrder

variable (A : Type*) [CStarAlgebra A]

/-- An actual unital representation on a nonzero finite-dimensional space. -/
structure Representation where
  dimension : ℕ
  positive_dimension : 0 < dimension
  hom : A →⋆ₐ[ℂ] CStarMatrix (Fin dimension) (Fin dimension) ℂ

/-- Finite-dimensional unital representations separate every nonzero element. -/
def IsRFD : Prop := ∀ a : A, a ≠ 0 → ∃ ρ : Representation A, ρ.hom a ≠ 0

/-- A sequence is separating after every finite deletion. -/
def SeparatingTails (ρ : ℕ → Representation A) : Prop :=
  ∀ (N : ℕ) (a : A), a ≠ 0 → ∃ n, N ≤ n ∧ (ρ n).hom a ≠ 0

variable {A}

theorem exists_separating_sequence [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (h : IsRFD A) :
    ∃ ρ : ℕ → Representation A, ∀ a : A, a ≠ 0 → ∃ n, (ρ n).hom a ≠ 0 := by
  obtain ⟨ρ₀, _⟩ := h 1 one_ne_zero
  let : Nonempty (Representation A) := ⟨ρ₀⟩
  let U : Representation A → Set A := fun ρ => {a | ρ.hom a ≠ 0}
  have hU : ∀ ρ, IsOpen (U ρ) := by
    intro ρ
    exact isOpen_ne_fun (map_continuous ρ.hom) continuous_const
  have hc : {a : A | a ≠ 0} ⊆ ⋃ ρ, U ρ := by
    intro a ha
    obtain ⟨ρ, hρ⟩ := h a ha
    exact Set.mem_iUnion.mpr ⟨ρ, hρ⟩
  obtain ⟨ρ, hρ⟩ :=
    (HereditarilyLindelofSpace.isLindelof {a : A | a ≠ 0}).indexed_countable_subcover U hU hc
  refine ⟨ρ, fun a ha => ?_⟩
  exact Set.mem_iUnion.mp (hρ ha)

/-- Repeating every selected representation infinitely often makes every tail
separating, with no homotopy assumption on any representation. -/
theorem exists_separating_tails [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (h : IsRFD A) : ∃ ρ : ℕ → Representation A, SeparatingTails A ρ := by
  obtain ⟨ρ, hρ⟩ := exists_separating_sequence h
  refine ⟨fun n => ρ (Nat.unpair n).1, ?_⟩
  intro N a ha
  obtain ⟨j, hj⟩ := hρ a ha
  refine ⟨Nat.pair j N, Nat.right_le_pair j N, ?_⟩
  change (ρ (Nat.unpair (Nat.pair j N)).1).hom a ≠ 0
  rw [Nat.unpair_pair]
  exact hj

theorem separatingTails_detects_equality {ρ : ℕ → Representation A}
    (hρ : SeparatingTails A ρ) (N : ℕ) {a b : A}
    (h : ∀ n, N ≤ n → (ρ n).hom a = (ρ n).hom b) : a = b := by
  by_contra hab
  obtain ⟨n, hn, hd⟩ := hρ N (a - b) (sub_ne_zero.mpr hab)
  exact hd (by rw [map_sub, h n hn, sub_self])

variable {B : Type*} [CStarAlgebra B]

/-- Residual finite dimensionality passes through an actual injective unital
star homomorphism, in particular to unital C⋆-subalgebras. -/
theorem of_injective (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f)
    (hB : IsRFD B) : IsRFD A := by
  intro a ha
  have hfa : f a ≠ 0 := fun hz => ha (hf (hz.trans (map_zero f).symm))
  obtain ⟨ρ, hρ⟩ := hB (f a) hfa
  exact ⟨⟨ρ.dimension, ρ.positive_dimension, ρ.hom.comp f⟩, hρ⟩

/-- Separation by finite matrix representations rules out one-sided inverses
at every matrix size, with no trace-existence assumption. -/
theorem isStablyFiniteRing (h : IsRFD A) : IsStablyFiniteRing A where
  isDedekindFiniteMonoid k := ⟨fun {x y} hxy => by
    ext i j
    by_contra hne
    obtain ⟨ρ, hρ⟩ := h ((y * x) i j - (1 : Matrix (Fin k) (Fin k) A) i j)
      (sub_ne_zero.mpr hne)
    let : IsStablyFiniteRing (CStarMatrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ) :=
      (RingEquiv.isStablyFiniteRing_iff CStarMatrix.ofMatrixRingEquiv).mp inferInstance
    let φ : Matrix (Fin k) (Fin k) A →+*
        Matrix (Fin k) (Fin k) (CStarMatrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ) :=
      ρ.hom.toAlgHom.toRingHom.mapMatrix
    have hp : φ x * φ y = 1 := by rw [← map_mul, hxy, map_one]
    have hp' : φ (y * x) = φ 1 := by
      rw [map_mul, map_one]
      exact mul_eq_one_symm hp
    have heq : ρ.hom ((y * x) i j) = ρ.hom ((1 : Matrix (Fin k) (Fin k) A) i j) :=
      congrFun (congrFun hp' i) j
    exact hρ (by rw [map_sub, heq, sub_self])⟩

/-- The concrete matrix-isometry convention used in the target follows from RFD. -/
theorem stablyFinite (h : IsRFD A) : StableFiniteness.IsStablyFinite A := by
  let := isStablyFiniteRing h
  intro k v hv
  exact mul_eq_one_symm hv

end Suzuki.ResidualRepresentations

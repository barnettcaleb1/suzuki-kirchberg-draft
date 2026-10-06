import Suzuki.CommonCorner
import Suzuki.StableFiniteness
import Mathlib.Tactic.NoncommRing

/-!
# Finiteness of concrete projection corners

The corner inclusion is nonunital. Adding the complement of the image of one
gives a multiplicative unital embedding, which is sufficient to pass direct
finiteness. Entrywise amplification proves the stable version.
-/

noncomputable section

namespace Suzuki.CornerFiniteness

section Rings

variable {R S : Type*} [Ring R] [Ring S]

/-- Extend a nonunital ring map on the multiplicative monoid by the complementary
idempotent. This construction is not claimed to be additive. -/
def complementHom (f : R →ₙ+* S) : R →* S where
  toFun a := f a + (1 - f 1)
  map_one' := by simp
  map_mul' a b := by
    have h₁ : f a * f 1 = f a := by rw [← map_mul, mul_one]
    have h₂ : f 1 * f b = f b := by rw [← map_mul, one_mul]
    have h₃ : f 1 * f 1 = f 1 := by rw [← map_mul, one_mul]
    rw [map_mul]
    noncomm_ring [h₁, h₂, h₃]

theorem complementHom_injective (f : R →ₙ+* S) (hf : Function.Injective f) :
    Function.Injective (complementHom f) := by
  intro a b h
  exact hf (add_right_cancel h)

/-- Direct finiteness passes through injective nonunital ring maps. -/
theorem dedekindFinite (f : R →ₙ+* S) (hf : Function.Injective f)
    [IsDedekindFiniteMonoid S] : IsDedekindFiniteMonoid R :=
  .of_injective (complementHom f) (complementHom_injective f hf)

/-- Entrywise nonunital ring map on square matrices. -/
def matrixMap (n : ℕ) (f : R →ₙ+* S) :
    Matrix (Fin n) (Fin n) R →ₙ+* Matrix (Fin n) (Fin n) S where
  toFun a := a.map f
  map_zero' := Matrix.map_zero _ (map_zero f)
  map_add' a b := Matrix.map_add f (map_add f) a b
  map_mul' _ _ := Matrix.map_mul

/-- Ring-theoretic stable finiteness passes through nonunital inclusions. -/
theorem stablyFiniteRing (f : R →ₙ+* S) (hf : Function.Injective f)
    [IsStablyFiniteRing S] : IsStablyFiniteRing R where
  isDedekindFiniteMonoid n :=
    dedekindFinite (matrixMap n f) (Matrix.map_injective hf)

variable [StarRing R] [StarRing S]

/-- The complement construction respects star when the original map does. -/
theorem complementHom_star (f : R →ₙ+* S) (hs : ∀ a, f (star a) = star (f a))
    (a : R) : complementHom f (star a) = star (complementHom f a) := by
  have h₁ : star (f 1) = f 1 := by rw [← hs, star_one]
  simp only [complementHom, MonoidHom.coe_mk, OneHom.coe_mk, hs, star_add,
    star_sub, star_one, h₁]

/-- Isometry finiteness passes through a nonunital injective star-preserving map. -/
theorem isometry_unitary (f : R →ₙ+* S) (hf : Function.Injective f)
    (hs : ∀ a, f (star a) = star (f a))
    (hS : ∀ v : S, star v * v = 1 → v * star v = 1)
    (v : R) (hv : star v * v = 1) : v * star v = 1 := by
  let g := complementHom f
  have hstar (a : R) : g (star a) = star (g a) := complementHom_star f hs a
  have hgv : star (g v) * g v = 1 := by
    rw [← hstar, ← map_mul, hv, map_one]
  apply complementHom_injective f hf
  change g (v * star v) = g 1
  rw [map_mul, hstar, hS (g v) hgv, map_one]

/-- Stable finiteness in the matrix-isometry convention also passes through
nonunital injective star-preserving ring maps. -/
theorem stablyFinite (f : R →ₙ+* S) (hf : Function.Injective f)
    (hs : ∀ a, f (star a) = star (f a)) (hS : StableFiniteness.IsStablyFinite S) :
    StableFiniteness.IsStablyFinite R := by
  intro n v hv
  apply isometry_unitary (matrixMap n f) (Matrix.map_injective hf) _ (hS n) v hv
  intro a
  ext i j
  exact hs (a j i)

end Rings

variable {A : Type*} [CStarAlgebra A] {p : A}

/-- Every projection corner of a stably finite ring is stably finite as a ring,
with the projection as its own unit. Fullness is unnecessary for this fact. -/
theorem corner_stablyFiniteRing (hp : IsStarProjection p) [IsStablyFiniteRing A] :
    IsStablyFiniteRing (CommonCorner.Corner hp) :=
  stablyFiniteRing (CommonCorner.inclusion hp : CommonCorner.Corner hp →ₙ+* A)
    Subtype.val_injective

/-- The resulting corner also satisfies the target's matrix-isometry convention. -/
theorem corner_stablyFinite (hp : IsStarProjection p) [IsStablyFiniteRing A] :
    StableFiniteness.IsStablyFinite (CommonCorner.Corner hp) := by
  let := corner_stablyFiniteRing hp
  intro n v hv
  exact mul_eq_one_symm hv

/-- A projection corner inherits exactly the target's matrix-isometry
finiteness hypothesis, without a stronger ring-theoretic assumption. -/
theorem corner_stablyFinite_of (hp : IsStarProjection p)
    (hA : StableFiniteness.IsStablyFinite A) :
    StableFiniteness.IsStablyFinite (CommonCorner.Corner hp) :=
  stablyFinite (CommonCorner.inclusion hp : CommonCorner.Corner hp →ₙ+* A)
    Subtype.val_injective (map_star (CommonCorner.inclusion hp)) hA

/-- Projection corners of separable C⋆-algebras are separable in their inherited
norm topology. -/
theorem corner_separable (hp : IsStarProjection p) [TopologicalSpace.SeparableSpace A] :
    TopologicalSpace.SeparableSpace (CommonCorner.Corner hp) := inferInstance

end Suzuki.CornerFiniteness

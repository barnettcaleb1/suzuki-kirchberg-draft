import Suzuki.CStarAmalgam
import Mathlib.RingTheory.Idempotents
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Concrete projection corners and finite frames

The corner below carries the inherited C⋆-norm and has unit `p`.
Its inclusion into the ambient algebra is a nonunital star homomorphism.
The finite-frame hypothesis is explicit; no derivation from fullness is
asserted in this file.
-/

noncomputable section

open scoped CStarAlgebra

namespace Suzuki.CommonCorner

universe u

variable {A : Type u} [CStarAlgebra A] {p : A}

/-- The concrete nonunital star subalgebra `pAp`. -/
def cornerSubalgebra (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ A where
  __ := NonUnitalRing.corner p
  smul_mem' c x hx := by
    rcases hx with ⟨a, rfl⟩
    exact ⟨c • a, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' {x} hx := by
    rcases hx with ⟨a, rfl⟩
    exact ⟨star a, by simp only [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc]⟩

/-- A projection corner, with its own unit `p`. -/
abbrev Corner (hp : IsStarProjection p) := cornerSubalgebra hp

instance cornerClosed (hp : IsStarProjection p) :
    IsClosed (cornerSubalgebra hp : Set A) := by
  have he : (cornerSubalgebra hp : Set A) = {a | p * a = a ∧ a * p = a} := by
    ext a
    exact Subsemigroup.mem_corner_iff hp.isIdempotentElem
  rw [he]
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

instance cornerNonUnitalCStarAlgebra (hp : IsStarProjection p) :
    NonUnitalCStarAlgebra (Corner hp) :=
  inferInstanceAs (NonUnitalCStarAlgebra (cornerSubalgebra hp))

instance cornerRing (hp : IsStarProjection p) : Ring (Corner hp) :=
  inferInstanceAs (Ring hp.isIdempotentElem.Corner)

instance cornerNormedRing (hp : IsStarProjection p) : NormedRing (Corner hp) where
  __ := cornerRing hp
  __ := (inferInstance : NonUnitalNormedRing (Corner hp))

instance cornerAlgebra (hp : IsStarProjection p) : Algebra ℂ (Corner hp) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance cornerNormedAlgebra (hp : IsStarProjection p) : NormedAlgebra ℂ (Corner hp) where
  norm_smul_le := norm_smul_le

instance cornerCStarAlgebra (hp : IsStarProjection p) : CStarAlgebra (Corner hp) where

instance cornerPartialOrder (hp : IsStarProjection p) : PartialOrder (Corner hp) :=
  CStarAlgebra.spectralOrder (Corner hp)

instance cornerStarOrderedRing (hp : IsStarProjection p) : StarOrderedRing (Corner hp) :=
  CStarAlgebra.spectralOrderedRing (Corner hp)

@[simp] theorem coe_one (hp : IsStarProjection p) : ((1 : Corner hp) : A) = p := rfl

@[simp] theorem coe_mul (hp : IsStarProjection p) (a b : Corner hp) :
    ((a * b : Corner hp) : A) = (a : A) * (b : A) := rfl

@[simp] theorem coe_star (hp : IsStarProjection p) (a : Corner hp) :
    ((star a : Corner hp) : A) = star (a : A) := rfl

theorem left_support (hp : IsStarProjection p) (a : Corner hp) : p * (a : A) = a :=
  ((Subsemigroup.mem_corner_iff hp.isIdempotentElem).mp a.property).1

theorem right_support (hp : IsStarProjection p) (a : Corner hp) : (a : A) * p = a :=
  ((Subsemigroup.mem_corner_iff hp.isIdempotentElem).mp a.property).2

/-- Ambient inclusion. It is deliberately nonunital: its value at one is `p`. -/
def inclusion (hp : IsStarProjection p) : Corner hp →⋆ₙₐ[ℂ] A :=
  NonUnitalStarSubalgebraClass.subtype (cornerSubalgebra hp)

@[simp] theorem inclusion_apply (hp : IsStarProjection p) (a : Corner hp) :
    inclusion hp a = (a : A) := rfl

theorem inclusion_isometry (hp : IsStarProjection p) : Isometry (inclusion hp) :=
  NonUnitalStarAlgHom.isometry (inclusion hp) Subtype.val_injective

@[simp] theorem coe_sum (hp : IsStarProjection p) {ι : Type*} (s : Finset ι)
    (f : ι → Corner hp) : ((∑ i ∈ s, f i : Corner hp) : A) = ∑ i ∈ s, (f i : A) :=
  map_sum (inclusion hp) _ _

/-- Make a corner element from its two support equations. -/
def ofSupport (hp : IsStarProjection p) (a : A) (hl : p * a = a) (hr : a * p = a) :
    Corner hp :=
  ⟨a, (Subsemigroup.mem_corner_iff hp.isIdempotentElem).mpr ⟨hl, hr⟩⟩

@[simp] theorem coe_ofSupport (hp : IsStarProjection p) (a : A)
    (hl : p * a = a) (hr : a * p = a) : (ofSupport hp a hl hr : A) = a := rfl

/-- Compression is linear, but is not claimed to be multiplicative. -/
def compress (hp : IsStarProjection p) : A →ₗ[ℂ] Corner hp where
  toFun a := ⟨p * a * p, a, rfl⟩
  map_add' a b := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c a := Subtype.ext (by simp)

@[simp] theorem coe_compress (hp : IsStarProjection p) (a : A) :
    (compress hp a : A) = p * a * p := rfl

@[simp] theorem compress_coe (hp : IsStarProjection p) (a : Corner hp) :
    compress hp (a : A) = a := Subtype.ext (by rw [coe_compress, left_support, right_support])

variable {B : Type u} [CStarAlgebra B] {q : B}

/-- A homomorphism carrying `p` to `q` restricts to a unital homomorphism of corners. -/
def map (hp : IsStarProjection p) (hq : IsStarProjection q)
    (f : A →⋆ₐ[ℂ] B) (hf : f p = q) : Corner hp →⋆ₐ[ℂ] Corner hq where
  toFun a := ofSupport hq (f a)
    (by rw [← hf, ← map_mul, left_support])
    (by rw [← hf, ← map_mul, right_support])
  map_one' := Subtype.ext hf
  map_mul' a b := Subtype.ext (map_mul f (a : A) (b : A))
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : A) (b : A))
  commutes' c := Subtype.ext (by
    change f (c • p) = c • q
    rw [map_smul, hf])
  map_star' a := Subtype.ext (map_star f (a : A))

@[simp] theorem coe_map (hp : IsStarProjection p) (hq : IsStarProjection q)
    (f : A →⋆ₐ[ℂ] B) (hf : f p = q) (a : Corner hp) :
    (map hp hq f hf a : B) = f a := rfl

theorem map_compress (hp : IsStarProjection p) (hq : IsStarProjection q)
    (f : A →⋆ₐ[ℂ] B) (hf : f p = q) (a : A) :
    map hp hq f hf (compress hp a) = compress hq (f a) := by
  apply Subtype.ext
  simp only [coe_map, coe_compress, map_mul, hf]

/-- The image of the ambient unit under a nonunital star homomorphism is a projection. -/
theorem image_one_projection (f : A →⋆ₙₐ[ℂ] B) : IsStarProjection (f 1) := by
  refine ⟨?_, ?_⟩
  · change f 1 * f 1 = f 1
    rw [← map_mul, one_mul]
  · change star (f 1) = f 1
    rw [← map_star, star_one]

/-- Regard a nonunital star homomorphism as a unital map to the corner cut out
by its image of one. -/
def toCornerHom (f : A →⋆ₙₐ[ℂ] B) (hq : IsStarProjection q) (hf : f 1 = q) :
    A →⋆ₐ[ℂ] Corner hq where
  toFun a := ofSupport hq (f a)
    (by rw [← hf, ← map_mul, one_mul])
    (by rw [← hf, ← map_mul, mul_one])
  map_one' := Subtype.ext hf
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f a b)
  map_mul' a b := Subtype.ext (map_mul f a b)
  commutes' c := Subtype.ext (by
    change f (algebraMap ℂ A c) = c • q
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hf])
  map_star' a := Subtype.ext (map_star f a)

@[simp] theorem coe_toCornerHom (f : A →⋆ₙₐ[ℂ] B) (hq : IsStarProjection q)
    (hf : f 1 = q) (a : A) : (toCornerHom f hq hf a : B) = f a := rfl

/-- The explicit finite-frame hypothesis used below. Its derivation from ideal
fullness of a projection is not part of this declaration. -/
structure Frame (hp : IsStarProjection p) (n : ℕ) where
  x : Fin n → A
  support : ∀ i, x i * p = x i
  total : ∑ i, x i * star (x i) = 1

namespace Frame

variable {hp : IsStarProjection p} {n : ℕ} (F : Frame hp n)

theorem star_support (i : Fin n) : p * star (F.x i) = star (F.x i) := by
  simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star (F.support i)

/-- Insert the finite resolution of the identity between any two elements. -/
theorem insert (a b : A) : a * b = ∑ i, (a * F.x i) * (star (F.x i) * b) := by
  calc a * b = a * (∑ i, F.x i * star (F.x i)) * b := by rw [F.total, mul_one]
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- Frame coefficients are genuine elements of the projection corner. -/
def coefficient (a : A) (i j : Fin n) : Corner hp :=
  ofSupport hp (star (F.x i) * a * F.x j)
    (by simp only [← mul_assoc, F.star_support])
    (by simp only [mul_assoc, F.support])

@[simp] theorem coe_coefficient (a : A) (i j : Fin n) :
    (F.coefficient a i j : A) = star (F.x i) * a * F.x j := rfl

/-- Reconstruction from all frame coefficients. -/
theorem reconstruction (a : A) :
    (∑ i, ∑ j, F.x i * (F.coefficient a i j : A) * star (F.x j)) = a := by
  simp only [coe_coefficient]
  calc
    _ = (∑ i, F.x i * star (F.x i)) * a * (∑ j, F.x j * star (F.x j)) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = a := by rw [F.total, one_mul, mul_one]

theorem coefficient_injective : Function.Injective F.coefficient := by
  intro a b hab
  rw [← F.reconstruction a, ← F.reconstruction b, hab]

/-- The frame coefficient map into matrices over the actual C⋆-corner.
This is nonunital because the image of `1` is the Gram projection. -/
def matrixHom : A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) (Corner hp) where
  toFun a := CStarMatrix.ofMatrix (F.coefficient a)
  map_zero' := by
    apply CStarMatrix.ext
    intro i j
    apply Subtype.ext
    change star (F.x i) * 0 * F.x j = 0
    simp
  map_add' a b := by
    apply CStarMatrix.ext
    intro i j
    apply Subtype.ext
    change star (F.x i) * (a + b) * F.x j =
      star (F.x i) * a * F.x j + star (F.x i) * b * F.x j
    simp only [mul_add, add_mul]
  map_smul' c a := by
    apply CStarMatrix.ext
    intro i j
    apply Subtype.ext
    change star (F.x i) * (c • a) * F.x j = c • (star (F.x i) * a * F.x j)
    simp only [mul_smul_comm, smul_mul_assoc]
  map_mul' a b := by
    ext i j
    change star (F.x i) * (a * b) * F.x j =
      ((∑ k, F.coefficient a i k * F.coefficient b k j : Corner hp) : A)
    rw [coe_sum]
    change star (F.x i) * (a * b) * F.x j =
      ∑ k, (star (F.x i) * a * F.x k) * (star (F.x k) * b * F.x j)
    simpa only [mul_assoc] using F.insert (star (F.x i) * a) (b * F.x j)
  map_star' a := by
    ext i j
    change star (F.x i) * star a * F.x j = star (star (F.x j) * a * F.x i)
    simp only [star_mul, star_star, mul_assoc]

theorem matrixHom_injective : Function.Injective F.matrixHom := by
  intro a b hab
  apply F.coefficient_injective
  exact congrArg CStarMatrix.ofMatrix.symm hab

theorem matrixHom_isometry : Isometry F.matrixHom :=
  NonUnitalStarAlgHom.isometry F.matrixHom F.matrixHom_injective

@[simp] theorem matrixHom_apply (a : A) (i j : Fin n) :
    F.matrixHom a i j = F.coefficient a i j := rfl

/-- The Gram matrix `R = (xᵢ⋆ xⱼ)`, with entries in `pAp`. -/
def gram : CStarMatrix (Fin n) (Fin n) (Corner hp) := F.matrixHom 1

@[simp] theorem coe_gram_apply (i j : Fin n) :
    (F.gram i j : A) = star (F.x i) * F.x j := by
  change star (F.x i) * 1 * F.x j = _
  rw [mul_one]

theorem gram_projection : IsStarProjection F.gram := by
  refine ⟨?_, ?_⟩
  · change F.matrixHom 1 * F.matrixHom 1 = F.matrixHom 1
    rw [← map_mul, one_mul]
  · change star (F.matrixHom 1) = F.matrixHom 1
    rw [← map_star, star_one]

/-- The frame representation lands in the Gram projection corner and is unital
for that corner's unit `R`. -/
def representation : A →⋆ₐ[ℂ] Corner F.gram_projection where
  toFun a := ofSupport F.gram_projection (F.matrixHom a)
    (by change F.matrixHom 1 * F.matrixHom a = _; rw [← map_mul, one_mul])
    (by change F.matrixHom a * F.matrixHom 1 = _; rw [← map_mul, mul_one])
  map_one' := rfl
  map_zero' := Subtype.ext (map_zero F.matrixHom)
  map_add' a b := Subtype.ext (map_add F.matrixHom a b)
  map_mul' a b := Subtype.ext (map_mul F.matrixHom a b)
  commutes' c := Subtype.ext (by
    change F.matrixHom (algebraMap ℂ A c) = c • F.matrixHom 1
    rw [Algebra.algebraMap_eq_smul_one, map_smul])
  map_star' a := Subtype.ext (map_star F.matrixHom a)

theorem representation_injective : Function.Injective F.representation := by
  intro a b hab
  exact F.matrixHom_injective (congrArg Subtype.val hab)

theorem representation_isometry : Isometry F.representation :=
  NonUnitalStarAlgHom.isometry F.representation F.representation_injective

/-- Reconstruction applied to an arbitrary matrix over `pAp`. -/
def expand (M : CStarMatrix (Fin n) (Fin n) (Corner hp)) : A :=
  ∑ i, ∑ j, F.x i * (M i j : A) * star (F.x j)

theorem matrixHom_expand (M : CStarMatrix (Fin n) (Fin n) (Corner hp)) :
    F.matrixHom (F.expand M) = F.gram * M * F.gram := by
  apply CStarMatrix.ext
  intro i j
  apply Subtype.ext
  simp only [matrixHom_apply, coe_coefficient, expand, CStarMatrix.mul_apply, coe_sum,
    coe_mul, coe_gram_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- The representation is onto the actual Gram projection corner. -/
theorem representation_surjective : Function.Surjective F.representation := by
  intro M
  refine ⟨F.expand (M : CStarMatrix (Fin n) (Fin n) (Corner hp)), ?_⟩
  apply Subtype.ext
  change F.matrixHom (F.expand _) = _
  rw [F.matrixHom_expand, left_support, right_support]

/-- The frame gives the concrete C⋆-algebra equivalence
`A ≃⋆ₐ R Mₙ(pAp) R`, with no abstract Morita predicate. -/
def equivalence : A ≃⋆ₐ[ℂ] Corner F.gram_projection :=
  StarAlgEquiv.ofBijective F.representation
    ⟨F.representation_injective, F.representation_surjective⟩

theorem equivalence_isometry : Isometry F.equivalence :=
  NonUnitalStarAlgHom.isometry F.equivalence F.equivalence.injective

/-- Amplification of a homomorphism from the corner by its frame coefficients. -/
def amplification {C : Type u} [CStarAlgebra C] (f : Corner hp →⋆ₐ[ℂ] C) :
    A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) C :=
  (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom).comp F.matrixHom

@[simp] theorem amplification_apply {C : Type u} [CStarAlgebra C]
    (f : Corner hp →⋆ₐ[ℂ] C) (a : A) (i j : Fin n) :
    F.amplification f a i j = f (F.coefficient a i j) := rfl

/-- Transport a frame along a unital star homomorphism. -/
def mapFrame (f : A →⋆ₐ[ℂ] B) (hq : IsStarProjection q) (hf : f p = q) : Frame hq n where
  x i := f (F.x i)
  support i := by rw [← hf, ← map_mul, F.support]
  total := by simpa only [map_sum, map_mul, map_star, map_one] using congrArg f F.total

theorem coefficient_map (f : A →⋆ₐ[ℂ] B) (hq : IsStarProjection q) (hf : f p = q)
    (a : A) (i j : Fin n) :
    (F.mapFrame f hq hf).coefficient (f a) i j =
      Suzuki.CommonCorner.map hp hq f hf (F.coefficient a i j) := by
  apply Subtype.ext
  change star (f (F.x i)) * f a * f (F.x j) = f (star (F.x i) * a * F.x j)
  simp only [map_mul, map_star]

theorem coefficient_mul (a b : A) (i j : Fin n) :
    F.coefficient (a * b) i j = ∑ k, F.coefficient a i k * F.coefficient b k j :=
  congrArg (fun M : CStarMatrix (Fin n) (Fin n) (Corner hp) => M i j)
    (map_mul F.matrixHom a b)

theorem coefficient_star (a : A) (i j : Fin n) :
    F.coefficient (star a) i j = star (F.coefficient a j i) :=
  congrArg (fun M : CStarMatrix (Fin n) (Fin n) (Corner hp) => M i j)
    (map_star F.matrixHom a)

theorem coefficient_add (a b : A) (i j : Fin n) :
    F.coefficient (a + b) i j = F.coefficient a i j + F.coefficient b i j :=
  congrArg (fun M : CStarMatrix (Fin n) (Fin n) (Corner hp) => M i j)
    (map_add F.matrixHom a b)

theorem coefficient_smul (c : ℂ) (a : A) (i j : Fin n) :
    F.coefficient (c • a) i j = c • F.coefficient a i j :=
  congrArg (fun M : CStarMatrix (Fin n) (Fin n) (Corner hp) => M i j)
    (map_smul F.matrixHom c a)

theorem coefficient_continuous (i j : Fin n) : Continuous (fun a => F.coefficient a i j) := by
  apply Continuous.subtype_mk
  exact (continuous_const.mul continuous_id).mul continuous_const

/-- The ambient subalgebra whose frame coefficients all belong to `S`. -/
def coefficientSubalgebra (S : StarSubalgebra ℂ (Corner hp))
    (h1 : ∀ i j, F.coefficient 1 i j ∈ S) : StarSubalgebra ℂ A where
  carrier := {a | ∀ i j, F.coefficient a i j ∈ S}
  mul_mem' ha hb i j := by
    rw [F.coefficient_mul]
    exact S.sum_mem fun k _ => S.mul_mem (ha i k) (hb k j)
  add_mem' ha hb i j := by
    rw [F.coefficient_add]
    exact S.add_mem (ha i j) (hb i j)
  algebraMap_mem' c i j := by
    rw [Algebra.algebraMap_eq_smul_one, F.coefficient_smul]
    exact S.smul_mem (h1 i j) c
  star_mem' ha i j := by
    rw [F.coefficient_star]
    exact star_mem (ha j i)

theorem coefficientSubalgebra_closed (S : StarSubalgebra ℂ (Corner hp))
    (h1 : ∀ i j, F.coefficient 1 i j ∈ S) (hS : IsClosed (S : Set (Corner hp))) :
    IsClosed (F.coefficientSubalgebra S h1 : Set A) := by
  change IsClosed {a | ∀ i j, F.coefficient a i j ∈ S}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    hS.preimage (F.coefficient_continuous i j)

/-- Reconstruct a corner element using compressed frame elements and its
coefficients. This is the finite-word insertion underlying corner generation. -/
theorem corner_reconstruction (a : Corner hp) :
    (∑ i, ∑ j, compress hp (F.x i) * F.coefficient (a : A) i j *
      star (compress hp (F.x j))) = a := by
  apply Subtype.ext
  simp only [coe_sum, coe_mul, coe_star, coe_compress, star_mul, hp.isSelfAdjoint.star_eq]
  have hs : ∀ i j,
      p * F.x i * p * (F.coefficient (a : A) i j : A) * (p * (star (F.x j) * p)) =
      p * (F.x i * (F.coefficient (a : A) i j : A) * star (F.x j)) * p := by
    intro i j
    calc
      _ = (p * F.x i) * (p * (F.coefficient (a : A) i j : A) * p) *
          (star (F.x j) * p) := by simp only [mul_assoc]
      _ = _ := by rw [left_support, right_support]; simp only [mul_assoc]
  simp_rw [hs]
  calc
    _ = p * (∑ i, ∑ j, F.x i * (F.coefficient (a : A) i j : A) * star (F.x j)) * p := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = (a : A) := by rw [F.reconstruction, left_support, right_support]

theorem compressed_total :
    (∑ i, compress hp (F.x i) * star (compress hp (F.x i))) = (1 : Corner hp) := by
  apply Subtype.ext
  simp only [coe_sum, coe_mul, coe_star, coe_compress, coe_one,
    star_mul, hp.isSelfAdjoint.star_eq]
  have he (i : Fin n) :
      p * F.x i * p * (p * (star (F.x i) * p)) = p * (F.x i * star (F.x i)) * p := by
    calc
      _ = p * (F.x i * p) * (p * star (F.x i)) * p := by simp only [mul_assoc]
      _ = _ := by rw [F.support, F.star_support]; simp only [mul_assoc]
  simp_rw [he]
  rw [← Finset.sum_mul, ← Finset.mul_sum, F.total, mul_one, hp.isIdempotentElem.eq]

theorem coefficient_projection (i j : Fin n) :
    F.coefficient p i j = star (compress hp (F.x i)) * compress hp (F.x j) := by
  apply Subtype.ext
  simp only [coe_coefficient, coe_mul, coe_star, coe_compress,
    star_mul, hp.isSelfAdjoint.star_eq]
  symm
  calc
    _ = (p * star (F.x i)) * p * (F.x j * p) := by
      simp only [mul_assoc, ← mul_assoc p p, hp.isIdempotentElem.eq]
    _ = _ := by rw [F.star_support, F.support]

theorem eq_top_of_coefficients (S : StarSubalgebra ℂ (Corner hp))
    (hcoeff : ∀ a i j, F.coefficient a i j ∈ S)
    (hx : ∀ i, compress hp (F.x i) ∈ S) : S = ⊤ := by
  apply top_unique
  intro a _
  rw [← F.corner_reconstruction a]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ =>
    S.mul_mem (S.mul_mem (hx i) (hcoeff (a : A) i j)) (star_mem (s := S) (hx j))

end Frame

section MatrixCompression

variable {C : Type u} [CStarAlgebra C] {n : ℕ}

/-- Compression by a row coisometry, on a corner whose image projection is
the associated column-row product. The result is a genuine star homomorphism
into one-by-one matrices over the target algebra. -/
def rowCompression (hp : IsStarProjection p)
    (f : A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) C)
    (v : Matrix Unit (Fin n) C)
    (hv : v * v.conjTranspose = 1)
    (hfp : f p = CStarMatrix.ofMatrix (v.conjTranspose * v)) :
    Corner hp →⋆ₐ[ℂ] CStarMatrix Unit Unit C where
  toFun a := CStarMatrix.ofMatrix (v * CStarMatrix.ofMatrix.symm (f (a : A)) * v.conjTranspose)
  map_zero' := by
    change CStarMatrix.ofMatrix (v * CStarMatrix.ofMatrix.symm (f 0) * v.conjTranspose) = 0
    rw [map_zero]
    change v * (0 : Matrix (Fin n) (Fin n) C) * v.conjTranspose = 0
    simp
  map_add' a b := by
    change v * CStarMatrix.ofMatrix.symm (f ((a : A) + (b : A))) * v.conjTranspose = _
    rw [map_add]
    change v * (CStarMatrix.ofMatrix.symm (f (a : A)) + CStarMatrix.ofMatrix.symm (f (b : A))) * v.conjTranspose = _
    simp only [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_mul' a b := by
    change v * CStarMatrix.ofMatrix.symm (f ((a : A) * (b : A))) * v.conjTranspose = _
    rw [map_mul]
    change v * (CStarMatrix.ofMatrix.symm (f (a : A)) * CStarMatrix.ofMatrix.symm (f (b : A))) * v.conjTranspose =
      (v * CStarMatrix.ofMatrix.symm (f (a : A)) * v.conjTranspose) *
      (v * CStarMatrix.ofMatrix.symm (f (b : A)) * v.conjTranspose)
    have hb : CStarMatrix.ofMatrix.symm (f p) * CStarMatrix.ofMatrix.symm (f (b : A)) = CStarMatrix.ofMatrix.symm (f (b : A)) := by
      change f p * f (b : A) = f (b : A)
      rw [← map_mul, left_support]
    calc
      _ = v * (CStarMatrix.ofMatrix.symm (f (a : A)) * (CStarMatrix.ofMatrix.symm (f p) * CStarMatrix.ofMatrix.symm (f (b : A)))) *
          v.conjTranspose := by rw [hb]
      _ = _ := by
        rw [hfp]
        change v * (CStarMatrix.ofMatrix.symm (f (a : A)) *
          ((v.conjTranspose * v) * CStarMatrix.ofMatrix.symm (f (b : A)))) * v.conjTranspose = _
        simp only [Matrix.mul_assoc]
  map_one' := by
    change v * CStarMatrix.ofMatrix.symm (f p) * v.conjTranspose = 1
    rw [hfp]
    change v * (v.conjTranspose * v) * v.conjTranspose = 1
    calc
      _ = (v * v.conjTranspose) * (v * v.conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hv, one_mul]
  commutes' c := by
    change v * CStarMatrix.ofMatrix.symm (f (c • p)) * v.conjTranspose = _
    rw [map_smul, hfp]
    rw [Algebra.algebraMap_eq_smul_one]
    change v * (c • (v.conjTranspose * v)) * v.conjTranspose = c • (1 : Matrix Unit Unit C)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc
      _ = (v * v.conjTranspose) * (v * v.conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hv, one_mul]
  map_star' a := by
    change v * CStarMatrix.ofMatrix.symm (f (star (a : A))) * v.conjTranspose = _
    rw [map_star]
    change v * (CStarMatrix.ofMatrix.symm (f (a : A))).conjTranspose * v.conjTranspose =
      (v * CStarMatrix.ofMatrix.symm (f (a : A)) * v.conjTranspose).conjTranspose
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end MatrixCompression

section CommonAmalgam

variable {D A₀ A₁ P : Type u}
variable [CStarAlgebra D] [CStarAlgebra A₀] [CStarAlgebra A₁] [CStarAlgebra P]
variable {i₀ : D →⋆ₐ[ℂ] A₀} {i₁ : D →⋆ₐ[ℂ] A₁}
variable {j₀ : A₀ →⋆ₐ[ℂ] P} {j₁ : A₁ →⋆ₐ[ℂ] P}
variable (h : CStarAmalgam.IsFullAmalgam i₀ i₁ j₀ j₁)
variable {pD : D} {p₀ : A₀} {p₁ : A₁} {pP : P}
variable (hpD : IsStarProjection pD) (hp₀ : IsStarProjection p₀)
  (hp₁ : IsStarProjection p₁) (hpP : IsStarProjection pP)
variable (hi₀ : i₀ pD = p₀) (hi₁ : i₁ pD = p₁)
  (hj₀ : j₀ p₀ = pP) (hj₁ : j₁ p₁ = pP)

include h hi₀ hi₁ in
/-- The factor corners generate the common corner as a closed star algebra,
provided a finite frame is supplied in the common algebra. This proves the
generation step in the common-full-corner argument for genuine C⋆-algebras. -/
theorem corner_eq_top_of_isClosed {n : ℕ} (F : Frame hpD n)
    (S : StarSubalgebra ℂ (Corner hpP)) (hS : IsClosed (S : Set (Corner hpP)))
    (h₀ : ∀ a, map hp₀ hpP j₀ hj₀ a ∈ S)
    (h₁ : ∀ a, map hp₁ hpP j₁ hj₁ a ∈ S) : S = ⊤ := by
  let FP : Frame hpP n := F.mapFrame (j₀.comp i₀) hpP (by simp [hi₀, hj₀])
  let F₀ : Frame hp₀ n := F.mapFrame i₀ hp₀ hi₀
  let F₁ : Frame hp₁ n := F.mapFrame i₁ hp₁ hi₁
  have hc₀ (a : A₀) (r s : Fin n) :
      FP.coefficient (j₀ a) r s = map hp₀ hpP j₀ hj₀ (F₀.coefficient a r s) := by
    apply Subtype.ext
    change star (j₀ (i₀ (F.x r))) * j₀ a * j₀ (i₀ (F.x s)) =
      j₀ (star (i₀ (F.x r)) * a * i₀ (F.x s))
    simp only [map_mul, map_star]
  have hc₁ (a : A₁) (r s : Fin n) :
      FP.coefficient (j₁ a) r s = map hp₁ hpP j₁ hj₁ (F₁.coefficient a r s) := by
    have hx (k : Fin n) : j₀ (i₀ (F.x k)) = j₁ (i₁ (F.x k)) :=
      DFunLike.congr_fun h.commutes (F.x k)
    apply Subtype.ext
    change star (j₀ (i₀ (F.x r))) * j₁ a * j₀ (i₀ (F.x s)) =
      j₁ (star (i₁ (F.x r)) * a * i₁ (F.x s))
    simp only [hx, map_mul, map_star]
  have h1 : ∀ r s, FP.coefficient 1 r s ∈ S := by
    intro r s
    have ht : FP.coefficient (j₀ 1) r s ∈ S := by
      rw [hc₀]
      exact h₀ _
    simpa only [map_one] using ht
  have hT : FP.coefficientSubalgebra S h1 = ⊤ := by
    apply h.eq_top_of_isClosed _ (FP.coefficientSubalgebra_closed S h1 hS)
    · intro a r s
      rw [hc₀]
      exact h₀ _
    · intro a r s
      rw [hc₁]
      exact h₁ _
  apply FP.eq_top_of_coefficients S
  · intro a r s
    have ha : a ∈ FP.coefficientSubalgebra S h1 := by rw [hT]; trivial
    exact ha r s
  · intro r
    change compress hpP (j₀ (i₀ (F.x r))) ∈ S
    rw [← map_compress hp₀ hpP j₀ hj₀]
    exact h₀ _

include h hi₀ hi₁ in
/-- The uniqueness half of the common-corner universal property: maps from
`pPp` are determined by their restrictions to the two factor corners. -/
theorem corner_hom_ext {n : ℕ} (F : Frame hpD n) {C : Type u} [CStarAlgebra C]
    {φ ψ : Corner hpP →⋆ₐ[ℂ] C}
    (h₀ : φ.comp (map hp₀ hpP j₀ hj₀) = ψ.comp (map hp₀ hpP j₀ hj₀))
    (h₁ : φ.comp (map hp₁ hpP j₁ hj₁) = ψ.comp (map hp₁ hpP j₁ hj₁)) : φ = ψ := by
  let S : StarSubalgebra ℂ (Corner hpP) := StarAlgHom.equalizer φ ψ
  have hS : S = ⊤ := corner_eq_top_of_isClosed h hpD hp₀ hp₁ hpP hi₀ hi₁ hj₀ hj₁ F S
    (isClosed_eq (map_continuous φ) (map_continuous ψ))
    (fun a => DFunLike.congr_fun h₀ a) (fun a => DFunLike.congr_fun h₁ a)
  apply StarAlgHom.ext
  intro a
  have ha : a ∈ S := by rw [hS]; trivial
  exact ha

include h in
/-- Compatible homomorphisms on the two corners have a common amplification to
the ambient full amalgam. The target is the concrete Gram projection corner
in matrices over `C`, and the conclusion specifies every matrix entry. -/
theorem matrix_extension {n : ℕ} (F : Frame hpD n)
    {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (f₀ : Corner hp₀ →⋆ₐ[ℂ] C) (f₁ : Corner hp₁ →⋆ₐ[ℂ] C)
    (hf : f₀.comp (map hpD hp₀ i₀ hi₀) = f₁.comp (map hpD hp₁ i₁ hi₁)) :
    ∃ (R : CStarMatrix (Fin n) (Fin n) C) (hR : IsStarProjection R)
      (Ψ : P →⋆ₐ[ℂ] Corner hR),
      (∀ a r s, (Ψ (j₀ a) : CStarMatrix (Fin n) (Fin n) C) r s =
        f₀ ((F.mapFrame i₀ hp₀ hi₀).coefficient a r s)) ∧
      (∀ a r s, (Ψ (j₁ a) : CStarMatrix (Fin n) (Fin n) C) r s =
        f₁ ((F.mapFrame i₁ hp₁ hi₁).coefficient a r s)) := by
  let F₀ := F.mapFrame i₀ hp₀ hi₀
  let F₁ := F.mapFrame i₁ hp₁ hi₁
  let G₀ := F₀.amplification f₀
  let G₁ := F₁.amplification f₁
  have hc (d : D) : G₀ (i₀ d) = G₁ (i₁ d) := by
    apply CStarMatrix.ext
    intro r s
    change f₀ (F₀.coefficient (i₀ d) r s) = f₁ (F₁.coefficient (i₁ d) r s)
    rw [F.coefficient_map, F.coefficient_map]
    exact DFunLike.congr_fun hf (F.coefficient d r s)
  let R := G₀ 1
  have hR : IsStarProjection R := image_one_projection G₀
  have hG₁ : G₁ 1 = R := by simpa only [map_one] using (hc 1).symm
  let g₀ := toCornerHom G₀ hR rfl
  let g₁ := toCornerHom G₁ hR hG₁
  have hg : g₀.comp i₀ = g₁.comp i₁ := by
    apply StarAlgHom.ext
    intro d
    exact Subtype.ext (hc d)
  refine ⟨R, hR, h.lift g₀ g₁ hg, ?_, ?_⟩
  · intro a r s
    have ha : h.lift g₀ g₁ hg (j₀ a) = g₀ a :=
      DFunLike.congr_fun (h.lift_left g₀ g₁ hg) a
    rw [ha]
    rfl
  · intro a r s
    have ha : h.lift g₀ g₁ hg (j₁ a) = g₁ a :=
      DFunLike.congr_fun (h.lift_right g₀ g₁ hg) a
    rw [ha]
    rfl

include h in
/-- The common-corner universal property under the explicit finite-frame
hypothesis. The algebras and all target homomorphisms are genuine C⋆-algebraic
ones; no existence of a corner-amalgam candidate is assumed. -/
theorem isFullAmalgam_of_frame {n : ℕ} (F : Frame hpD n) :
    CStarAmalgam.IsFullAmalgam
      (map hpD hp₀ i₀ hi₀) (map hpD hp₁ i₁ hi₁)
      (map hp₀ hpP j₀ hj₀) (map hp₁ hpP j₁ hj₁) := by
  refine ⟨?_, ?_⟩
  · apply StarAlgHom.ext
    intro d
    exact Subtype.ext (DFunLike.congr_fun h.commutes (d : D))
  · intro C instC f₀ f₁ hf
    let : PartialOrder C := CStarAlgebra.spectralOrder C
    let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
    let fD := f₀.comp (map hpD hp₀ i₀ hi₀)
    let F₀ := F.mapFrame i₀ hp₀ hi₀
    let F₁ := F.mapFrame i₁ hp₁ hi₁
    obtain ⟨R, hR, Ψ, hΨ₀, hΨ₁⟩ := matrix_extension h hpD hp₀ hp₁ hi₀ hi₁ F f₀ f₁ hf
    let G : P →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) C :=
      (inclusion hR).comp Ψ.toNonUnitalStarAlgHom
    let v : Matrix Unit (Fin n) C := fun _ r => fD (compress hpD (F.x r))
    have hv : v * v.conjTranspose = 1 := by
      ext a b
      have ht := congrArg fD F.compressed_total
      change (∑ r, fD (compress hpD (F.x r)) * star (fD (compress hpD (F.x r)))) =
        if a = b then 1 else 0
      rw [if_pos (Subsingleton.elim a b)]
      simpa only [map_sum, map_mul, map_star, map_one] using ht
    have hfp : G pP = CStarMatrix.ofMatrix (v.conjTranspose * v) := by
      apply CStarMatrix.ext
      intro r s
      change (Ψ pP : CStarMatrix (Fin n) (Fin n) C) r s = _
      rw [← hj₀, hΨ₀]
      have hc := F.coefficient_map i₀ hp₀ hi₀ pD r s
      rw [hi₀] at hc
      rw [hc, F.coefficient_projection]
      change fD (star (compress hpD (F.x r)) * compress hpD (F.x s)) = _
      change fD (star (compress hpD (F.x r)) * compress hpD (F.x s)) =
        ∑ _ : Unit, star (fD (compress hpD (F.x r))) * fD (compress hpD (F.x s))
      simp only [map_mul, map_star, Finset.univ_unique, Finset.sum_singleton]
    let χ := rowCompression hpP G v hv hfp
    let φ : Corner hpP →⋆ₐ[ℂ] C := (CStarMatrix.toOneByOne Unit ℂ C).symm.toStarAlgHom.comp χ
    have hv₀ (r : Fin n) : v () r = f₀ (compress hp₀ (F₀.x r)) := by
      change f₀ (map hpD hp₀ i₀ hi₀ (compress hpD (F.x r))) = _
      rw [map_compress]
      rfl
    have hv₁ (r : Fin n) : v () r = f₁ (compress hp₁ (F₁.x r)) := by
      change (f₀.comp (map hpD hp₀ i₀ hi₀)) (compress hpD (F.x r)) = _
      rw [hf]
      change f₁ (map hpD hp₁ i₁ hi₁ (compress hpD (F.x r))) = _
      rw [map_compress]
      rfl
    have hφ₀ : φ.comp (map hp₀ hpP j₀ hj₀) = f₀ := by
      apply StarAlgHom.ext
      intro a
      change (v * CStarMatrix.ofMatrix.symm (G (j₀ (a : A₀))) * v.conjTranspose) () () = f₀ a
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
      change (∑ s, ∑ r, v () r * (Ψ (j₀ (a : A₀)) : CStarMatrix (Fin n) (Fin n) C) r s * star (v () s)) = f₀ a
      simp_rw [hΨ₀, hv₀]
      rw [Finset.sum_comm]
      have ht := congrArg f₀ (F₀.corner_reconstruction a)
      simpa only [map_sum, map_mul, map_star] using ht
    have hφ₁ : φ.comp (map hp₁ hpP j₁ hj₁) = f₁ := by
      apply StarAlgHom.ext
      intro a
      change (v * CStarMatrix.ofMatrix.symm (G (j₁ (a : A₁))) * v.conjTranspose) () () = f₁ a
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
      change (∑ s, ∑ r, v () r * (Ψ (j₁ (a : A₁)) : CStarMatrix (Fin n) (Fin n) C) r s * star (v () s)) = f₁ a
      simp_rw [hΨ₁, hv₁]
      rw [Finset.sum_comm]
      have ht := congrArg f₁ (F₁.corner_reconstruction a)
      simpa only [map_sum, map_mul, map_star] using ht
    refine ⟨φ, ⟨hφ₀, hφ₁⟩, ?_⟩
    intro ψ hψ
    apply corner_hom_ext h hpD hp₀ hp₁ hpP hi₀ hi₁ hj₀ hj₁ F
    · exact hψ.1.trans hφ₀.symm
    · exact hψ.2.trans hφ₁.symm

end CommonAmalgam

end Suzuki.CommonCorner

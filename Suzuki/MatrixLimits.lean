import Suzuki.LimitFiniteness
import Suzuki.ResidualRepresentations

/-!
# Matrix finiteness of injective sequential limits

Finite families of algebraic limit elements come from one common stage.
Entrywise density then gives simultaneous matrix approximations in the C⋆-norm.
-/

noncomputable section

namespace Suzuki.MatrixLimits

open InductiveAmalgam SequentialCStarLimit
open scoped CStarAlgebra ComplexOrder

universe u

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable (k : Type*) [Fintype k] [DecidableEq k]

/-- The unital entrywise amplification of an actual star homomorphism. -/
def matrixHom (f : A →⋆ₐ[ℂ] B) : CStarMatrix k k A →⋆ₐ[ℂ] CStarMatrix k k B where
  __ := CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom
  map_one' := Matrix.map_one _ (map_zero f) (map_one f)
  commutes' z := by
    ext i j
    change f (if i = j then algebraMap ℂ A z else 0) =
      if i = j then algebraMap ℂ B z else 0
    split_ifs
    · exact f.commutes z
    · exact map_zero f

@[simp] theorem matrixHom_apply (f : A →⋆ₐ[ℂ] B) (x : CStarMatrix k k A) (i j : k) :
    matrixHom k f x i j = f (x i j) := rfl

theorem matrixHom_injective (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f) :
    Function.Injective (matrixHom k f) := by
  intro x y h
  ext i j
  exact hf (congrFun (congrFun h i) j)

variable (S : System.{u}) [Fact (∀ n, Function.Injective (S.step n))]

omit [Fact (∀ n, Function.Injective (S.step n))] in
/-- Every finite family in the algebraic limit can be represented at one stage. -/
theorem finite_common_stage {ι : Type*} [Fintype ι]
    (a : ι → DirectedCStarLimit.Algebraic S.obj (transition S)) :
    ∃ n, ∃ b : ι → S.obj n, ∀ i, a i = ⟦⟨n, b i⟩⟧ := by
  classical
  choose n b hb using (fun i => DirectLimit.exists_eq_mk (transition S) (a i))
  let N := Finset.univ.sup n
  have hn (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N, fun i => transition S (n i) N (hn i) (b i), ?_⟩
  intro i
  exact (hb i).trans (DirectLimit.mk_apply (n i) N (b i) (hn i)).symm

local instance stageOrder (n : ℕ) : PartialOrder (S.obj n) :=
  CStarAlgebra.spectralOrder (S.obj n)

local instance stageStarOrderedRing (n : ℕ) : StarOrderedRing (S.obj n) :=
  CStarAlgebra.spectralOrderedRing (S.obj n)

local instance limitOrder : PartialOrder (Limit S) := CStarAlgebra.spectralOrder (Limit S)

local instance limitStarOrderedRing : StarOrderedRing (Limit S) :=
  CStarAlgebra.spectralOrderedRing (Limit S)

/-- Pairs of matrices can be approximated by matrices over a common stage. -/
theorem dense_matrix_stage_pairs : DenseRange
    (fun p : Σ n, CStarMatrix k k (S.obj n) × CStarMatrix k k (S.obj n) =>
      (matrixHom k (stage S p.1) p.2.1, matrixHom k (stage S p.1) p.2.2)) := by
  have hdM : DenseRange (fun a : Matrix k k
      (DirectedCStarLimit.Algebraic S.obj (transition S)) =>
      CStarMatrix.ofMatrix (fun i j => (a i j : Limit S))) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => UniformSpace.Completion.denseRange_coe
  apply (hdM.prodMap hdM).mono
  rintro z ⟨⟨a, b⟩, rfl⟩
  let c : Bool × k × k → DirectedCStarLimit.Algebraic S.obj (transition S) :=
    fun t => if t.1 then a t.2.1 t.2.2 else b t.2.1 t.2.2
  obtain ⟨n, d, hd⟩ := finite_common_stage S c
  refine ⟨⟨n, CStarMatrix.ofMatrix (fun i j => d (true, i, j)),
    CStarMatrix.ofMatrix (fun i j => d (false, i, j))⟩, ?_⟩
  apply Prod.ext
  · ext i j
    exact congrArg (fun x : DirectedCStarLimit.Algebraic S.obj (transition S) =>
      (x : Limit S)) (hd (true, i, j)).symm
  · ext i j
    exact congrArg (fun x : DirectedCStarLimit.Algebraic S.obj (transition S) =>
      (x : Limit S)) (hd (false, i, j)).symm

/-- Ring-theoretic stable finiteness of the stages excludes one-sided inverses
in every matrix algebra over the completed limit. -/
theorem matrixDedekindFinite [∀ n, IsStablyFiniteRing (S.obj n)] :
    IsDedekindFiniteMonoid (CStarMatrix k k (Limit S)) := by
  let : ∀ n, IsStablyFiniteRing (CStarMatrix k k (S.obj n)) := fun _ =>
    (RingEquiv.isStablyFiniteRing_iff CStarMatrix.ofMatrixRingEquiv).mp inferInstance
  exact LimitFiniteness.of_dense_pairs (fun n => CStarMatrix k k (S.obj n))
    (fun n => matrixHom k (stage S n))
    (fun n => matrixHom_injective k (stage S n) (stage_injective S n))
    (dense_matrix_stage_pairs k S)

theorem isStablyFiniteRing [∀ n, IsStablyFiniteRing (S.obj n)] :
    IsStablyFiniteRing (Limit S) := by
  refine ⟨fun n => ?_⟩
  let := matrixDedekindFinite (Fin n) S
  exact IsDedekindFiniteMonoid.of_injective
    (CStarMatrix.ofMatrixRingEquiv : Matrix (Fin n) (Fin n) (Limit S) ≃+* _)
    CStarMatrix.ofMatrixRingEquiv.injective

/-- In particular, an injective limit of actual RFD algebras is stably finite
in the target's matrix-isometry convention. No limit trace is assumed. -/
theorem stablyFinite_of_rfd (h : ∀ n, ResidualRepresentations.IsRFD (S.obj n)) :
    StableFiniteness.IsStablyFinite (Limit S) := by
  let : ∀ n, IsStablyFiniteRing (S.obj n) := fun n => ResidualRepresentations.isStablyFiniteRing (h n)
  let := isStablyFiniteRing S
  intro n v hv
  exact mul_eq_one_symm hv

end Suzuki.MatrixLimits

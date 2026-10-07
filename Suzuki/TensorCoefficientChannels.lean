import Suzuki.OrthogonalChannels
import Suzuki.CStarAmalgam
import Suzuki.GraphCommonInclusions
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual coefficient channels, conditional on standard spatial tensor theory

`Spatial` contains standard tensor-product support for actual complex C⋆-algebras.
It contains no manuscript-specific channel or amalgam conclusion. The object,
maps, density and faithfulness laws are external inputs, intended as the minimal
tensor product. `MaximalOn` is the ordinary maximal universal property on that
same product, available when the second factor is nuclear (min = max).

`ScalarChannels` is LOCAL scalar construction data, not a published input and
not an acceptable hypothesis of the final main theorem. It must be instantiated
from the orthogonal finite diagrams and scalar graph product maps. Given it,
the actual coefficient maps and their properties are constructed below.

Matrices use `ULift (Fin q)` as index set, so their algebras and all constructions
stay in the universe of the coefficient. This is a reindexing of M_q, not an
infinite amplification. `graph_isFullAmalgam` transports the concrete scalar
graph construction using its extension theorem for Type-u targets. Binding the
recursive scalar channel sequence to these lifted stages remains an assembly obligation.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace Suzuki.TensorCoefficientChannels
universe u

namespace UniverseLift
universe v
variable {A : Type v}

instance [Star A] : Star (ULift.{u} A) := ⟨fun a => ⟨star a.down⟩⟩

instance [NonUnitalNonAssocSemiring A] [StarRing A] : StarRing (ULift.{u} A) :=
  Function.Injective.starRing ULift.down ULift.down_injective (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance [CStarAlgebra A] : CStarAlgebra (ULift.{u} A) where
  norm_mul_self_le a := CStarRing.norm_mul_self_le a.down
  star_smul z a := by
    apply ULift.down_injective
    exact star_smul z a.down

/-- Exact actual C⋆-algebra equivalence to the original scalar algebra. This
changes only the carrier universe, not multiplication, involution or norm. -/
def equiv (A : Type v) [CStarAlgebra A] : ULift.{u} A ≃⋆ₐ[ℂ] A :=
  { (ULift.algEquiv (R := ℂ) (A := A)) with map_star' := fun _ => rfl, map_smul' := fun _ _ => rfl }

theorem equiv_isometry (A : Type v) [CStarAlgebra A] :
    Isometry (equiv.{u} A) := NonUnitalStarAlgHom.isometry _ (equiv A).injective

end UniverseLift

structure Algebra where
  Carrier : Type u
  algebra : CStarAlgebra Carrier

attribute [instance] Algebra.algebra
instance : CoeSort Algebra.{u} (Type u) := ⟨Algebra.Carrier⟩

noncomputable instance (A : Algebra) : PartialOrder A := CStarAlgebra.spectralOrder A
instance (A : Algebra) : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

namespace UniverseLift

def algebra (A : Type) [CStarAlgebra A] : Algebra.{u} := ⟨ULift.{u} A, inferInstance⟩

def map {A B : Type} [CStarAlgebra A] [CStarAlgebra B] (f : A →⋆ₐ[ℂ] B) :
    algebra.{u} A →⋆ₐ[ℂ] algebra.{u} B :=
  (equiv B).symm.toStarAlgHom.comp (f.comp (equiv A).toStarAlgHom)

def nonUnitalMap {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) : algebra.{u} A →⋆ₙₐ[ℂ] algebra.{u} B :=
  (equiv B).symm.toStarAlgHom.toNonUnitalStarAlgHom.comp
    (f.comp (equiv A).toStarAlgHom.toNonUnitalStarAlgHom)

@[simp] theorem map_up {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (a : A) : map.{u} f (ULift.up a) = ULift.up (f a) := rfl

@[simp] theorem nonUnitalMap_up {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) (a : A) : nonUnitalMap.{u} f (ULift.up a) = ULift.up (f a) := rfl

theorem nonUnitalMap_injective {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) (hf : Function.Injective f) :
    Function.Injective (nonUnitalMap.{u} f) :=
  (equiv B).symm.injective.comp (hf.comp (equiv A).injective)

/-- Literal scalar squares survive the universe transport. -/
theorem map_square {A B C D : Type}
    [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C] [CStarAlgebra D]
    (f : A →⋆ₐ[ℂ] B) (g : C →⋆ₐ[ℂ] D) (i : A →⋆ₐ[ℂ] C) (j : B →⋆ₐ[ℂ] D)
    (h : g.comp i = j.comp f) : (map.{u} g).comp (map i) = (map j).comp (map f) := by
  apply StarAlgHom.ext
  intro x
  exact congrArg ULift.up (DFunLike.congr_fun h x.down)

/-- The required universe adapter uses an extension property already quantified
over the LARGE target universe. A Type-0-only full-amalgam hypothesis is not
sufficient for this lemma and is never promoted silently. -/
theorem fullAmalgamOfSmallInputs {D A₀ A₁ P : Type}
    [CStarAlgebra D] [CStarAlgebra A₀] [CStarAlgebra A₁] [CStarAlgebra P]
    (i₀ : D →⋆ₐ[ℂ] A₀) (i₁ : D →⋆ₐ[ℂ] A₁)
    (j₀ : A₀ →⋆ₐ[ℂ] P) (j₁ : A₁ →⋆ₐ[ℂ] P)
    (hc : j₀.comp i₀ = j₁.comp i₁)
    (hex : ∀ {C : Type u} [CStarAlgebra C]
      (f₀ : A₀ →⋆ₐ[ℂ] C) (f₁ : A₁ →⋆ₐ[ℂ] C), f₀.comp i₀ = f₁.comp i₁ →
        ∃! φ : P →⋆ₐ[ℂ] C, φ.comp j₀ = f₀ ∧ φ.comp j₁ = f₁) :
    CStarAmalgam.IsFullAmalgam (map.{u} i₀) (map.{u} i₁) (map.{u} j₀) (map.{u} j₁) where
  commutes := by
    apply StarAlgHom.ext
    intro x
    exact congrArg ULift.up (DFunLike.congr_fun hc x.down)
  extension f₀ f₁ hf := by
    let g₀ := f₀.comp (equiv A₀).symm.toStarAlgHom
    let g₁ := f₁.comp (equiv A₁).symm.toStarAlgHom
    have hg : g₀.comp i₀ = g₁.comp i₁ := by
      apply StarAlgHom.ext
      intro d
      exact DFunLike.congr_fun hf (ULift.up d)
    obtain ⟨φ, hφ, hu⟩ := hex g₀ g₁ hg
    let φ' := φ.comp (equiv P).toStarAlgHom
    refine ⟨φ', ⟨?_, ?_⟩, ?_⟩
    · apply StarAlgHom.ext
      intro x
      exact DFunLike.congr_fun hφ.1 x.down
    · apply StarAlgHom.ext
      intro x
      exact DFunLike.congr_fun hφ.2 x.down
    · intro ψ hψ
      have hψ' : ψ.comp (equiv P).symm.toStarAlgHom = φ := by
        apply hu
        constructor
        · apply StarAlgHom.ext
          intro x
          exact DFunLike.congr_fun hψ.1 (ULift.up x)
        · apply StarAlgHom.ext
          intro x
          exact DFunLike.congr_fun hψ.2 (ULift.up x)
      apply StarAlgHom.ext
      intro x
      exact DFunLike.congr_fun hψ' x.down

end UniverseLift

section GraphUniverse
open WeightedGraphAmalgam GraphCornerIdentification
variable {V Edge : Type} [Fintype V] [Fintype Edge] [DecidableEq V] [DecidableEq Edge]
    (source target : Edge → V) (k l : V → ℕ)
    (hk : ∀ v, 0 < k v) (hl : ∀ v, 0 < l v) (hns : GraphRelations.NoSinks source)

local instance : PartialOrder (GraphUniversal.Algebra.{u} source target) :=
  CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (GraphUniversal.Algebra.{u} source target) :=
  CStarAlgebra.spectralOrderedRing _

include hl

/-- Actual scalar graph amalgam in the coefficient's universe. The common, factor,
and graph-corner carriers are ULift transports. The graph construction
has an extension theorem for targets in this universe. Common-entry premises are discharged
by the existing concrete finite inclusions. -/
theorem graph_isFullAmalgam :
    CStarAmalgam.IsFullAmalgam
      (UniverseLift.map.{u} (GraphCommonInclusions.first k l))
      (UniverseLift.map.{u} (GraphCommonInclusions.second source target k l))
      (UniverseLift.map.{u}
        (firstFactorHom (graphFamily.{u} (source := source) (target := target)) k l))
      (UniverseLift.map.{u}
        (factorHom (graphFamily.{u} (source := source) (target := target)) k l hk hns)) := by
  apply UniverseLift.fullAmalgamOfSmallInputs
  · exact GraphCommonInclusions.commutes_of_commonEntries source target k l _ _
      (GraphFiniteAmalgam.graph_commonEntries k l hk hns)
  · intro C _ f₀ f₁ hf
    exact GraphFiniteAmalgam.existsUnique_extension k l hk hl f₀ f₁
      (GraphCommonInclusions.commonEntries_of_commutes source target k l f₀ f₁ hf) hns

end GraphUniverse

def matrixAlgebra (q : ℕ) : Algebra.{u} :=
  ⟨CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) ℂ, inferInstance⟩

def amplification (A : Algebra.{u}) (q : ℕ) : Algebra.{u} :=
  ⟨CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A, inferInstance⟩

/-- Only a finite index reindexing is used to accept the manuscript's ordinary
sigma : E → M_q(C) in an arbitrary coefficient universe. -/
def liftRepresentation {E : Algebra.{u}} {q : ℕ}
    (σ : E →⋆ₐ[ℂ] CStarMatrix (Fin q) (Fin q) ℂ) : E →⋆ₐ[ℂ] matrixAlgebra.{u} q :=
  (CStarMatrix.reindexₐ ℂ ℂ Equiv.ulift.symm).toStarAlgHom.comp σ

/-- Standard spatial tensor support; every object is an actual complete C⋆-algebra
and every map an actual complex star homomorphism. No UCT is involved. -/
structure Spatial where
  tensor : Algebra.{u} → Algebra.{u} → Algebra.{u}
  left (A B : Algebra.{u}) : A →⋆ₐ[ℂ] tensor A B
  right (A B : Algebra.{u}) : B →⋆ₐ[ℂ] tensor A B
  commute (A B : Algebra.{u}) (a : A) (b : B) :
    left A B a * right A B b = right A B b * left A B a
  norm_pure (A B : Algebra.{u}) (a : A) (b : B) :
    ‖left A B a * right A B b‖ = ‖a‖ * ‖b‖
  dense (A B : Algebra.{u}) : Dense
    (Submodule.span ℂ (Set.range fun p : A × B => left A B p.1 * right A B p.2) :
      Set (tensor A B))
  map {A B C D : Algebra.{u}} (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] D) :
    tensor A B →⋆ₙₐ[ℂ] tensor C D
  map_pure {A B C D : Algebra.{u}} (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] D)
      (a : A) (b : B) :
    map f g (left A B a * right A B b) = left C D (f a) * right C D (g b)
  map_injective {A B C D : Algebra.{u}} (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] D) :
    Function.Injective f → Function.Injective g → Function.Injective (map f g)
  matrixEquiv (A : Algebra.{u}) (q : ℕ) :
    tensor A (matrixAlgebra q) ≃⋆ₐ[ℂ] amplification A q
  matrixEquiv_pure (A : Algebra.{u}) (q : ℕ) (a : A) (m : matrixAlgebra q)
      (i j : ULift.{u} (Fin q)) :
    matrixEquiv A q (left A (matrixAlgebra q) a * right A (matrixAlgebra q) m) i j =
      m i j • a

namespace Spatial
variable (T : Spatial.{u})
variable {A B C D X : Algebra.{u}}

def pure (a : A) (b : B) : T.tensor A B := T.left A B a * T.right A B b

@[simp] theorem pure_one_one : T.pure (1 : A) (1 : B) = 1 := by
  simp [pure]
@[simp] theorem pure_one_right (a : A) : T.pure a (1 : B) = T.left A B a := by
  simp [pure]
@[simp] theorem pure_one_left (b : B) : T.pure (1 : A) b = T.right A B b := by
  simp [pure]
@[simp] theorem pure_zero_left (b : B) : T.pure (0 : A) b = 0 := by
  simp [pure]

theorem pure_mul (a a' : A) (b b' : B) :
    T.pure a b * T.pure a' b' = T.pure (a * a') (b * b') := by
  simp only [pure, map_mul]
  calc
    _ = T.left A B a * (T.right A B b * T.left A B a') * T.right A B b' := by
      simp only [mul_assoc]
    _ = T.left A B a * (T.left A B a' * T.right A B b) * T.right A B b' := by
      rw [← T.commute]
    _ = _ := by simp only [mul_assoc]

theorem pure_star (a : A) (b : B) : star (T.pure a b) = T.pure (star a) (star b) := by
  simp only [pure, star_mul, ← map_star]
  exact (T.commute A B (star a) (star b)).symm

theorem hom_ext {f g : T.tensor A B →⋆ₙₐ[ℂ] X}
    (h : ∀ a b, f (T.pure a b) = g (T.pure a b)) : f = g := by
  let fc : T.tensor A B →L[ℂ] X :=
    { toFun := f, map_add' := map_add f, map_smul' := map_smul f,
      cont := map_continuous f }
  let gc : T.tensor A B →L[ℂ] X :=
    { toFun := g, map_add' := map_add g, map_smul' := map_smul g,
      cont := map_continuous g }
  have he : fc = gc := ContinuousLinearMap.ext_on (T.dense A B) (by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact h a b)
  exact NonUnitalStarAlgHom.ext fun x => DFunLike.congr_fun he x

@[simp] theorem map_pure' (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] D) (a : A) (b : B) :
    T.map f g (T.pure a b) = T.pure (f a) (g b) := T.map_pure f g a b

/-- Functoriality follows from the pure formula and norm density. -/
theorem map_comp {A₁ B₁ A₂ B₂ A₃ B₃ : Algebra.{u}}
    (f₁ : A₁ →⋆ₙₐ[ℂ] A₂) (f₂ : A₂ →⋆ₙₐ[ℂ] A₃)
    (g₁ : B₁ →⋆ₙₐ[ℂ] B₂) (g₂ : B₂ →⋆ₙₐ[ℂ] B₃) :
    (T.map f₂ g₂).comp (T.map f₁ g₁) = T.map (f₂.comp f₁) (g₂.comp g₁) := by
  apply T.hom_ext
  intro a b
  simp

theorem map_id :
    T.map (StarAlgHom.id ℂ A).toNonUnitalStarAlgHom
      (StarAlgHom.id ℂ B).toNonUnitalStarAlgHom =
      (StarAlgHom.id ℂ (T.tensor A B)).toNonUnitalStarAlgHom := by
  apply T.hom_ext
  intro a b
  simp

theorem map_unit (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] D) :
    T.map f g 1 = T.pure (f 1) (g 1) := by
  conv_lhs => rw [← T.pure_one_one (A := A) (B := B)]
  exact T.map_pure' f g 1 1

def unitalMap (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] D) :
    T.tensor A B →⋆ₐ[ℂ] T.tensor C D where
  toFun := T.map f.toNonUnitalStarAlgHom g.toNonUnitalStarAlgHom
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := map_mul _
  map_star' := map_star _
  map_one' := by simpa using T.map_unit f.toNonUnitalStarAlgHom g.toNonUnitalStarAlgHom
  commutes' := by
    intro z
    rw [Algebra.algebraMap_eq_smul_one, map_smul, T.map_unit]
    simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem unitalMap_pure (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] D) (a : A) (b : B) :
    T.unitalMap f g (T.pure a b) = T.pure (f a) (g b) := T.map_pure _ _ a b

theorem unital_hom_ext {f g : T.tensor A B →⋆ₐ[ℂ] X}
    (h : ∀ a b, f (T.pure a b) = g (T.pure a b)) : f = g := by
  have := T.hom_ext (f := f.toNonUnitalStarAlgHom) (g := g.toNonUnitalStarAlgHom) h
  exact StarAlgHom.ext fun x => DFunLike.congr_fun this x

@[simp] theorem unitalMap_left (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] D) (a : A) :
    T.unitalMap f g (T.left A B a) = T.left C D (f a) := by
  have h := T.unitalMap_pure f g a 1
  simpa using h

@[simp] theorem unitalMap_right (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] D) (b : B) :
    T.unitalMap f g (T.right A B b) = T.right C D (g b) := by
  have h := T.unitalMap_pure f g 1 b
  simpa using h

/-- Actual matrix amplification of a scalar map, transported through the
standard pure-tensor-fixing matrix equivalence. -/
def amplifiedMap (q : ℕ) (f : A →⋆ₐ[ℂ] C) :
    amplification A q →⋆ₐ[ℂ] amplification C q :=
  (T.matrixEquiv C q).toStarAlgHom.comp
    ((T.unitalMap f (StarAlgHom.id ℂ (matrixAlgebra q))).comp
      (T.matrixEquiv A q).symm.toStarAlgHom)

@[simp] theorem amplifiedMap_matrixEquiv (q : ℕ) (f : A →⋆ₐ[ℂ] C)
    (a : A) (m : matrixAlgebra q) :
    T.amplifiedMap q f (T.matrixEquiv A q (T.pure a m)) =
      T.matrixEquiv C q (T.pure (f a) m) := by
  simp [amplifiedMap]

/-- The matrix equivalence uses an actual single minimal matrix position.
It does not replace this position by the full q-by-q unit. -/
theorem matrixEquiv_single (q : ℕ) (a : A) (r s : ULift.{u} (Fin q)) :
    T.matrixEquiv A q
      (T.pure a (CStarMatrix.ofMatrix (Matrix.single r s (1 : ℂ)))) =
      CStarMatrix.ofMatrix (Matrix.single r s a) := by
  apply CStarMatrix.ext
  intro i j
  have he := T.matrixEquiv_pure A q a
    (CStarMatrix.ofMatrix (Matrix.single r s (1 : ℂ))) i j
  change (T.matrixEquiv A q (T.pure a _)) i j = _ at he
  rw [he]
  by_cases hi : r = i <;> by_cases hj : s = j <;>
    simp [CStarMatrix.ofMatrix_apply, hi, hj]

end Spatial

/-- Standard min=max consequence for a nuclear coefficient E. It may equally
be supplied for the maximal tensor product. No amalgam statement is a field. -/
structure MaximalOn (T : Spatial.{u}) (E : Algebra.{u}) where
  lift {A C : Algebra.{u}} (f : A →⋆ₐ[ℂ] C) (g : E →⋆ₐ[ℂ] C)
    (h : ∀ a e, f a * g e = g e * f a) : T.tensor A E →⋆ₐ[ℂ] C
  lift_pure {A C : Algebra.{u}} (f : A →⋆ₐ[ℂ] C) (g : E →⋆ₐ[ℂ] C)
    (h : ∀ a e, f a * g e = g e * f a) (a : A) (e : E) :
    lift f g h (T.pure a e) = f a * g e

inductive Channel | plus | minus | noise
  deriving DecidableEq

instance : Fintype Channel := ⟨{.plus, .minus, .noise}, by intro c; cases c <;> simp⟩

theorem sum_channel {V : Type*} [AddCommMonoid V] (f : Channel → V) :
    ∑ c, f c = f .plus + f .minus + f .noise := by
  change ∑ c ∈ ({.plus, .minus, .noise} : Finset Channel), f c = _
  simp [add_assoc]

/-- Scalar graph-channel data at ONE step, still a local construction obligation.
The noise source is the actual matrix amplification, with its usual unit. -/
structure ScalarChannels (A B : Algebra.{u}) (q : ℕ) where
  plus : A →⋆ₙₐ[ℂ] B
  minus : A →⋆ₙₐ[ℂ] B
  noise : amplification A q →⋆ₙₐ[ℂ] B
  plus_injective : Function.Injective plus
  orthogonal : ∀ c d : Channel, c ≠ d →
    (match c with | .plus => plus 1 | .minus => minus 1 | .noise => noise 1) *
    (match d with | .plus => plus 1 | .minus => minus 1 | .noise => noise 1) = 0
  unit_sum : plus 1 + minus 1 + noise 1 = 1

namespace ScalarChannels
variable {A B E : Algebra.{u}} {q : ℕ}
variable (T : Spatial.{u}) (G : ScalarChannels A B q)
variable (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E)
variable (σ : E →⋆ₐ[ℂ] matrixAlgebra.{u} q)

def support : Channel → B
  | .plus => G.plus 1
  | .minus => G.minus 1
  | .noise => G.noise 1

def noiseTensor : T.tensor A (matrixAlgebra q) →⋆ₙₐ[ℂ] B :=
  G.noise.comp (T.matrixEquiv A q).toStarAlgHom.toNonUnitalStarAlgHom

/-- These are precisely γ+⊗id, γ−⊗ηε, and (γ0~ (id⊗σ)(−))⊗1. -/
def coefficient : Channel → T.tensor A E →⋆ₙₐ[ℂ] T.tensor B E
  | .plus => T.map G.plus (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom
  | .minus => T.map G.minus (η.comp ε).toNonUnitalStarAlgHom
  | .noise => (T.left B E).toNonUnitalStarAlgHom.comp
      ((G.noiseTensor T).comp (T.map (StarAlgHom.id ℂ A).toNonUnitalStarAlgHom
        σ.toNonUnitalStarAlgHom))

theorem coefficient_unit (c : Channel) :
    G.coefficient T ε η σ c 1 = T.left B E (G.support c) := by
  cases c <;> simp [coefficient, support, noiseTensor, T.map_unit]

theorem coefficient_orthogonal (c d : Channel) (h : c ≠ d) :
    G.coefficient T ε η σ c 1 * G.coefficient T ε η σ d 1 = 0 := by
  rw [G.coefficient_unit, G.coefficient_unit, ← map_mul]
  have hg : G.support c * G.support d = 0 := G.orthogonal c d h
  rw [hg, map_zero]

theorem coefficient_unit_sum : ∑ c, G.coefficient T ε η σ c 1 = 1 := by
  have hs : ∑ c : Channel, G.support c = 1 := by
    simpa [sum_channel, support] using G.unit_sum
  simp_rw [G.coefficient_unit]
  rw [← map_sum, hs, map_one]

/-- The actual unital connecting homomorphism of coefficient algebras. -/
def phi : T.tensor A E →⋆ₐ[ℂ] T.tensor B E :=
  OrthogonalChannels.sumHom (G.coefficient T ε η σ)
    (G.coefficient_orthogonal T ε η σ) (G.coefficient_unit_sum T ε η σ)

theorem phi_formula (x : T.tensor A E) :
    G.phi T ε η σ x = T.map G.plus (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom x +
      T.map G.minus (η.comp ε).toNonUnitalStarAlgHom x +
      T.left B E (G.noiseTensor T (T.map (StarAlgHom.id ℂ A).toNonUnitalStarAlgHom
        σ.toNonUnitalStarAlgHom x)) := by
  change (∑ c, G.coefficient T ε η σ c x) = _
  rw [sum_channel]
  rfl

/-- Faithfulness comes from the positive identity-coefficient channel. It does
not require sigma, eta-epsilon, or the individual noise channel to be faithful. -/
theorem phi_injective : Function.Injective (G.phi T ε η σ) := by
  apply OrthogonalChannels.sumHom_injective _ _ _ Channel.plus
  exact T.map_injective G.plus (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom
    G.plus_injective Function.injective_id

theorem phi_isometry : Isometry (G.phi T ε η σ) :=
  NonUnitalStarAlgHom.isometry _ (G.phi_injective T ε η σ)

/-- Compression uses the actual constant support projection in the target. -/
theorem coefficient_compression (c : Channel) (x : T.tensor A E) :
    T.left B E (G.support c) * G.phi T ε η σ x = G.coefficient T ε η σ c x := by
  rw [← G.coefficient_unit T ε η σ c]
  exact OrthogonalChannels.compression _ (G.coefficient_orthogonal T ε η σ) c x

variable {C D : Algebra.{u}} (H : ScalarChannels C D q)
variable (i : A →⋆ₐ[ℂ] C) (j : B →⋆ₐ[ℂ] D)
variable (hp : ∀ a, H.plus (i a) = j (G.plus a))
variable (hm : ∀ a, H.minus (i a) = j (G.minus a))
variable (hn : ∀ x, H.noise (T.amplifiedMap q i x) = j (G.noise x))

include hp hm hn

/-- Literal coefficient squares are derived from the scalar squares, including
the amplified source square for noise. The coefficient operation is shared. -/
theorem coefficient_square (c : Channel) :
    (H.coefficient T ε η σ c).comp
      (T.unitalMap i (StarAlgHom.id ℂ E)).toNonUnitalStarAlgHom =
    (T.unitalMap j (StarAlgHom.id ℂ E)).toNonUnitalStarAlgHom.comp
      (G.coefficient T ε η σ c) := by
  apply T.hom_ext
  intro a e
  have hnoise := hn (T.matrixEquiv A q (T.pure a (σ e)))
  rw [T.amplifiedMap_matrixEquiv] at hnoise
  cases c
  · simp [coefficient, hp]
  · simp [coefficient, hm]
  · simpa [coefficient, noiseTensor] using congrArg (T.left D E) hnoise

/-- The actual sums form a literal square of unital homomorphisms. -/
theorem phi_square :
    (H.phi T ε η σ).comp (T.unitalMap i (StarAlgHom.id ℂ E)) =
      (T.unitalMap j (StarAlgHom.id ℂ E)).comp (G.phi T ε η σ) := by
  apply StarAlgHom.ext
  intro x
  change (∑ c, H.coefficient T ε η σ c (T.unitalMap i (StarAlgHom.id ℂ E) x)) =
    T.unitalMap j (StarAlgHom.id ℂ E) (∑ c, G.coefficient T ε η σ c x)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact DFunLike.congr_fun (G.coefficient_square T ε η σ H i j hp hm hn c) x

end ScalarChannels

section Amalgam
variable {D A₀ A₁ P E C : Algebra.{u}}
variable {i₀ : D →⋆ₐ[ℂ] A₀} {i₁ : D →⋆ₐ[ℂ] A₁}
variable {j₀ : A₀ →⋆ₐ[ℂ] P} {j₁ : A₁ →⋆ₐ[ℂ] P}

/-- Commutation with both factor copies extends to their full amalgam. This
uses the proved closed-generation consequence of the full universal property. -/
theorem amalgam_commutes (h : CStarAmalgam.IsFullAmalgam i₀ i₁ j₀ j₁)
    (f : P →⋆ₐ[ℂ] C) (g : E →⋆ₐ[ℂ] C)
    (h₀ : ∀ a e, f (j₀ a) * g e = g e * f (j₀ a))
    (h₁ : ∀ a e, f (j₁ a) * g e = g e * f (j₁ a)) :
    ∀ p e, f p * g e = g e * f p := by
  let S := (StarSubalgebra.centralizer ℂ (Set.range g)).comap f
  have hc : IsClosed (S : Set P) :=
    (Set.isClosed_centralizer _).preimage (map_continuous f)
  have hs : S = ⊤ := by
    apply h.eq_top_of_isClosed S hc
    · intro a
      apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
      rintro _ ⟨e, rfl⟩
      refine ⟨(h₀ a e).symm, ?_⟩
      change star (g e) * f (j₀ a) = f (j₀ a) * star (g e)
      simpa only [map_star] using (h₀ a (star e)).symm
    · intro a
      apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
      rintro _ ⟨e, rfl⟩
      refine ⟨(h₁ a e).symm, ?_⟩
      change star (g e) * f (j₁ a) = f (j₁ a) * star (g e)
      simpa only [map_star] using (h₁ a (star e)).symm
  intro p e
  have hp : p ∈ S := by rw [hs]; trivial
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hp) (g e) ⟨e, rfl⟩).1.symm

variable (T : Spatial.{u}) (M : MaximalOn T E)
include M

/-- The manuscript's full-amalgam tensor identity, derived from the ordinary
maximal tensor universal property and the common commuting coefficient copy.
For the spatial tensor product the external `MaximalOn` input requires E nuclear.
There is no internal commutativity assumption on E. -/
theorem tensor_isFullAmalgam (h : CStarAmalgam.IsFullAmalgam i₀ i₁ j₀ j₁) :
    CStarAmalgam.IsFullAmalgam
      (T.unitalMap i₀ (StarAlgHom.id ℂ E)) (T.unitalMap i₁ (StarAlgHom.id ℂ E))
      (T.unitalMap j₀ (StarAlgHom.id ℂ E)) (T.unitalMap j₁ (StarAlgHom.id ℂ E)) where
  commutes := by
    apply T.unital_hom_ext
    intro d e
    have he := DFunLike.congr_fun h.commutes d
    simpa using congrArg (fun p => T.pure p e) he
  extension {C'} _ f₀ f₁ hf := by
    let Cb : Algebra.{u} := ⟨C', inferInstance⟩
    let a₀ : A₀ →⋆ₐ[ℂ] Cb := f₀.comp (T.left A₀ E)
    let a₁ : A₁ →⋆ₐ[ℂ] Cb := f₁.comp (T.left A₁ E)
    let g₀ : E →⋆ₐ[ℂ] Cb := f₀.comp (T.right A₀ E)
    let g₁ : E →⋆ₐ[ℂ] Cb := f₁.comp (T.right A₁ E)
    have hg : g₀ = g₁ := by
      apply StarAlgHom.ext
      intro e
      have he := DFunLike.congr_fun hf (T.right D E e)
      change f₀ (T.right A₀ E e) = f₁ (T.right A₁ E e)
      simpa using he
    have ha : a₀.comp i₀ = a₁.comp i₁ := by
      apply StarAlgHom.ext
      intro d
      have hd := DFunLike.congr_fun hf (T.left D E d)
      simpa [a₀, a₁] using hd
    let a : P →⋆ₐ[ℂ] Cb := h.lift a₀ a₁ ha
    have ha₀ (x : A₀) : a (j₀ x) = a₀ x := DFunLike.congr_fun (h.lift_left a₀ a₁ ha) x
    have ha₁ (x : A₁) : a (j₁ x) = a₁ x := DFunLike.congr_fun (h.lift_right a₀ a₁ ha) x
    have hcomm : ∀ p e, a p * g₀ e = g₀ e * a p := by
      apply amalgam_commutes h a g₀
      · intro x e
        rw [ha₀]
        exact (map_mul f₀ _ _).symm.trans
          ((congrArg f₀ (T.commute A₀ E x e)).trans (map_mul f₀ _ _))
      · intro x e
        rw [ha₁, hg]
        exact (map_mul f₁ _ _).symm.trans
          ((congrArg f₁ (T.commute A₁ E x e)).trans (map_mul f₁ _ _))
    let φ : T.tensor P E →⋆ₐ[ℂ] Cb := M.lift a g₀ hcomm
    have hφ₀ : φ.comp (T.unitalMap j₀ (StarAlgHom.id ℂ E)) = f₀ := by
      apply T.unital_hom_ext (X := Cb)
      intro x e
      change φ (T.unitalMap j₀ (StarAlgHom.id ℂ E) (T.pure x e)) = _
      rw [T.unitalMap_pure]
      change M.lift a g₀ hcomm (T.pure (j₀ x) e) = _
      rw [M.lift_pure, ha₀]
      exact (map_mul f₀ _ _).symm
    have hφ₁ : φ.comp (T.unitalMap j₁ (StarAlgHom.id ℂ E)) = f₁ := by
      apply T.unital_hom_ext (X := Cb)
      intro x e
      change φ (T.unitalMap j₁ (StarAlgHom.id ℂ E) (T.pure x e)) = _
      rw [T.unitalMap_pure]
      change M.lift a g₀ hcomm (T.pure (j₁ x) e) = _
      rw [M.lift_pure, ha₁, hg]
      exact (map_mul f₁ _ _).symm
    refine ⟨φ, ⟨hφ₀, hφ₁⟩, ?_⟩
    intro ψ hψ
    have hl : ψ.comp (T.left P E) = φ.comp (T.left P E) := by
      apply h.hom_ext
      · apply StarAlgHom.ext
        intro x
        have he := DFunLike.congr_fun (hψ.1.trans hφ₀.symm) (T.left A₀ E x)
        change ψ (T.left P E (j₀ x)) = φ (T.left P E (j₀ x))
        change ψ (T.unitalMap _ _ (T.left _ E x)) = φ (T.unitalMap _ _ (T.left _ E x)) at he
        simpa only [Spatial.unitalMap_left] using he
      · apply StarAlgHom.ext
        intro x
        have he := DFunLike.congr_fun (hψ.2.trans hφ₁.symm) (T.left A₁ E x)
        change ψ (T.left P E (j₁ x)) = φ (T.left P E (j₁ x))
        change ψ (T.unitalMap _ _ (T.left _ E x)) = φ (T.unitalMap _ _ (T.left _ E x)) at he
        simpa only [Spatial.unitalMap_left] using he
    have hr (e : E) : ψ (T.right P E e) = φ (T.right P E e) := by
      have he := DFunLike.congr_fun (hψ.1.trans hφ₀.symm) (T.right A₀ E e)
      change ψ (T.unitalMap j₀ _ (T.right A₀ E e)) =
        φ (T.unitalMap j₀ _ (T.right A₀ E e)) at he
      simpa only [Spatial.unitalMap_right, StarAlgHom.coe_id, id_eq] using he
    apply T.unital_hom_ext (X := Cb)
    intro p e
    change ψ (T.left P E p * T.right P E e) = φ (T.left P E p * T.right P E e)
    rw [map_mul, map_mul]
    exact congrArg₂ (fun x y : C' => x * y) (DFunLike.congr_fun hl p) (hr e)

end Amalgam

/-- Transport a full amalgam along four specified actual star equivalences.
All four inclusions are conjugated, so this preserves the literal diagram. -/
theorem amalgam_transport
    {D A₀ A₁ P D' A₀' A₁' P' : Type u}
    [CStarAlgebra D] [CStarAlgebra A₀] [CStarAlgebra A₁] [CStarAlgebra P]
    [CStarAlgebra D'] [CStarAlgebra A₀'] [CStarAlgebra A₁'] [CStarAlgebra P']
    {i₀ : D →⋆ₐ[ℂ] A₀} {i₁ : D →⋆ₐ[ℂ] A₁}
    {j₀ : A₀ →⋆ₐ[ℂ] P} {j₁ : A₁ →⋆ₐ[ℂ] P}
    (h : CStarAmalgam.IsFullAmalgam i₀ i₁ j₀ j₁)
    (eD : D ≃⋆ₐ[ℂ] D') (e₀ : A₀ ≃⋆ₐ[ℂ] A₀')
    (e₁ : A₁ ≃⋆ₐ[ℂ] A₁') (eP : P ≃⋆ₐ[ℂ] P') :
    CStarAmalgam.IsFullAmalgam
      (e₀.toStarAlgHom.comp (i₀.comp eD.symm.toStarAlgHom))
      (e₁.toStarAlgHom.comp (i₁.comp eD.symm.toStarAlgHom))
      (eP.toStarAlgHom.comp (j₀.comp e₀.symm.toStarAlgHom))
      (eP.toStarAlgHom.comp (j₁.comp e₁.symm.toStarAlgHom)) where
  commutes := by
    apply StarAlgHom.ext
    intro d
    have hd := DFunLike.congr_fun h.commutes (eD.symm d)
    simpa using congrArg eP hd
  extension f₀ f₁ hf := by
    let g₀ := f₀.comp e₀.toStarAlgHom
    let g₁ := f₁.comp e₁.toStarAlgHom
    have hg : g₀.comp i₀ = g₁.comp i₁ := by
      apply StarAlgHom.ext
      intro d
      have hd := DFunLike.congr_fun hf (eD d)
      simpa [g₀, g₁] using hd
    let a := h.lift g₀ g₁ hg
    let φ := a.comp eP.symm.toStarAlgHom
    have ha₀ (x : A₀) : a (j₀ x) = g₀ x := DFunLike.congr_fun (h.lift_left g₀ g₁ hg) x
    have ha₁ (x : A₁) : a (j₁ x) = g₁ x := DFunLike.congr_fun (h.lift_right g₀ g₁ hg) x
    have hφ₀ : φ.comp (eP.toStarAlgHom.comp (j₀.comp e₀.symm.toStarAlgHom)) = f₀ := by
      apply StarAlgHom.ext
      intro x
      simpa [φ, g₀] using ha₀ (e₀.symm x)
    have hφ₁ : φ.comp (eP.toStarAlgHom.comp (j₁.comp e₁.symm.toStarAlgHom)) = f₁ := by
      apply StarAlgHom.ext
      intro x
      simpa [φ, g₁] using ha₁ (e₁.symm x)
    refine ⟨φ, ⟨hφ₀, hφ₁⟩, ?_⟩
    intro ψ hψ
    have hbase : ψ.comp eP.toStarAlgHom = a := by
      apply h.hom_ext
      · apply StarAlgHom.ext
        intro x
        have hx := DFunLike.congr_fun hψ.1 (e₀ x)
        change ψ (eP (j₀ x)) = a (j₀ x)
        rw [ha₀]
        simpa [g₀] using hx
      · apply StarAlgHom.ext
        intro x
        have hx := DFunLike.congr_fun hψ.2 (e₁ x)
        change ψ (eP (j₁ x)) = a (j₁ x)
        rw [ha₁]
        simpa [g₁] using hx
    apply StarAlgHom.ext
    intro x
    simpa [φ] using DFunLike.congr_fun hbase (eP.symm x)

/-- The amplified triple's actual full amalgam is M_q(P). The matrix
universal-property input here is standard nuclearity/min=max for M_q(C). -/
theorem amplification_isFullAmalgam (T : Spatial.{u}) (q : ℕ)
    (M : MaximalOn T (matrixAlgebra q))
    {D A₀ A₁ P : Algebra.{u}}
    {i₀ : D →⋆ₐ[ℂ] A₀} {i₁ : D →⋆ₐ[ℂ] A₁}
    {j₀ : A₀ →⋆ₐ[ℂ] P} {j₁ : A₁ →⋆ₐ[ℂ] P}
    (h : CStarAmalgam.IsFullAmalgam i₀ i₁ j₀ j₁) :
    CStarAmalgam.IsFullAmalgam (T.amplifiedMap q i₀) (T.amplifiedMap q i₁)
      (T.amplifiedMap q j₀) (T.amplifiedMap q j₁) :=
  amalgam_transport (tensor_isFullAmalgam T M h)
    (T.matrixEquiv D q) (T.matrixEquiv A₀ q) (T.matrixEquiv A₁ q) (T.matrixEquiv P q)

/-- The explicit three-channel product formula is the induced full-product
map. Only the SCALAR factor squares are hypotheses; the coefficient squares
and the universal-product identification are derived here. -/
theorem phi_is_full_product_map (T : Spatial.{u})
    {D A₀ A₁ P B₀ B₁ Q E : Algebra.{u}} {q : ℕ}
    (M : MaximalOn T E)
    {i₀ : D →⋆ₐ[ℂ] A₀} {i₁ : D →⋆ₐ[ℂ] A₁}
    (j₀ : A₀ →⋆ₐ[ℂ] P) (j₁ : A₁ →⋆ₐ[ℂ] P)
    (k₀ : B₀ →⋆ₐ[ℂ] Q) (k₁ : B₁ →⋆ₐ[ℂ] Q)
    (h : CStarAmalgam.IsFullAmalgam i₀ i₁ j₀ j₁)
    (G₀ : ScalarChannels A₀ B₀ q) (G₁ : ScalarChannels A₁ B₁ q)
    (GP : ScalarChannels P Q q)
    (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E) (σ : E →⋆ₐ[ℂ] matrixAlgebra q)
    (hp₀ : ∀ a, GP.plus (j₀ a) = k₀ (G₀.plus a))
    (hm₀ : ∀ a, GP.minus (j₀ a) = k₀ (G₀.minus a))
    (hn₀ : ∀ x, GP.noise (T.amplifiedMap q j₀ x) = k₀ (G₀.noise x))
    (hp₁ : ∀ a, GP.plus (j₁ a) = k₁ (G₁.plus a))
    (hm₁ : ∀ a, GP.minus (j₁ a) = k₁ (G₁.minus a))
    (hn₁ : ∀ x, GP.noise (T.amplifiedMap q j₁ x) = k₁ (G₁.noise x)) :
    ∃ hf,
      (tensor_isFullAmalgam T M h).lift
        ((T.unitalMap k₀ (StarAlgHom.id ℂ E)).comp (G₀.phi T ε η σ))
        ((T.unitalMap k₁ (StarAlgHom.id ℂ E)).comp (G₁.phi T ε η σ)) hf =
        GP.phi T ε η σ := by
  have h₀ := G₀.phi_square T ε η σ GP j₀ k₀ hp₀ hm₀ hn₀
  have h₁ := G₁.phi_square T ε η σ GP j₁ k₁ hp₁ hm₁ hn₁
  have ht := tensor_isFullAmalgam T M h
  have hf :
      ((T.unitalMap k₀ (StarAlgHom.id ℂ E)).comp (G₀.phi T ε η σ)).comp
        (T.unitalMap i₀ (StarAlgHom.id ℂ E)) =
      ((T.unitalMap k₁ (StarAlgHom.id ℂ E)).comp (G₁.phi T ε η σ)).comp
        (T.unitalMap i₁ (StarAlgHom.id ℂ E)) := by
    rw [← h₀, ← h₁, StarAlgHom.comp_assoc, StarAlgHom.comp_assoc, ht.commutes]
  exact ⟨hf, (ht.lift_unique _ _ hf (GP.phi T ε η σ) h₀ h₁).symm⟩

end Suzuki.TensorCoefficientChannels

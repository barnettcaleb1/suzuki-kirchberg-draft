import Suzuki.GraphChannelKKCalculation
import Suzuki.CommonUnitProjection
import Suzuki.RecursiveGraphSequence
import Suzuki.TensorCoefficientChannels
import Suzuki.CoefficientModelFromExtension

/-!
# Actual common-projection coordinates

The graph image and coefficient-block decomposition below concern actual maps
and actual projections. Standard K0 interpretation laws, when used, are explicit
parameters; the desired signed projection coordinate is never an input.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Suzuki.PrescribedUnitCoordinate
open Matrix WeightedGraphAmalgam GraphCommonInclusions GraphCornerIdentification
open scoped CStarAlgebra ComplexOrder

section GraphImages
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (source target : E → V) (k l : V → ℕ) (hk : ∀ v, 0 < k v) (hl : ∀ v, 0 < l v)
  (hns : GraphRelations.NoSinks source)
local instance graphOrder : PartialOrder (GraphUniversal.Algebra.{0} source target) :=
  CStarAlgebra.spectralOrder _
local instance graphOrderedRing : StarOrderedRing (GraphUniversal.Algebra.{0} source target) :=
  CStarAlgebra.spectralOrderedRing _

/-- Complete actual first-factor formula, adapted from the frozen supplemental
GraphProjectionCoordinates proof without changing an existing release module. -/
theorem left_image (a : FirstFactor k l) :
    GraphCommonInclusions.amalgamEquivCorner source target k l hk hl hns
      (UniversalAmalgam.left (first k l) (second source target k l) a) =
      firstFactorHom (graphFamily.{0} (source := source) (target := target)) k l a := by
  unfold GraphCommonInclusions.amalgamEquivCorner GraphFiniteAmalgam.identify
    GraphCornerIdentification.amalgamEquivCorner
  change GraphCornerIdentification.forward k l hk _ _ _ _ _ _ _ _ = _
  unfold GraphCornerIdentification.forward
  conv_lhs =>
    arg 2
    rw [← GraphCanonicalUnits.representation_ofHom (coordVertex k l)
      (UniversalAmalgam.left (first k l) (second source target k l))]
  exact DFunLike.congr_fun (CStarAmalgam.IsFullAmalgam.lift_left _ _ _ _) a

/-- The common algebra's actual inclusion followed by the proved graph-corner
equivalence. -/
def commonToCorner : GraphCommonInclusions.Common k l →⋆ₐ[ℂ]
    graphCorner.{0} (source := source) (target := target) k l :=
  (GraphCommonInclusions.amalgamEquivCorner source target k l hk hl hns).toStarAlgHom.comp
    ((UniversalAmalgam.left (first k l) (second source target k l)).comp (first k l))

/-- Every P-block matrix unit is literally the same matrix position with the
vertex projection as its coefficient. In particular this fixes the minimal
projection normalization before any K0 law is applied. -/
theorem common_P_image (v : V) (a b : Fin (k v)) :
    ((commonToCorner source target k l hk hl hns
      (GraphCommonInclusions.unit k l (.inl v) a b) : graphCorner.{0}
        (source := source) (target := target) k l) :
      CStarMatrix (Coord k l) (Coord k l) (GraphUniversal.Algebra.{0} source target)) =
    WeightedGraphAmalgam.single k l (GraphAmalgamInverse.pCoord k l v a)
      (GraphAmalgamInverse.pCoord k l v b)
      ((graphFamily.{0} (source := source) (target := target)).vertex v) := by
  calc
    _ = (firstFactorHom (graphFamily.{0} (source := source) (target := target)) k l
        (first k l (GraphCommonInclusions.unit k l (.inl v) a b))).val :=
      congrArg Subtype.val (left_image source target k l hk hl hns
        (first k l (GraphCommonInclusions.unit k l (.inl v) a b)))
    _ = _ := by
      rw [first_P]
      rw [GraphCanonicalUnits.scalarUnit_single (coordVertex k l) v
        ⟨GraphAmalgamInverse.pCoord k l v a,rfl⟩ ⟨GraphAmalgamInverse.pCoord k l v b,rfl⟩,
        firstFactor_single,one_smul]
      rfl

end GraphImages

section CoefficientProjection
variable {E : Type*} [CStarAlgebra E]
local instance coefficientOrder : PartialOrder E := CStarAlgebra.spectralOrder E
local instance coefficientStarOrderedRing : StarOrderedRing E := CStarAlgebra.spectralOrderedRing E

def coefficientBlock (n : ℕ) (v : Fin 2) :
    CStarMatrix (Fin (n+1)) (Fin (n+1)) E →⋆ₙₐ[ℂ] CommonUnitProjection.Common E n :=
  OrthogonalFiniteDiagrams.singleHom
    (fun i => CStarMatrix (Fin (CommonUnitProjection.commonSize n i))
      (Fin (CommonUnitProjection.commonSize n i)) E) (.inl v)

/-- The actual initial projection is an orthogonal sum of its two positive
coefficient-block images. The minus sign has not yet entered this formula. -/
theorem commonProjection_decomposition {n : ℕ}
    (p q : CStarMatrix (Fin n) (Fin n) E) :
    CommonUnitProjection.commonProjection p q =
      coefficientBlock n 0 (CommonUnitProjection.stabilizedFin p) +
      coefficientBlock n 1 (CommonUnitProjection.stabilizedFin q) := by
  funext i
  cases i with
  | inl i => fin_cases i <;> simp [CommonUnitProjection.commonProjection,coefficientBlock,
      OrthogonalFiniteDiagrams.singleHom]
  | inr i => simp [CommonUnitProjection.commonProjection,coefficientBlock,
      OrthogonalFiniteDiagrams.singleHom]

theorem coefficientBlock_orthogonal (n : ℕ) (p q : CStarMatrix (Fin (n+1)) (Fin (n+1)) E) :
    coefficientBlock n 0 p * coefficientBlock n 1 q = 0 := by
  funext i
  cases i with
  | inl i => fin_cases i <;> simp [coefficientBlock,OrthogonalFiniteDiagrams.singleHom]
  | inr i => simp [coefficientBlock,OrthogonalFiniteDiagrams.singleHom]
end CoefficientProjection



section TensorImages
open TensorCoefficientChannels
universe u

abbrev scalarMatrices (n : ℕ) : Algebra.{u} :=
  UniverseLift.algebra (CStarMatrix (Fin n) (Fin n) ℂ)

abbrev scalarBlocks {I : Type} [Fintype I] [DecidableEq I] (w : I → ℕ) : Algebra.{u} :=
  UniverseLift.algebra (MultiplicityEmbeddings.Blocks w)

abbrev coefficientMatrices (E : Algebra.{u}) (n : ℕ) : Algebra.{u} :=
  ⟨CStarMatrix (Fin n) (Fin n) E, inferInstance⟩

abbrev coefficientBlocks (E : Algebra.{u}) {I : Type} [Fintype I] [DecidableEq I]
    (w : I → ℕ) : Algebra.{u} :=
  ⟨∀ i, CStarMatrix (Fin (w i)) (Fin (w i)) E, inferInstance⟩

/-- Standard finite-dimensional spatial tensor coordinates, quantified over ALL
finite products, weights and coefficients. These are actual star algebra
isomorphisms with their elementary-tensor formulas, not K-theory conclusions. -/
structure FiniteTensorCoordinates (T : Spatial.{u}) where
  matrix (E : Algebra.{u}) (n : ℕ) :
    T.tensor (scalarMatrices n) E ≃⋆ₐ[ℂ] coefficientMatrices E n
  matrix_pure (E : Algebra.{u}) (n : ℕ) (a : CStarMatrix (Fin n) (Fin n) ℂ)
    (e : E) (r s : Fin n) : matrix E n (T.pure (ULift.up a) e) r s = a r s • e
  blocks (E : Algebra.{u}) {I : Type} [Fintype I] [DecidableEq I] (w : I → ℕ) :
    T.tensor (scalarBlocks w) E ≃⋆ₐ[ℂ] coefficientBlocks E w
  blocks_pure (E : Algebra.{u}) {I : Type} [Fintype I] [DecidableEq I]
    (w : I → ℕ) (a : MultiplicityEmbeddings.Blocks w) (e : E) (i : I)
    (r s : Fin (w i)) : blocks E w (T.pure (ULift.up a) e) i r s = a i r s • e

variable (T : Spatial.{u}) (F : FiniteTensorCoordinates T)

def scalarBlock (n : ℕ) (v : Fin 2) :
    scalarMatrices.{u} (n+1) →⋆ₙₐ[ℂ] scalarBlocks (CommonUnitProjection.commonSize n) :=
  UniverseLift.nonUnitalMap (coefficientBlock (E := ℂ) n v)

/-- The actual tensor map obtained from a scalar matrix-block homomorphism. -/
def blockTensor {A E : Algebra.{u}} {n : ℕ} (ψ : scalarMatrices n →⋆ₙₐ[ℂ] A) :
    coefficientMatrices E n →⋆ₙₐ[ℂ] T.tensor A E :=
  (T.map ψ (NonUnitalStarAlgHom.id ℂ E)).comp
    (F.matrix E n).symm.toStarAlgHom.toNonUnitalStarAlgHom

/-- Naturality of the finite-product coordinates is PROVED from the two
universal elementary-tensor formulas. -/
theorem scalarBlock_tensor_square (E : Algebra.{u}) (n : ℕ) (v : Fin 2) :
    (F.blocks E (CommonUnitProjection.commonSize n)).toStarAlgHom.toNonUnitalStarAlgHom.comp
      (T.map (scalarBlock n v) (NonUnitalStarAlgHom.id ℂ E)) =
    (coefficientBlock (E := E) n v).comp
      (F.matrix E (n+1)).toStarAlgHom.toNonUnitalStarAlgHom := by
  apply T.hom_ext
  intro a e
  change F.blocks E _ (T.map (scalarBlock n v) (NonUnitalStarAlgHom.id ℂ E)
    (T.pure a e)) = coefficientBlock n v (F.matrix E (n+1) (T.pure a e))
  rw [T.map_pure']
  change F.blocks E _ (T.pure (ULift.up (coefficientBlock (E := ℂ) n v a.down)) e) =
    coefficientBlock n v (F.matrix E (n+1) (T.pure (ULift.up a.down) e))
  funext i
  apply CStarMatrix.ext
  intro r s
  rw [F.blocks_pure]
  cases i with
  | inl i =>
    by_cases hi : i = v
    · subst i
      simpa only [coefficientBlock,OrthogonalFiniteDiagrams.singleHom,
        NonUnitalStarAlgHom.coe_mk,Pi.single_eq_same] using
        (F.matrix_pure E (n+1) a.down e r s).symm
    · simp [coefficientBlock,OrthogonalFiniteDiagrams.singleHom,hi]
  | inr i => simp [coefficientBlock,OrthogonalFiniteDiagrams.singleHom]

theorem blockTensor_scalarBlock (E : Algebra.{u}) (n : ℕ) (v : Fin 2)
    (p : coefficientMatrices E (n+1)) :
    F.blocks E (CommonUnitProjection.commonSize n)
      (blockTensor T F (scalarBlock n v) p) = coefficientBlock n v p := by
  have h := DFunLike.congr_fun (scalarBlock_tensor_square T F E n v)
    ((F.matrix E (n+1)).symm p)
  change F.blocks E _ (blockTensor T F (scalarBlock n v) p) =
    coefficientBlock n v (F.matrix E (n+1) ((F.matrix E (n+1)).symm p)) at h
  rw [(F.matrix E (n+1)).apply_symm_apply] at h
  exact h

/-- The actual initial common projection followed by a given actual scalar
common inclusion tensor the coefficient identity. -/
def commonTensorProjection {E : Algebra.{u}} {n : ℕ}
    (p q : coefficientMatrices E n) : T.tensor (scalarBlocks
      (CommonUnitProjection.commonSize n)) E :=
  (F.blocks E (CommonUnitProjection.commonSize n)).symm
    (CommonUnitProjection.commonProjection p q)

theorem commonTensorProjection_projection {E : Algebra.{u}} {n : ℕ}
    {p q : coefficientMatrices E n} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (commonTensorProjection T F p q) :=
  (CommonUnitProjection.commonProjection_projection hp hq).map
    (F.blocks E (CommonUnitProjection.commonSize n)).symm

theorem commonTensorProjection_nonzero {E : Algebra.{u}} [Nontrivial E] {n : ℕ}
    (p q : coefficientMatrices E n) : commonTensorProjection T F p q ≠ 0 := by
  intro h
  have hh := congrArg (F.blocks E (CommonUnitProjection.commonSize n)) h
  rw [show F.blocks E (CommonUnitProjection.commonSize n)
    (commonTensorProjection T F p q) = CommonUnitProjection.commonProjection p q from
    (F.blocks E (CommonUnitProjection.commonSize n)).apply_symm_apply _, map_zero] at hh
  exact CommonUnitProjection.commonProjection_nonzero p q hh

def tensorProjection {A E : Algebra.{u}} {n : ℕ}
    (f : scalarBlocks (CommonUnitProjection.commonSize n) →⋆ₐ[ℂ] A)
    (p q : coefficientMatrices E n) : T.tensor A E :=
  T.unitalMap f (StarAlgHom.id ℂ E)
    ((F.blocks E (CommonUnitProjection.commonSize n)).symm
      (CommonUnitProjection.commonProjection p q))

/-- Literal actual-map binding of the common-stage projection and its product
image. This equality carries no K0 or KK hypothesis. -/
theorem commonTensorProjection_image {A E : Algebra.{u}} {n : ℕ}
    (f : scalarBlocks (CommonUnitProjection.commonSize n) →⋆ₐ[ℂ] A)
    (p q : coefficientMatrices E n) :
    T.unitalMap f (StarAlgHom.id ℂ E) (commonTensorProjection T F p q) =
      tensorProjection T F f p q := rfl

theorem tensorProjection_decomposition {A E : Algebra.{u}} {n : ℕ}
    (f : scalarBlocks (CommonUnitProjection.commonSize n) →⋆ₐ[ℂ] A)
    (p q : coefficientMatrices E n) :
    tensorProjection T F f p q =
    blockTensor T F (f.toNonUnitalStarAlgHom.comp (scalarBlock n 0))
      (CommonUnitProjection.stabilizedFin p) +
    blockTensor T F (f.toNonUnitalStarAlgHom.comp (scalarBlock n 1))
      (CommonUnitProjection.stabilizedFin q) := by
  have h (v : Fin 2) (r : coefficientMatrices E (n+1)) :
      (F.blocks E (CommonUnitProjection.commonSize n)).symm (coefficientBlock n v r) =
      blockTensor T F (scalarBlock n v) r := by
    apply (F.blocks E _).injective
    change F.blocks E (CommonUnitProjection.commonSize n)
      ((F.blocks E (CommonUnitProjection.commonSize n)).symm (coefficientBlock n v r)) =
      F.blocks E (CommonUnitProjection.commonSize n) (blockTensor T F (scalarBlock n v) r)
    rw [(F.blocks E (CommonUnitProjection.commonSize n)).apply_symm_apply,blockTensor_scalarBlock]
  unfold tensorProjection
  rw [commonProjection_decomposition,map_add,map_add,h,h]
  congr 1 <;> unfold blockTensor <;>
    simp only [NonUnitalStarAlgHom.comp_apply,
      StarAlgHom.coe_toNonUnitalStarAlgHom]
  all_goals
    change T.map _ _ (T.map _ _ _) = T.map _ _ _
    rw [← NonUnitalStarAlgHom.comp_apply,T.map_comp]
    rfl

/-- The tensor image is a projection because every map in its definition is an
actual star homomorphism. -/
theorem tensorProjection_projection {A E : Algebra.{u}} {n : ℕ}
    (f : scalarBlocks (CommonUnitProjection.commonSize n) →⋆ₐ[ℂ] A)
    {p q : coefficientMatrices E n} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (tensorProjection T F f p q) :=
  ((CommonUnitProjection.commonProjection_projection hp hq).map
    (F.blocks E (CommonUnitProjection.commonSize n)).symm).map _

/-- Injectivity of the scalar common inclusion suffices for the actual tensor
projection to remain nonzero, including p=q=0. -/
theorem tensorProjection_nonzero {A E : Algebra.{u}} [Nontrivial E] {n : ℕ}
    (f : scalarBlocks (CommonUnitProjection.commonSize n) →⋆ₐ[ℂ] A)
    (hf : Function.Injective f) (p q : coefficientMatrices E n) :
    tensorProjection T F f p q ≠ 0 := by
  intro h
  have ht := T.map_injective f.toNonUnitalStarAlgHom
    (NonUnitalStarAlgHom.id ℂ E) hf Function.injective_id
  have hzero : (F.blocks E (CommonUnitProjection.commonSize n)).symm
      (CommonUnitProjection.commonProjection p q) = 0 :=
    ht (h.trans (map_zero _).symm)
  have hh := congrArg (F.blocks E (CommonUnitProjection.commonSize n)) hzero
  rw [(F.blocks E (CommonUnitProjection.commonSize n)).apply_symm_apply,map_zero] at hh
  exact CommonUnitProjection.commonProjection_nonzero p q hh

end TensorImages

section ProjectionClasses
open TensorCoefficientChannels
universe u t
variable (T : Spatial.{u}) (F : FiniteTensorCoordinates T)

/-- Generic ordinary K0 support. Class values on non-projections are irrelevant.
The external laws here are the universal orthogonal-addition, stabilization,
and matrix-Morita/exterior-product laws (Blackadar, K-Theory, §§5.1--5.5,
17.8 and 18.9). They mention no graph, signed coordinate or unit target. -/
structure ProjectionK0 where
  group : Algebra.{u} → Type t
  abelian : ∀ A, AddCommGroup (group A)
  cl : ∀ A : Algebra.{u}, A → group A
  matrixClass : ∀ E n, coefficientMatrices E n → group E
  unitClass : ∀ E, group E
  exterior : ∀ A E, group A →+ (group E →+ group (T.tensor A E))
  orthogonal_add : ∀ (A : Algebra.{u}) (p q : A), IsStarProjection p → IsStarProjection q → p*q=0 →
    cl A (p+q) = cl A p + cl A q
  stabilize : ∀ E n (p : coefficientMatrices E n), IsStarProjection p →
    matrixClass E (n+1) (CommonUnitProjection.stabilizedFin p) =
      matrixClass E n p + unitClass E
  block_morita : ∀ (A E : Algebra.{u}) n (ψ : scalarMatrices (n+1) →⋆ₙₐ[ℂ] A)
    (p : coefficientMatrices E (n+1)), IsStarProjection p →
    cl (T.tensor A E) (blockTensor T F ψ p) =
      exterior A E (cl A (ψ (ULift.up (CStarMatrix.ofMatrix (Matrix.single 0 0 1)))))
        (matrixClass E (n+1) p)

attribute [instance] ProjectionK0.abelian

variable (P : ProjectionK0 T F)

/-- Universal reference-summand exterior formula, and naturality under the
chosen scalar KK equivalence tensor 1_E. The reference groups allow the
NONUNITAL reference C ⊕ S(C); no unital reference algebra is required here. `transport` and `scalarTransport` must
be the K0 actions of those actual classes. This is LOCAL binding data until
identified with the separately constructed kappa; it is not a final P-input. -/
structure ReferenceTransport (A E : Algebra.{u}) (H : Type*) [AddCommGroup H] where
  referenceGroup : Type t
  referenceTensorGroup : Type t
  referenceAbelian : AddCommGroup referenceGroup
  referenceTensorAbelian : AddCommGroup referenceTensorGroup
  referenceExterior : referenceGroup →+ (P.group E →+ referenceTensorGroup)
  scalarTransport : P.group A →+ referenceGroup
  tensorTransport : P.group (T.tensor A E) →+ referenceTensorGroup
  referenceCoordinate : referenceGroup →+ ℤ
  splitCoordinate : referenceTensorGroup →+ (P.group E × H)
  naturality : ∀ x y, tensorTransport (P.exterior A E x y) =
    referenceExterior (scalarTransport x) y
  reference_exterior : ∀ x y, splitCoordinate (referenceExterior x y) =
    (referenceCoordinate x • y,0)

attribute [instance] ReferenceTransport.referenceAbelian ReferenceTransport.referenceTensorAbelian

namespace ReferenceTransport
variable {T F P} {A E : Algebra.{u}} {H : Type*} [AddCommGroup H]
    (C : ReferenceTransport T F P A E H)

def coordinate : P.group (T.tensor A E) →+ (P.group E × H) :=
  C.splitCoordinate.comp C.tensorTransport

def scalarCoordinate : P.group A →+ ℤ :=
  C.referenceCoordinate.comp C.scalarTransport

theorem exterior_coordinate (x : P.group A) (y : P.group E) :
    C.coordinate (P.exterior A E x y) = (C.scalarCoordinate x • y,0) := by
  exact (congrArg C.splitCoordinate (C.naturality x y)).trans (C.reference_exterior _ y)
end ReferenceTransport

/-- The normalized INITIAL cokernel coordinate on each actual scalar block.
This is deliberately marked local: its construction from first-factor graph
normalization must use the same finite-cone coordinates as kappa. It is not a
published axiom and must not be supplied as a final theorem input. -/
structure InitialScalarCoordinate {A : Algebra.{u}} {n : ℕ}
    (f : scalarBlocks (CommonUnitProjection.commonSize n) →⋆ₐ[ℂ] A) where
  coordinate : P.group A →+ PositiveLifting.Cokernel InitialGraphPresentation.B
  first_factor_minimal : ∀ v : Fin 2,
    coordinate (P.cl A (f (scalarBlock n v (ULift.up (CStarMatrix.ofMatrix (Matrix.single 0 0 1)))))) =
      PositiveLifting.quotient InitialGraphPresentation.B (Pi.single v 1)

/-- From universal tensor/Morita laws and local scalar-coordinate bindings, the
ACTUAL common projection has signed coordinate ([p]-[q],0). Neither the desired
projection coordinate nor the prescribed unit equation is assumed. -/
theorem tensorProjection_coordinate {A E : Algebra.{u}} {H : Type*} [AddCommGroup H]
    {n : ℕ} (f : scalarBlocks (CommonUnitProjection.commonSize n) →⋆ₐ[ℂ] A)
    (C : ReferenceTransport T F P A E H) (G : InitialScalarCoordinate T F P f)
    (hbind : C.scalarCoordinate =
      InitialGraphPresentation.cokernelEquiv.toAddMonoidHom.comp G.coordinate)
    {p q : coefficientMatrices E n} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    C.coordinate (P.cl (T.tensor A E) (tensorProjection T F f p q)) =
      (P.matrixClass E n p - P.matrixClass E n q,0) := by
  let ψ (v : Fin 2) := f.toNonUnitalStarAlgHom.comp (scalarBlock n v)
  let bp := blockTensor T F (ψ 0) (CommonUnitProjection.stabilizedFin p)
  let bq := blockTensor T F (ψ 1) (CommonUnitProjection.stabilizedFin q)
  have hbp : IsStarProjection bp := (CommonUnitProjection.stabilizedFin_projection hp).map _
  have hbq : IsStarProjection bq := (CommonUnitProjection.stabilizedFin_projection hq).map _
  have hborth : bp*bq=0 := by
    let φ := (T.unitalMap f (StarAlgHom.id ℂ E)).comp
      (F.blocks E (CommonUnitProjection.commonSize n)).symm.toStarAlgHom
    have himage (v : Fin 2) (r : coefficientMatrices E (n+1)) :
        φ (coefficientBlock n v r) = blockTensor T F (ψ v) r := by
      have hh := blockTensor_scalarBlock T F E n v r
      have hh' : (F.blocks E (CommonUnitProjection.commonSize n)).symm
        (coefficientBlock n v r) = blockTensor T F (scalarBlock n v) r :=
        (F.blocks E (CommonUnitProjection.commonSize n)).symm_apply_eq.mpr hh.symm
      change T.unitalMap f (StarAlgHom.id ℂ E) ((F.blocks E _).symm _) = _
      rw [hh']
      change T.map _ _ (T.map _ _ _) = T.map _ _ _
      rw [← NonUnitalStarAlgHom.comp_apply,T.map_comp]
      rfl
    change blockTensor T F (ψ 0) _ * blockTensor T F (ψ 1) _ = 0
    rw [← himage,← himage,← map_mul,coefficientBlock_orthogonal,map_zero]
  have hs (v : Fin 2) : C.scalarCoordinate
      (P.cl A (ψ v (ULift.up (CStarMatrix.ofMatrix (Matrix.single 0 0 1))))) =
      (if v=0 then 1 else -1) := by
    rw [hbind]
    change InitialGraphPresentation.cokernelEquiv
      (G.coordinate (P.cl A (f (scalarBlock n v _)))) = _
    rw [G.first_factor_minimal,InitialGraphPresentation.cokernelEquiv_quotient]
    fin_cases v <;> simp
  rw [tensorProjection_decomposition,P.orthogonal_add _ _ _ hbp hbq hborth,map_add]
  rw [P.block_morita _ _ _ _ _ (CommonUnitProjection.stabilizedFin_projection hp),
    P.block_morita _ _ _ _ _ (CommonUnitProjection.stabilizedFin_projection hq),
    C.exterior_coordinate,C.exterior_coordinate]
  change ((C.scalarCoordinate (P.cl A (ψ 0 _))) • _, (0 : H)) +
    ((C.scalarCoordinate (P.cl A (ψ 1 _))) • _, (0 : H)) = _
  rw [hs,hs]
  simp only [show (1 : Fin 2) ≠ 0 by decide,
    ite_true, ite_false, one_zsmul, neg_one_zsmul, Prod.mk_add_mk, add_zero]
  rw [P.stabilize _ _ _ hp,P.stabilize _ _ _ hq]
  congr 1
  abel
/-- Standard Grothendieck projection picture for every unital coefficient
algebra (Blackadar 5.1.2,5.3.1,5.5.5). This is universal K0 support, not a
representation of a prescribed construction-specific class. -/
structure ProjectionRepresentatives where
  represent : ∀ (E : Algebra.{u}) (x : P.group E), ∃ (n : ℕ)
    (p q : coefficientMatrices E n), IsStarProjection p ∧ IsStarProjection q ∧
      P.matrixClass E n p - P.matrixClass E n q = x

/-- Pull back ANY target class through the coefficient-model equivalence and
then use the universal projection picture. In particular u may be [1_B].
The scalar augmentation vanishes because the class came from the ideal.
No target or coefficient UCT is used. -/
theorem prescribedClass_representative (R : ProjectionRepresentatives T F P)
    (E : Algebra.{u}) {I D : Type*} [AddCommGroup I] [AddCommGroup D]
    (ξ : I ≃+ D) (includeIdeal : I →+ P.group E)
    (augment : P.group E →+ ℤ) (hkernel : ∀ x, augment (includeIdeal x)=0)
    (toTarget : P.group E →+ D) (htarget : ∀ x, toTarget (includeIdeal x)=ξ x)
    (u : D) : ∃ (n : ℕ) (p q : coefficientMatrices E n),
      IsStarProjection p ∧ IsStarProjection q ∧
      P.matrixClass E n p - P.matrixClass E n q = includeIdeal (ξ.symm u) ∧
      augment (P.matrixClass E n p - P.matrixClass E n q) = 0 ∧
      toTarget (P.matrixClass E n p - P.matrixClass E n q) = u := by
  obtain ⟨n,p,q,hp,hq,h⟩ := R.represent E (includeIdeal (ξ.symm u))
  refine ⟨n,p,q,hp,hq,h,?_,?_⟩
  · rw [h]; exact hkernel _
  · rw [h,htarget,ξ.apply_symm_apply]

end ProjectionClasses

section FiniteConeNormalization
open TensorCoefficientChannels GraphChannelKKCalculation MultiplicityEmbeddings
open FiniteDiagram PositiveLifting CategoryTheory
universe u v w t s
variable (T : Spatial.{u}) (F : FiniteTensorCoordinates T) (P : ProjectionK0.{u,s} T F)
variable {K : Type v} [Category.{w} K] [Preadditive K]
    (J : CoefficientModelFromExtension.KKInterpretation.{0,v,w} (K := K))
    (G : GraphChannelKKCalculation.KTheory.{0,v,w,t} J)
    (N : FiniteK0Input) (U : FreeUCTInput J G) (V : FiniteConeInput J G N U)

/-- Standard finite-dimensional projection/rank interpretation of the SAME
finite K0 action N. `rank` means the integer vector of ordinary matrix ranks.
The minimal-projection and naturality laws quantify over every finite product
and every homomorphism. Blackadar §§5.1.2,5.2.1,5.2.3,5.3.1. -/
structure FiniteProjectionRanks where
  rank : ∀ {I : Type} [Fintype I] [DecidableEq I] {d : I → ℕ}, Blocks d → (I → ℤ)
  minimal : ∀ {I : Type} [Fintype I] [DecidableEq I] (d : I → ℕ)
    (i : I) (r : Fin (d i)),
    rank (Pi.single i (CStarMatrix.ofMatrix (Matrix.single r r (1 : ℂ)))) = Pi.single i 1
  naturality : ∀ {I L : Type} [Fintype I] [Fintype L] [DecidableEq I] [DecidableEq L]
    {d : I → ℕ} {e : L → ℕ} (_hd : ∀ i, 0 < d i) (_he : ∀ i, 0 < e i)
    (f : Blocks d →⋆ₐ[ℂ] Blocks e) (x : Blocks d), IsStarProjection x →
      rank (f x) = N.action f.toNonUnitalStarAlgHom (rank x)

/-- UNIVERSAL standard projection normalization for the actual finite-cone
coordinates already chosen by V. It applies to every positive finite presentation
and EVERY projection of its first factor. The comparison is ordinary K0
invariance under the explicit ULift star isomorphism. It neither mentions the
initial presentation nor the signed coefficient projection. Fima--Germain
Theorem 4.1 with its actual inclusion, and ordinary K0 projection naturality.
The field must be interpreted using the SAME K0 groups/classes as P and G. -/
structure FiniteConeProjectionInput (Rk : FiniteProjectionRanks N) where
  comparison : ∀ {I : Type} [Fintype I] [DecidableEq I]
    {B : Matrix I I ℤ} {k l : I → ℕ} (Q : FinitePresentation B k l),
      P.group (UniverseLift.algebra.{u} Q) ≃+ G.group false Q.actual
  left_projection : ∀ {I : Type} [Fintype I] [DecidableEq I]
    {B : Matrix I I ℤ} {k l : I → ℕ} (Q : FinitePresentation B k l)
    (x : Blocks (k+l)), IsStarProjection x →
      (V.coordinates Q).even (comparison Q
        (P.cl (UniverseLift.algebra Q) (ULift.up (Q.left x)))) = quotient B (Rk.rank x)

/-- Actual common inclusion into any of the already constructed finite products. -/
def finiteCommon {I : Type} [Fintype I] [DecidableEq I]
    {B : Matrix I I ℤ} {k l : I → ℕ} (Q : FinitePresentation B k l) :
    scalarBlocks.{u} (Sum.elim k l) →⋆ₐ[ℂ] UniverseLift.algebra Q :=
  UniverseLift.map (Q.left.comp (firstInclusion k l))

/-- The previously local initial scalar normalization is now DERIVED from a
universal finite-cone projection interpretation, finite matrix ranks, and the
literal multiplicity [I I] of the actual first inclusion. -/
def initialScalarCoordinate_of_finiteCone
    (Rk : FiniteProjectionRanks N) (C : FiniteConeProjectionInput T F P J G N U V Rk)
    {n : ℕ} (Q : FinitePresentation InitialGraphPresentation.B
      (fun _ : Fin 2 => n+1) (fun _ => 1)) :
    InitialScalarCoordinate T F P (finiteCommon Q) where
  coordinate := (V.coordinates Q).even.toAddMonoidHom.comp (C.comparison Q).toAddMonoidHom
  first_factor_minimal v := by
    let k : Fin 2 → ℕ := fun _ => n+1
    let l : Fin 2 → ℕ := fun _ => 1
    let x : Blocks (Sum.elim k l) :=
      coefficientBlock (E := ℂ) n v (CStarMatrix.ofMatrix (Matrix.single 0 0 1))
    have hx : IsStarProjection x := by
      apply IsStarProjection.map (f := coefficientBlock (E := ℂ) n v)
      constructor
      · change Matrix.single (0 : Fin (n+1)) 0 (1 : ℂ) * Matrix.single 0 0 1 = Matrix.single 0 0 1
        simpa only [mul_one] using (Matrix.single_mul_single_same (c := (1 : ℂ)) (0 : Fin (n+1)) 0 0 (1 : ℂ))
      · change (Matrix.single (0 : Fin (n+1)) 0 (1 : ℂ)).conjTranspose = Matrix.single 0 0 1
        simp
    change (V.coordinates Q).even (C.comparison Q
      (P.cl (UniverseLift.algebra Q) (ULift.up (Q.left (firstInclusion k l x))))) = _
    rw [C.left_projection Q _ (hx.map (firstInclusion k l))]
    have hk : ∀ i, 0 < k i := fun _ => Nat.succ_pos n
    have hd : ∀ i, 0 < Sum.elim k l i := by intro i; cases i <;> simp [k,l]
    apply congrArg (quotient InitialGraphPresentation.B)
    calc
      Rk.rank (firstInclusion k l x) =
          N.action (firstInclusion k l).toNonUnitalStarAlgHom (Rk.rank x) :=
        Rk.naturality hd (fun i => Nat.add_pos_left (hk i) _) (firstInclusion k l) x hx
      _ = Pi.single v 1 := by
        rw [N.multiplicity hd (fun i => Nat.add_pos_left (hk i) _) firstMultiplicity
          (firstInclusion k l) (intoDimensions_hasMultiplicity _ _ _ (first_targetSize k l))]
        have hr : Rk.rank x = Pi.single (Sum.inl v) 1 :=
          Rk.minimal (Sum.elim k l) (.inl v) ⟨0,Nat.succ_pos n⟩
        rw [hr]
        funext i
        simp [firstMultiplicity,Matrix.mulVec,Matrix.fromCols,dotProduct,
          Matrix.one_apply,Pi.single_apply,eq_comm]

/-- The scalar coordinate of the constructed KK equivalence is exactly the
normalization used above; this is the already proved kappa action theorem,
not a new input on the initial scalar signs. -/
theorem finiteCone_kappa_scalar
    (Rk : FiniteProjectionRanks N) (C : FiniteConeProjectionInput T F P J G N U V Rk)
    {n : ℕ} (Q : FinitePresentation InitialGraphPresentation.B
      (fun _ : Fin 2 => n+1) (fun _ => 1))
    {R : CoefficientModelFromExtension.Algebra} (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ)
    (x : P.group (UniverseLift.algebra.{u} Q)) :
    r₀ (G.action false
      (U.kappa J G (V.bootstrap Q) hR
        ((V.coordinates Q).even.trans InitialGraphPresentation.cokernelEquiv.toAddEquiv)
        ((V.coordinates Q).odd.trans InitialGraphPresentation.kernelEquiv.toAddEquiv) r₀ r₁).hom
      (C.comparison Q x)) =
    InitialGraphPresentation.cokernelEquiv
      ((initialScalarCoordinate_of_finiteCone T F P J G N U V Rk C Q).coordinate x) :=
  U.kappa_even J G (V.bootstrap Q) hR
    ((V.coordinates Q).even.trans InitialGraphPresentation.cokernelEquiv.toAddEquiv)
    ((V.coordinates Q).odd.trans InitialGraphPresentation.kernelEquiv.toAddEquiv) r₀ r₁ _

/-- Initial signed tensor coordinate with its scalar graph normalization
DISCHARGED by universal finite-cone projection naturality. `hscalar` only
identifies the scalar action of ReferenceTransport with the already constructed
kappa; it does not prescribe a generator or projection value. -/
theorem initialTensorProjection_coordinate
    (Rk : FiniteProjectionRanks N) (C : FiniteConeProjectionInput T F P J G N U V Rk)
    {n : ℕ} (Q : FinitePresentation InitialGraphPresentation.B
      (fun _ : Fin 2 => n+1) (fun _ => 1))
    {R : CoefficientModelFromExtension.Algebra} (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ)
    (E : TensorCoefficientChannels.Algebra.{u}) {H : Type*} [AddCommGroup H]
    (Ct : ReferenceTransport T F P (UniverseLift.algebra Q) E H)
    (hscalar : ∀ x, Ct.scalarCoordinate x = r₀ (G.action false
      (U.kappa J G (V.bootstrap Q) hR
        ((V.coordinates Q).even.trans InitialGraphPresentation.cokernelEquiv.toAddEquiv)
        ((V.coordinates Q).odd.trans InitialGraphPresentation.kernelEquiv.toAddEquiv) r₀ r₁).hom
      (C.comparison Q x)))
    {p q : coefficientMatrices E n} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    Ct.coordinate (P.cl (T.tensor (UniverseLift.algebra Q) E)
      (tensorProjection T F (finiteCommon Q) p q)) =
      (P.matrixClass E n p - P.matrixClass E n q,0) := by
  apply tensorProjection_coordinate T F P (finiteCommon Q) Ct
    (initialScalarCoordinate_of_finiteCone T F P J G N U V Rk C Q) _ hp hq
  ext x
  exact (hscalar x).trans (finiteCone_kappa_scalar T F P J G N U V Rk C Q hR r₀ r₁ x)

end FiniteConeNormalization

end Suzuki.PrescribedUnitCoordinate

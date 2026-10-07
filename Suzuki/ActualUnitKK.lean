import Suzuki.PrescribedUnitCoordinate
import Suzuki.CoefficientSchedule
import Suzuki.ActualCoefficientKK

/-!
# Representable actual KK unit calculation

All K0-to-KK identifications here are universal established-theory inputs.
The common-stage projection and its tensor image are the literal projections
constructed in `PrescribedUnitCoordinate`. No target or coefficient UCT is
used. A conditional theorem does not instantiate the external KK semantics.
-/
noncomputable section
open scoped CStarAlgebra ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Suzuki.ActualUnitKK
open CategoryTheory CategoryTheory.Preadditive
open TensorCoefficientChannels PrescribedUnitCoordinate

universe u v w t
variable {K : Type v} [Category.{w} K] [Preadditive K]

/-- The actual scalar algebra in the coefficient carrier universe. -/
abbrev scalar : CoefficientModelFromExtension.Algebra.{u} := ActualCoefficientKK.scalar.{u}

/-- A separable unital spatial object viewed as a nonunital admissible object.
No additional UCT or nuclearity predicate is part of admissibility. -/
abbrev actual (A : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) : CoefficientModelFromExtension.Algebra.{u} :=
  ActualCoefficientKK.actual A hA

/-- A projection defines the ACTUAL scalar star homomorphism z ↦ z p. -/
def projectionMap (A : CoefficientModelFromExtension.Algebra.{u}) (p : A) (hp : IsStarProjection p) :
    scalar.{u} →⋆ₙₐ[ℂ] A where
  toFun z := z.down • p
  map_zero' := zero_smul _ _
  map_add' z y := add_smul _ _ _
  map_mul' z y := by
    change (z.down*y.down) • p = (z.down • p)*(y.down • p)
    rw [smul_mul_smul_comm,hp.1]
  map_smul' z y := by
    change (z • y.down) • p = z • (y.down • p)
    exact mul_smul _ _ _
  map_star' z := by
    change (star z.down) • p = star (z.down • p)
    rw [star_smul,hp.2]

theorem projectionMap_naturality {A B : CoefficientModelFromExtension.Algebra.{u}}
    (f : A →⋆ₙₐ[ℂ] B) (p : A) (hp : IsStarProjection p) :
    f.comp (projectionMap A p hp) = projectionMap B (f p) (hp.map f) := by
  ext z
  exact map_smul f z.down p

variable (J : CoefficientModelFromExtension.KKInterpretation.{u,v,w} (K := K))

abbrev K0 (A : CoefficientModelFromExtension.Algebra.{u}) := J.object scalar ⟶ J.object A

/-- K0 functoriality is literally Kasparov postcomposition. -/
def action {A B : CoefficientModelFromExtension.Algebra.{u}} (f : J.object A ⟶ J.object B) : K0 J A →+ K0 J B where
  toFun x := x ≫ f
  map_zero' := Limits.zero_comp
  map_add' x y := by simp only [add_comp]

@[simp] theorem action_apply {A B : CoefficientModelFromExtension.Algebra.{u}}
    (f : J.object A ⟶ J.object B) (x : K0 J A) : action J f x = x ≫ f := rfl

@[simp] theorem action_id (A : CoefficientModelFromExtension.Algebra.{u}) :
    action J (𝟙 (J.object A)) = AddMonoidHom.id (K0 J A) := by
  ext x
  exact Category.comp_id _

theorem action_comp {A B D : CoefficientModelFromExtension.Algebra.{u}} (f : J.object A ⟶ J.object B)
    (g : J.object B ⟶ J.object D) : action J (f ≫ g) = (action J g).comp (action J f) := by
  ext x
  exact (Category.assoc _ _ _).symm

def isoAction {A B : CoefficientModelFromExtension.Algebra.{u}} (e : J.object A ≅ J.object B) : K0 J A ≃+ K0 J B where
  toFun x := x ≫ e.hom
  invFun y := y ≫ e.inv
  left_inv x := by simp only [Category.assoc,e.hom_inv_id,Category.comp_id]
  right_inv y := by simp only [Category.assoc,e.inv_hom_id,Category.comp_id]
  map_add' x y := by simp only [add_comp]

/-- EXTERNAL P3: K0(A)=KK(C,A), natural for EVERY KK class on separable
actual algebras. Meyer math/0702145v2, Section 4.3; RS 1987 Theorem 1.11
in its stated nuclear scope. No class value specific to this construction
is included. The scalar is the explicit universe lift above. -/
structure RepresentableInput (G : GraphChannelKKCalculation.KTheory J) where
  even : ∀ A : CoefficientModelFromExtension.Algebra.{u}, G.group false A ≃+ K0 J A
  naturality : ∀ {A B : CoefficientModelFromExtension.Algebra.{u}} (f : J.object A ⟶ J.object B)
    (x : G.group false A), even B (G.action false f x) = even A x ≫ f

/-- EXTERNAL P3/P8: ordinary K0 of separable unital algebras is representable
KK, with the class of a projection identified with its literal scalar map.
The quantifier is universal; no common projection or target unit is named. -/
structure ProjectionInterpretation (T : Spatial.{u}) (F : FiniteTensorCoordinates T)
    (P : ProjectionK0.{u,t} T F) where
  identify : ∀ (A : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A), P.group A ≃+ K0 J (actual A hA)
  projection : ∀ (A : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) (p : A) (hp : IsStarProjection p),
    identify A hA (P.cl A p) = J.map (projectionMap (actual A hA) p hp)

/-- Pulling a prescribed target class back uses the derived coefficient
equivalence; composition with its forward class returns the prescribed class. -/
theorem pullback_unit {F B : CoefficientModelFromExtension.Algebra.{u}} (ξ : J.object F ≅ J.object B)
    (unitB : K0 J B) : (isoAction J ξ).symm unitB ≫ ξ.hom = unitB :=
  (isoAction J ξ).apply_symm_apply unitB

/-- The generic split-unitization identity kills the scalar retraction on
every class coming from the ideal. This is a product calculation, not UCT. -/
theorem included_augmentation_zero (S : CoefficientModelFromExtension.SplitUnitizationInput J)
    (F : CoefficientModelFromExtension.Algebra.{u}) (hF : CoefficientModelFromExtension.Nuclear F) (x : K0 J F) :
    (x ≫ J.map (CoefficientModelFromExtension.unitizationInclusion F)) ≫ J.map (CoefficientModelFromExtension.scalarRetraction F) = 0 := by
  let i := J.map (CoefficientModelFromExtension.unitizationInclusion F)
  let r := CoefficientModelFromExtension.unitizationRetraction J S F hF
  have hir : i ≫ r = 𝟙 (J.object F) := CoefficientModelFromExtension.inclusion_retraction J S F hF
  have hri : r ≫ i = 𝟙 (J.object (CoefficientModelFromExtension.unitization F)) - J.map (CoefficientModelFromExtension.scalarRetraction F) :=
    CoefficientModelFromExtension.retraction_inclusion J S F hF
  have h : i ≫ J.map (CoefficientModelFromExtension.scalarRetraction F) = 0 := by
    have hi : i ≫ (𝟙 _ - J.map (CoefficientModelFromExtension.scalarRetraction F)) = i := by
      rw [← hri,← Category.assoc,hir,Category.id_comp]
    rw [comp_sub,Category.comp_id] at hi
    exact (sub_eq_self.mp hi)
  rw [Category.assoc,h,Limits.comp_zero]

/-- The scalar quotient into the specified universe-lifted scalar object. -/
def augmentation (F : CoefficientModelFromExtension.Algebra.{u}) :
    CoefficientModelFromExtension.unitization F →⋆ₙₐ[ℂ] scalar.{u} where
  toFun a := ULift.up (CoefficientModelFromExtension.scalarQuotient F a)
  map_zero' := congrArg ULift.up (map_zero _)
  map_add' a b := congrArg ULift.up (map_add _ a b)
  map_mul' a b := congrArg ULift.up (map_mul _ a b)
  map_smul' z a := congrArg ULift.up (map_smul _ z a)
  map_star' a := congrArg ULift.up (map_star _ a)

def scalarSection (F : CoefficientModelFromExtension.Algebra.{u}) :
    scalar.{u} →⋆ₙₐ[ℂ] CoefficientModelFromExtension.unitization F where
  toFun z := CoefficientModelFromExtension.scalarSection F z.down
  map_zero' := map_zero _
  map_add' a b := map_add _ a.down b.down
  map_mul' a b := map_mul _ a.down b.down
  map_smul' z a := map_smul _ z a.down
  map_star' a := map_star _ a.down

theorem augmentation_section (F : CoefficientModelFromExtension.Algebra.{u}) :
    (augmentation F).comp (scalarSection F) = NonUnitalStarAlgHom.id ℂ scalar := by
  ext z
  rfl

theorem section_augmentation (F : CoefficientModelFromExtension.Algebra.{u}) :
    (scalarSection F).comp (augmentation F) = CoefficientModelFromExtension.scalarRetraction F := by
  ext a
  rfl

/-- Actual scalar rank vanishes on ideal classes, before choosing any
projections. All maps are the concrete external-unitization maps. -/
theorem included_scalar_zero (S : CoefficientModelFromExtension.SplitUnitizationInput J)
    (F : CoefficientModelFromExtension.Algebra.{u}) (hF : CoefficientModelFromExtension.Nuclear F)
    (x : K0 J F) : (x ≫ J.map (CoefficientModelFromExtension.unitizationInclusion F)) ≫
      J.map (augmentation F) = 0 := by
  have h := included_augmentation_zero J S F hF x
  rw [← section_augmentation F,J.map_comp] at h
  have hh := congrArg (fun f => f ≫ J.map (augmentation F)) h
  have hs : J.map (scalarSection F) ≫ J.map (augmentation F) = 𝟙 (J.object scalar) := by
    rw [← J.map_comp,augmentation_section,J.map_id]
  simpa only [Category.assoc,hs,Category.comp_id,Limits.zero_comp] using hh

abbrev unitizationSeparable (F : CoefficientModelFromExtension.Algebra.{u}) :
    TopologicalSpace.SeparableSpace (CoefficientSchedule.E F) :=
  (CoefficientModelFromExtension.unitization F).separable

/-- Prescribed representatives over the ACTUAL coefficient unitization. The
class is pulled back through a derived coefficient equivalence, included in
the unitization, and represented by generic K0 projection support. -/
theorem prescribedRepresentatives
    (T : Spatial.{u}) (Ftc : FiniteTensorCoordinates T) (P : ProjectionK0.{u,t} T Ftc)
    (I : ProjectionInterpretation J T Ftc P) (R : ProjectionRepresentatives T Ftc P)
    (S : CoefficientModelFromExtension.SplitUnitizationInput J)
    {F B : CoefficientModelFromExtension.Algebra.{u}}
    (hF : CoefficientModelFromExtension.Nuclear F) (ξ : J.object F ≅ J.object B)
    (unitB : K0 J B) :
    ∃ (n : ℕ) (p q : coefficientMatrices (CoefficientSchedule.E F) n),
      IsStarProjection p ∧ IsStarProjection q ∧
      I.identify (CoefficientSchedule.E F) (unitizationSeparable F)
        (P.matrixClass (CoefficientSchedule.E F) n p - P.matrixClass (CoefficientSchedule.E F) n q) =
          (unitB ≫ ξ.inv) ≫ J.map (CoefficientModelFromExtension.unitizationInclusion F) ∧
      (I.identify (CoefficientSchedule.E F) (unitizationSeparable F)
        (P.matrixClass (CoefficientSchedule.E F) n p - P.matrixClass (CoefficientSchedule.E F) n q)) ≫
          J.map (augmentation F) = 0 ∧
      (I.identify (CoefficientSchedule.E F) (unitizationSeparable F)
        (P.matrixClass (CoefficientSchedule.E F) n p - P.matrixClass (CoefficientSchedule.E F) n q)) ≫
          CoefficientModelFromExtension.unitizationRetraction J S F hF ≫ ξ.hom = unitB := by
  let E := CoefficientSchedule.E F
  let e := I.identify E (unitizationSeparable F)
  let x : K0 J (CoefficientModelFromExtension.unitization F) :=
    (unitB ≫ ξ.inv) ≫ J.map (CoefficientModelFromExtension.unitizationInclusion F)
  obtain ⟨n,p,q,hp,hq,hpq⟩ := R.represent E (e.symm x)
  have h : e (P.matrixClass E n p - P.matrixClass E n q) = x := by
    rw [hpq,e.apply_symm_apply]
  refine ⟨n,p,q,hp,hq,h,?_,?_⟩
  · rw [h]
    exact included_scalar_zero J S F hF _
  · rw [h]
    dsimp [x]
    rw [← Category.assoc,Category.assoc (unitB ≫ ξ.inv),CoefficientModelFromExtension.inclusion_retraction,
      Category.comp_id,Category.assoc,ξ.inv_hom_id,Category.comp_id]

section Residual
variable {S E X : K} (Q : ConditionalKK.FirstCoordinate E X)

/-- A projection onto the actual scalar summand, together with the residual
class. This form needs no Kunneth theorem or assertion about coefficient K1. -/
def residualCoordinate : (S ⟶ X) →+ ((S ⟶ E) × (S ⟶ X)) where
  toFun x := (x ≫ Q.projection,x - (x ≫ Q.projection) ≫ Q.inclusion)
  map_zero' := by simp only [Limits.zero_comp,sub_zero]; rfl
  map_add' x y := by
    simp only [add_comp,Prod.mk_add_mk]
    congr 1
    abel

theorem residualCoordinate_inclusion (y : S ⟶ E) :
    residualCoordinate Q (y ≫ Q.inclusion) = (y,0) := by
  change ((y ≫ Q.inclusion) ≫ Q.projection,
    (y ≫ Q.inclusion) - ((y ≫ Q.inclusion) ≫ Q.projection) ≫ Q.inclusion) = _
  rw [Category.assoc,Q.retract,Category.comp_id,sub_self]

/-- A coordinate with zero residual determines the complete map, not only its
first-coordinate image. This is the equation needed by ConditionalAssembly. -/
theorem residualCoordinate_eq {x : S ⟶ X} {y : S ⟶ E}
    (h : residualCoordinate Q x = (y,0)) : x = y ≫ Q.inclusion := by
  have h₀ : x ≫ Q.projection = y := congrArg Prod.fst h
  have h₁ : x - (x ≫ Q.projection) ≫ Q.inclusion = 0 := congrArg Prod.snd h
  exact (sub_eq_zero.mp h₁).trans (congrArg (fun z => z ≫ Q.inclusion) h₀)
end Residual

section Reference
open ActualCoefficientKK GraphChannelKKCalculation
variable (X : ExteriorInput J) (U : ScalarTensorInput J X)

/-- The ordinary degree-zero exterior product, normalized through the
universal scalar-unit constraint. Its domain is literally KK(C,-). -/
def exteriorK0 (A E : CoefficientModelFromExtension.Algebra.{u}) :
    K0 J A →+ (K0 J E →+ K0 J (X.tensor A E)) where
  toFun x :=
    { toFun := fun y => (U.unit scalar).inv ≫ X.product x y
      map_zero' := by rw [map_zero,Limits.comp_zero]
      map_add' y z := by rw [map_add]; simp only [comp_add] }
  map_zero' := by
    ext y
    change (U.unit scalar).inv ≫ X.product (0 : K0 J A) y = 0
    simp only [map_zero,AddMonoidHom.zero_apply,Limits.comp_zero]
  map_add' x z := by
    ext y
    change (U.unit scalar).inv ≫ X.product (x+z) y =
      (U.unit scalar).inv ≫ X.product x y + (U.unit scalar).inv ≫ X.product z y
    simp only [map_add,AddMonoidHom.add_apply,comp_add]

theorem exteriorK0_naturality {A B E : CoefficientModelFromExtension.Algebra.{u}}
    (x : K0 J A) (y : K0 J E) (f : J.object A ⟶ J.object B) :
    exteriorK0 J X U A E x y ≫ X.product f (𝟙 (J.object E)) =
      exteriorK0 J X U B E (x ≫ f) y := by
  change ((U.unit scalar).inv ≫ X.product x y) ≫ X.product f (𝟙 _) = _
  rw [Category.assoc,← X.product_comp,Category.comp_id]
  rfl

/-- The actual scalar summand of C⊕SC acts as the first-coordinate inclusion.
Only the universal scalar-unit naturality and exterior composition are used. -/
theorem exteriorK0_referenceInclusion (E : CoefficientModelFromExtension.Algebra.{u})
    (y : K0 J E) :
    exteriorK0 J X U reference E (J.map referenceInclusion) y =
      y ≫ (U.first J X E).inclusion := by
  have hu := U.naturality y
  have hu' := congrArg (fun f => (U.unit scalar).inv ≫ f ≫ (U.unit E).inv) hu
  have hn : (U.unit scalar).inv ≫ X.product (𝟙 (J.object scalar)) y =
      y ≫ (U.unit E).inv := by
    simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id,Iso.inv_hom_id_assoc] using hu'
  change (U.unit scalar).inv ≫ X.product (J.map referenceInclusion) y =
    y ≫ ((U.unit E).inv ≫ X.product (J.map referenceInclusion) (𝟙 _))
  rw [← Category.id_comp (J.map referenceInclusion),← Category.comp_id y,X.product_comp]
  rw [← Category.assoc,hn,Category.assoc]
  simp only [Category.id_comp,Category.comp_id]

/-- EXTERNAL standard scalar/suspension/direct-sum K0. The actual scalar
summand is the generator; K0(SC)=0 and K0(C)=Z. This fixes a universal
reference normalization, not a graph projection or prescribed unit value.
Blackadar second edition (1998), §§5.1--5.5, 8.1 and 9.1; Meyer v2 Theorem
50 and §4.3. Actual endpoint suspension and ULift correspondence are external. -/
structure ReferenceK0Input where
  rank : K0 J reference ≃+ ℤ
  generator : rank (J.map referenceInclusion) = 1

namespace ReferenceK0Input
variable (R : ReferenceK0Input J)

theorem expansion (x : K0 J reference) : x = R.rank x • J.map referenceInclusion := by
  apply R.rank.injective
  rw [map_zsmul,R.generator]
  simp

end ReferenceK0Input

/-- EXTERNAL ordinary K0/exterior-product interpretation for ALL separable
unital factors. It binds the same generic K0 groups and the actual spatial
tensor comparison to Kasparov exterior products. No graph equivalence, channel,
reference transport, signed coordinate, target or coefficient UCT occurs. -/
structure ProjectionExteriorInput {T : Spatial.{u}} {Ftc : FiniteTensorCoordinates T}
    {P : ProjectionK0.{u,t} T Ftc} (I : ProjectionInterpretation J T Ftc P)
    (H : SpatialKKInput J T) (U : ScalarTensorInput J H.exterior) where
  naturality : ∀ (A E : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) (hE : TopologicalSpace.SeparableSpace E)
    (x : P.group A) (y : P.group E),
    I.identify (T.tensor A E) (H.separable A E hA hE) (P.exterior A E x y) =
      exteriorK0 J H.exterior U (actual A hA) (actual E hE)
        (I.identify A hA x) (I.identify E hE y) ≫ (H.binding J A E hA hE).hom

end Reference

section ActualTransport
open ActualCoefficientKK GraphChannelKKCalculation
variable (T : Spatial.{u}) (Ftc : FiniteTensorCoordinates T) (P : ProjectionK0.{u,w} T Ftc)
variable (I : ProjectionInterpretation J T Ftc P) (H : SpatialKKInput J T)
variable (U : ScalarTensorInput J H.exterior) (R : ReferenceK0Input J)
variable (PE : ProjectionExteriorInput J I H U)

def referenceSplit (E : TensorCoefficientChannels.Algebra.{u})
    (hE : TopologicalSpace.SeparableSpace E) :
    K0 J (H.exterior.tensor reference (actual E hE)) →+
      (P.group E × K0 J (H.exterior.tensor reference (actual E hE))) where
  toFun x := ((I.identify E hE).symm (x ≫ (U.first J H.exterior (actual E hE)).projection),
    x - (x ≫ (U.first J H.exterior (actual E hE)).projection) ≫
      (U.first J H.exterior (actual E hE)).inclusion)
  map_zero' := by simp only [Limits.zero_comp,map_zero,sub_zero]; rfl
  map_add' x y := by
    simp only [add_comp,map_add,Prod.mk_add_mk]
    congr 1
    abel

theorem referenceSplit_inclusion (E : TensorCoefficientChannels.Algebra.{u})
    (hE : TopologicalSpace.SeparableSpace E) (y : P.group E) :
    referenceSplit J T Ftc P I H U E hE
      ((I.identify E hE y) ≫ (U.first J H.exterior (actual E hE)).inclusion) = (y,0) := by
  change ((I.identify E hE).symm
    (((I.identify E hE y) ≫ _) ≫ (U.first J H.exterior (actual E hE)).projection),
    ((I.identify E hE y) ≫ _) -
    (((I.identify E hE y) ≫ _) ≫ (U.first J H.exterior (actual E hE)).projection) ≫ _) = _
  rw [Category.assoc,(U.first J H.exterior (actual E hE)).retract,Category.comp_id,
    AddEquiv.symm_apply_apply,sub_self]

/-- The local ReferenceTransport premise is constructed from representable
K0, actual κ tensor the identity, and the universal scalar-summand law. -/
def referenceTransport (A E : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) (hE : TopologicalSpace.SeparableSpace E)
    (κ : J.object (actual A hA) ≅ J.object reference) :
    ReferenceTransport T Ftc P A E (K0 J (H.exterior.tensor reference (actual E hE))) where
  referenceGroup := K0 J reference
  referenceTensorGroup := K0 J (H.exterior.tensor reference (actual E hE))
  referenceAbelian := inferInstance
  referenceTensorAbelian := inferInstance
  referenceExterior :=
    { toFun := fun x => (exteriorK0 J H.exterior U reference (actual E hE) x).comp
        (I.identify E hE).toAddMonoidHom
      map_zero' := by ext y; simp
      map_add' := by intro x z; ext y; simp }
  scalarTransport := (action J κ.hom).comp (I.identify A hA).toAddMonoidHom
  tensorTransport := (action J (H.coordinate J hA E hE κ).hom).comp
    (I.identify (T.tensor A E) (H.separable A E hA hE)).toAddMonoidHom
  referenceCoordinate := R.rank.toAddMonoidHom
  splitCoordinate := referenceSplit J T Ftc P I H U E hE
  naturality x y := by
    change (I.identify (T.tensor A E) (H.separable A E hA hE) (P.exterior A E x y)) ≫
      (H.coordinate J hA E hE κ).hom = _
    rw [PE.naturality]
    simp only [SpatialKKInput.coordinate,Iso.trans_hom,Iso.symm_hom,Category.assoc,
      Iso.hom_inv_id_assoc]
    exact exteriorK0_naturality J H.exterior U _ _ κ.hom
  reference_exterior x y := by
    change referenceSplit J T Ftc P I H U E hE
      (exteriorK0 J H.exterior U reference (actual E hE) x (I.identify E hE y)) = _
    rw [R.expansion J x,map_zsmul,AddMonoidHom.zsmul_apply,
      exteriorK0_referenceInclusion,map_zsmul,referenceSplit_inclusion]
    simp [R.generator]

end ActualTransport

section UniverseConeUnit
open Matrix PositiveLifting FiniteDiagram MultiplicityEmbeddings
open ActualCoefficientKK GraphChannelKKCalculation
variable (T : Spatial.{u}) (Ftc : FiniteTensorCoordinates T) (P : ProjectionK0.{u,w} T Ftc)
variable (I : ProjectionInterpretation J T Ftc P)
variable (G : KTheory.{u,v,w,t} J) (Rep : RepresentableInput J G)
variable (N : FiniteK0Input) (UCT : FreeUCTInput J G) (V : UniverseCone.Input J G N UCT)
variable (Rk : FiniteProjectionRanks N)

/-- UNIVERSAL standard projection normalization for the SAME actual finite
cone comparison as UniverseCone.Input. It quantifies over every positive
finite presentation and every first-factor projection. Representability
identifies the ordinary K0 group with the actual KK hom group; no initial
sign, common projection, prescribed coordinate or target unit is a field. -/
structure ProjectionConeInput : Prop where
  left_projection : ∀ {L : Type} [Fintype L] [DecidableEq L]
    {B : Matrix L L ℤ} {k l : L → ℕ} (Q : UniverseCone.Presentation.{u} B k l)
    (x : Blocks (k+l)), IsStarProjection x →
    (V.coordinates Q).even ((Rep.even Q.actual).symm
      (I.identify Q.algebra Q.separable (P.cl Q.algebra (Q.left (ULift.up x))))) =
        quotient B (Rk.rank x)

def finiteCommon {L : Type} [Fintype L] [DecidableEq L]
    {B : Matrix L L ℤ} {k l : L → ℕ} (Q : UniverseCone.Presentation.{u} B k l) :
    scalarBlocks.{u} (Sum.elim k l) →⋆ₐ[ℂ] Q.algebra :=
  Q.left.comp (UniverseLift.map (firstInclusion k l))

/-- The actual finite-cone coordinate fixes both initial scalar block signs
by the literal [I I] common inclusion, in every coefficient universe. -/
def initialScalarCoordinate (C : ProjectionConeInput J T Ftc P I G Rep N UCT V Rk)
    {n : ℕ} (Q : UniverseCone.Presentation.{u} InitialGraphPresentation.B
      (fun _ : Fin 2 => n+1) (fun _ => 1)) :
    InitialScalarCoordinate T Ftc P (finiteCommon Q) where
  coordinate := (V.coordinates Q).even.toAddMonoidHom.comp
    ((Rep.even Q.actual).symm.toAddMonoidHom.comp (I.identify Q.algebra Q.separable).toAddMonoidHom)
  first_factor_minimal v := by
    let k : Fin 2 → ℕ := fun _ => n+1
    let l : Fin 2 → ℕ := fun _ => 1
    let x : Blocks (Sum.elim k l) :=
      coefficientBlock (E := ℂ) n v (CStarMatrix.ofMatrix (Matrix.single 0 0 1))
    have hx : IsStarProjection x := by
      apply IsStarProjection.map (f := coefficientBlock (E := ℂ) n v)
      constructor
      · change Matrix.single (0 : Fin (n+1)) 0 (1 : ℂ) * Matrix.single 0 0 1 = Matrix.single 0 0 1
        simpa only [mul_one] using
          (Matrix.single_mul_single_same (c := (1 : ℂ)) (0 : Fin (n+1)) 0 0 (1 : ℂ))
      · change (Matrix.single (0 : Fin (n+1)) 0 (1 : ℂ)).conjTranspose = Matrix.single 0 0 1
        simp
    change (V.coordinates Q).even ((Rep.even Q.actual).symm
      (I.identify Q.algebra Q.separable
        (P.cl Q.algebra (Q.left (ULift.up (firstInclusion k l x)))))) = _
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

/-- Ordinary finite first-factor normalization for either initial matrix
presentation, before applying its scalar cokernel generator. -/
theorem commonMinimal_coordinate
    (C : ProjectionConeInput J T Ftc P I G Rep N UCT V Rk)
    {n : ℕ} {B : Matrix (Fin 2) (Fin 2) ℤ}
    (Q : UniverseCone.Presentation.{u} B (fun _ : Fin 2 => n+1) (fun _ => 1)) (v : Fin 2) :
    (V.coordinates Q).even ((Rep.even Q.actual).symm
      (I.identify Q.algebra Q.separable (P.cl Q.algebra
        (finiteCommon Q (scalarBlock n v
          (ULift.up (CStarMatrix.ofMatrix (Matrix.single 0 0 1)))))))) =
      quotient B (Pi.single v 1) := by
  let k : Fin 2 → ℕ := fun _ => n+1
  let l : Fin 2 → ℕ := fun _ => 1
  let x : Blocks (Sum.elim k l) :=
    coefficientBlock (E := ℂ) n v (CStarMatrix.ofMatrix (Matrix.single 0 0 1))
  have hx : IsStarProjection x := by
    apply IsStarProjection.map (f := coefficientBlock (E := ℂ) n v)
    constructor
    · change Matrix.single (0 : Fin (n+1)) 0 (1 : ℂ) * Matrix.single 0 0 1 = Matrix.single 0 0 1
      simpa only [mul_one] using
        (Matrix.single_mul_single_same (c := (1 : ℂ)) (0 : Fin (n+1)) 0 0 (1 : ℂ))
    · change (Matrix.single (0 : Fin (n+1)) 0 (1 : ℂ)).conjTranspose = Matrix.single 0 0 1
      simp
  change (V.coordinates Q).even ((Rep.even Q.actual).symm
    (I.identify Q.algebra Q.separable
      (P.cl Q.algebra (Q.left (ULift.up (firstInclusion k l x)))))) = _
  rw [C.left_projection Q _ (hx.map (firstInclusion k l))]
  have hk : ∀ i, 0 < k i := fun _ => Nat.succ_pos n
  have hd : ∀ i, 0 < Sum.elim k l i := by intro i; cases i <;> simp [k,l]
  apply congrArg (quotient B)
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

/-- Generic reference-generator normalization in the actual K-theory chosen
for scalar UCT. The generator is the actual scalar summand, independent of
every new graph or coefficient construction. -/
structure ReferenceGeneratorInput (R : ActualCoefficientKK.ReferenceInput J G UCT) : Prop where
  generator : R.even ((Rep.even reference).symm (J.map referenceInclusion)) = 1

def referenceK0 (R : ActualCoefficientKK.ReferenceInput J G UCT)
    (Rg : ReferenceGeneratorInput J G Rep UCT R) : ReferenceK0Input J where
  rank := (Rep.even reference).symm.trans R.even
  generator := Rg.generator

def initialKappa {n : ℕ} (Q : UniverseCone.Presentation.{u} InitialGraphPresentation.B
    (fun _ : Fin 2 => n+1) (fun _ => 1)) (R : ActualCoefficientKK.ReferenceInput J G UCT) :
    J.object Q.actual ≅ J.object reference :=
  UCT.kappa J G (V.bootstrap Q) R.bootstrap
    ((V.coordinates Q).even.trans InitialGraphPresentation.cokernelEquiv.toAddEquiv)
    ((V.coordinates Q).odd.trans InitialGraphPresentation.kernelEquiv.toAddEquiv) R.even R.odd

variable (H : SpatialKKInput J T) (U : ScalarTensorInput J H.exterior)
variable (PE : ProjectionExteriorInput J I H U)

/-- The scalar action of actual κ is the SAME finite-cone normalization. The
formerly local hscalar binding is proved using representability and κ_even. -/
theorem initialKappa_scalar (C : ProjectionConeInput J T Ftc P I G Rep N UCT V Rk)
    {n : ℕ} (Q : UniverseCone.Presentation.{u} InitialGraphPresentation.B
      (fun _ : Fin 2 => n+1) (fun _ => 1))
    (R : ActualCoefficientKK.ReferenceInput J G UCT) (Rg : ReferenceGeneratorInput J G Rep UCT R)
    (E : TensorCoefficientChannels.Algebra.{u}) (hE : TopologicalSpace.SeparableSpace E)
    (x : P.group Q.algebra) :
    (referenceTransport J T Ftc P I H U (referenceK0 J G Rep UCT R Rg) PE
      Q.algebra E Q.separable hE (initialKappa J G N UCT V Q R)).scalarCoordinate x =
    InitialGraphPresentation.cokernelEquiv
      ((initialScalarCoordinate J T Ftc P I G Rep N UCT V Rk C Q).coordinate x) := by
  change R.even ((Rep.even reference).symm
    ((I.identify Q.algebra Q.separable x) ≫ (initialKappa J G N UCT V Q R).hom)) = _
  have hn := Rep.naturality (initialKappa J G N UCT V Q R).hom
    ((Rep.even Q.actual).symm (I.identify Q.algebra Q.separable x))
  rw [AddEquiv.apply_symm_apply] at hn
  rw [← hn,AddEquiv.symm_apply_apply]
  exact UCT.kappa_even J G (V.bootstrap Q) R.bootstrap
    ((V.coordinates Q).even.trans InitialGraphPresentation.cokernelEquiv.toAddEquiv)
    ((V.coordinates Q).odd.trans InitialGraphPresentation.kernelEquiv.toAddEquiv)
    R.even R.odd _

/-- The signed pair coordinate is DERIVED for the actual tensor projection,
with neither ReferenceTransport nor hscalar left as a local premise. -/
theorem initialTensor_coordinate (C : ProjectionConeInput J T Ftc P I G Rep N UCT V Rk)
    {n : ℕ} (Q : UniverseCone.Presentation.{u} InitialGraphPresentation.B
      (fun _ : Fin 2 => n+1) (fun _ => 1))
    (R : ActualCoefficientKK.ReferenceInput J G UCT) (Rg : ReferenceGeneratorInput J G Rep UCT R)
    (E : TensorCoefficientChannels.Algebra.{u}) (hE : TopologicalSpace.SeparableSpace E)
    {p q : coefficientMatrices E n} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (referenceTransport J T Ftc P I H U (referenceK0 J G Rep UCT R Rg) PE
      Q.algebra E Q.separable hE (initialKappa J G N UCT V Q R)).coordinate
        (P.cl (T.tensor Q.algebra E) (tensorProjection T Ftc (finiteCommon Q) p q)) =
      (P.matrixClass E n p - P.matrixClass E n q,0) := by
  apply tensorProjection_coordinate T Ftc P (finiteCommon Q)
    (referenceTransport J T Ftc P I H U (referenceK0 J G Rep UCT R Rg) PE
      Q.algebra E Q.separable hE (initialKappa J G N UCT V Q R))
    (initialScalarCoordinate J T Ftc P I G Rep N UCT V Rk C Q) _ hp hq
  ext x
  exact initialKappa_scalar J T Ftc P I G Rep N UCT V Rk H U PE C Q R Rg E hE x

include PE in
/-- Exact actual-map stage equation, including the zero residual. This is
stronger than equality only after projecting onto the first K0 coordinate. -/
theorem initialProjection_class (C : ProjectionConeInput J T Ftc P I G Rep N UCT V Rk)
    {n : ℕ} (Q : UniverseCone.Presentation.{u} InitialGraphPresentation.B
      (fun _ : Fin 2 => n+1) (fun _ => 1))
    (R : ActualCoefficientKK.ReferenceInput J G UCT) (Rg : ReferenceGeneratorInput J G Rep UCT R)
    (E : TensorCoefficientChannels.Algebra.{u}) (hE : TopologicalSpace.SeparableSpace E)
    {p q : coefficientMatrices E n} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    J.map (projectionMap (actual (T.tensor Q.algebra E) (H.separable Q.algebra E Q.separable hE))
      (tensorProjection T Ftc (finiteCommon Q) p q) (tensorProjection_projection T Ftc _ hp hq)) ≫
      (H.coordinate J Q.separable E hE (initialKappa J G N UCT V Q R)).hom =
    (I.identify E hE (P.matrixClass E n p - P.matrixClass E n q)) ≫
      (U.first J H.exterior (actual E hE)).inclusion := by
  have h := initialTensor_coordinate J T Ftc P I G Rep N UCT V Rk H U PE C Q R Rg E hE hp hq
  let z := I.identify (T.tensor Q.algebra E) (H.separable Q.algebra E Q.separable hE)
    (P.cl (T.tensor Q.algebra E) (tensorProjection T Ftc (finiteCommon Q) p q)) ≫
    (H.coordinate J Q.separable E hE (initialKappa J G N UCT V Q R)).hom
  change referenceSplit J T Ftc P I H U E hE z = _ at h
  have h₀ : z ≫ (U.first J H.exterior (actual E hE)).projection =
      I.identify E hE (P.matrixClass E n p - P.matrixClass E n q) := by
    exact (I.identify E hE).symm_apply_eq.mp (congrArg Prod.fst h)
  have h₁ : z - (z ≫ (U.first J H.exterior (actual E hE)).projection) ≫
      (U.first J H.exterior (actual E hE)).inclusion = 0 := congrArg Prod.snd h
  have hz := (sub_eq_zero.mp h₁).trans (congrArg
    (fun a => a ≫ (U.first J H.exterior (actual E hE)).inclusion) h₀)
  dsimp [z] at hz
  rw [I.projection _ _ _ (tensorProjection_projection T Ftc _ hp hq)] at hz
  exact hz

include PE in
/-- The unit-stage equation needed by ConditionalAssembly, with the actual
common tensor projection and the derived coefficient splitting. -/
theorem initialProjection_prescribed (C : ProjectionConeInput J T Ftc P I G Rep N UCT V Rk)
    {n : ℕ} (Q : UniverseCone.Presentation.{u} InitialGraphPresentation.B
      (fun _ : Fin 2 => n+1) (fun _ => 1))
    (R : ActualCoefficientKK.ReferenceInput J G UCT) (Rg : ReferenceGeneratorInput J G Rep UCT R)
    (S : CoefficientModelFromExtension.SplitUnitizationInput J)
    {F B : CoefficientModelFromExtension.Algebra.{u}} (hF : CoefficientModelFromExtension.Nuclear F)
    (ξ : J.object F ≅ J.object B) (unitB : K0 J B)
    {p q : coefficientMatrices (CoefficientSchedule.E F) n} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hrep : I.identify (CoefficientSchedule.E F) (unitizationSeparable F)
      (P.matrixClass (CoefficientSchedule.E F) n p - P.matrixClass (CoefficientSchedule.E F) n q) =
        (unitB ≫ ξ.inv) ≫ J.map (CoefficientModelFromExtension.unitizationInclusion F)) :
    J.map (projectionMap (actual (T.tensor Q.algebra (CoefficientSchedule.E F))
      (H.separable Q.algebra (CoefficientSchedule.E F) Q.separable (unitizationSeparable F)))
      (tensorProjection T Ftc (finiteCommon Q) p q) (tensorProjection_projection T Ftc _ hp hq)) ≫
      (H.coordinate J Q.separable (CoefficientSchedule.E F) (unitizationSeparable F)
        (initialKappa J G N UCT V Q R)).hom =
      (unitB ≫ ξ.inv) ≫ (U.splitting J H.exterior S F hF).j := by
  rw [initialProjection_class J T Ftc P I G Rep N UCT V Rk H U PE C Q R Rg _ _ hp hq,hrep]
  exact Category.assoc _ _ _

end UniverseConeUnit

section StageZero
open Matrix PositiveLifting FiniteDiagram MultiplicityEmbeddings
open ActualCoefficientKK GraphChannelKKCalculation RecursiveGraphSequence
variable (T : Spatial.{u}) (Ftc : FiniteTensorCoordinates T) (P : ProjectionK0.{u,w} T Ftc)
variable (I : ProjectionInterpretation J T Ftc P)
variable (G : KTheory.{u,v,w,t} J) (Rep : RepresentableInput J G)
variable (N : FiniteK0Input) (UCT : FreeUCTInput J G) (V : UniverseCone.Input J G N UCT)
variable (Rk : FiniteProjectionRanks N)
variable (C : ProjectionConeInput J T Ftc P I G Rep N UCT V Rk)
variable (Gi : GraphCoefficientLimit.GraphInput.{u})
variable (H : SpatialKKInput J T) (U : ScalarTensorInput J H.exterior)
variable (PE : ProjectionExteriorInput J I H U)

abbrev initialStage (n : ℕ) : Stage := Stage.initial
  (fun _ => n+1) (fun _ => 1) (fun _ => Nat.zero_lt_succ n) (fun _ => by decide)

def stageZeroScalarCoordinate (Rk : FiniteProjectionRanks N)
    (C : ProjectionConeInput J T Ftc P I G Rep N UCT V Rk)
    (Gi : GraphCoefficientLimit.GraphInput.{u}) (n : ℕ) :
    InitialScalarCoordinate T Ftc P (finiteCommon (UniverseCone.Input.stagePresentation Gi (initialStage n))) where
  coordinate := InitialGraphPresentation.cokernelEquiv.symm.toAddMonoidHom.comp
    ((initialStage n).cokernel.toAddMonoidHom.comp
      ((V.coordinates (UniverseCone.Input.stagePresentation Gi (initialStage n))).even.toAddMonoidHom.comp
        ((Rep.even (UniverseCone.Input.stageActual Gi (initialStage n))).symm.toAddMonoidHom.comp
          (I.identify _ (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable).toAddMonoidHom)))
  first_factor_minimal v := by
    apply InitialGraphPresentation.cokernelEquiv.injective
    change InitialGraphPresentation.cokernelEquiv (InitialGraphPresentation.cokernelEquiv.symm
      ((initialStage n).cokernel
        ((V.coordinates (UniverseCone.Input.stagePresentation Gi (initialStage n))).even
          ((Rep.even (UniverseCone.Input.stageActual Gi (initialStage n))).symm
            (I.identify _ (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable
              (P.cl _ (finiteCommon (UniverseCone.Input.stagePresentation Gi (initialStage n))
                (scalarBlock n v (ULift.up (CStarMatrix.ofMatrix (Matrix.single 0 0 1))))))))))) = _
    rw [LinearEquiv.apply_symm_apply,InitialGraphPresentation.cokernelEquiv_quotient]
    have hm := commonMinimal_coordinate J T Ftc P I G Rep N UCT V Rk C
      (UniverseCone.Input.stagePresentation Gi (initialStage n)) v
    have hm' := congrArg (initialStage n).cokernel hm
    apply hm'.trans
    change InitialGraphPresentation.transportedCokernel 1 isUnit_one
      (quotient (1 * InitialGraphPresentation.B) (Pi.single v 1)) = _
    simpa only [Matrix.one_mulVec] using
      (InitialGraphPresentation.transportedCokernel_quotient 1 isUnit_one (Pi.single v 1))

theorem stageZero_scalar (n : ℕ)
    (R : ActualCoefficientKK.ReferenceInput J G UCT) (Rg : ReferenceGeneratorInput J G Rep UCT R)
    (E : TensorCoefficientChannels.Algebra.{u}) (hE : TopologicalSpace.SeparableSpace E)
    (x : P.group (UniverseCone.Input.stagePresentation Gi (initialStage n)).algebra) :
    (referenceTransport J T Ftc P I H U (referenceK0 J G Rep UCT R Rg) PE
      (UniverseCone.Input.stagePresentation Gi (initialStage n)).algebra E
      (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable hE
      (V.kappa J G Gi (initialStage n) R.bootstrap R.even R.odd)).scalarCoordinate x =
    InitialGraphPresentation.cokernelEquiv
      ((stageZeroScalarCoordinate J T Ftc P I G Rep N UCT V Rk C Gi n).coordinate x) := by
  change R.even ((Rep.even reference).symm
    ((I.identify _ (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable x) ≫
      (V.kappa J G Gi (initialStage n) R.bootstrap R.even R.odd).hom)) = _
  have hn := Rep.naturality (V.kappa J G Gi (initialStage n) R.bootstrap R.even R.odd).hom
    ((Rep.even (UniverseCone.Input.stageActual Gi (initialStage n))).symm
      (I.identify _ (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable x))
  rw [AddEquiv.apply_symm_apply] at hn
  rw [← hn,AddEquiv.symm_apply_apply]
  have hk := UCT.kappa_even J G (V.bootstrap (UniverseCone.Input.stagePresentation Gi (initialStage n))) R.bootstrap
      ((V.coordinates (UniverseCone.Input.stagePresentation Gi (initialStage n))).even.trans
        (initialStage n).cokernel.toAddEquiv)
      ((V.coordinates (UniverseCone.Input.stagePresentation Gi (initialStage n))).odd.trans
        (initialStage n).kernel.toAddEquiv) R.even R.odd
      ((Rep.even (UniverseCone.Input.stageActual Gi (initialStage n))).symm
        (I.identify _ (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable x))
  change _ = InitialGraphPresentation.cokernelEquiv (InitialGraphPresentation.cokernelEquiv.symm
    ((initialStage n).cokernel ((V.coordinates (UniverseCone.Input.stagePresentation Gi (initialStage n))).even
      ((Rep.even (UniverseCone.Input.stageActual Gi (initialStage n))).symm
        (I.identify _ (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable x)))))
  rw [LinearEquiv.apply_symm_apply]
  exact hk

include C PE in
/-- The ACTUAL recursive stage-zero κ has the signed common-projection
coordinate. This uses exactly the same κ as the bond calculation. -/
theorem stageZero_projection_class (n : ℕ)
    (R : ActualCoefficientKK.ReferenceInput J G UCT) (Rg : ReferenceGeneratorInput J G Rep UCT R)
    (E : TensorCoefficientChannels.Algebra.{u}) (hE : TopologicalSpace.SeparableSpace E)
    {p q : coefficientMatrices E n} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    J.map (projectionMap
      (actual (T.tensor (UniverseCone.Input.stagePresentation Gi (initialStage n)).algebra E)
        (H.separable _ E (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable hE))
      (tensorProjection T Ftc (finiteCommon (UniverseCone.Input.stagePresentation Gi (initialStage n))) p q)
      (tensorProjection_projection T Ftc _ hp hq)) ≫
      (H.coordinate J (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable E hE
        (V.kappa J G Gi (initialStage n) R.bootstrap R.even R.odd)).hom =
      (I.identify E hE (P.matrixClass E n p - P.matrixClass E n q)) ≫
        (U.first J H.exterior (actual E hE)).inclusion := by
  let Q := UniverseCone.Input.stagePresentation Gi (initialStage n)
  let κ := V.kappa J G Gi (initialStage n) R.bootstrap R.even R.odd
  let Ct := referenceTransport J T Ftc P I H U (referenceK0 J G Rep UCT R Rg) PE
    Q.algebra E Q.separable hE κ
  have h := tensorProjection_coordinate T Ftc P (finiteCommon Q) Ct
    (stageZeroScalarCoordinate J T Ftc P I G Rep N UCT V Rk C Gi n)
    (AddMonoidHom.ext (stageZero_scalar J T Ftc P I G Rep N UCT V Rk C Gi H U PE n R Rg E hE)) hp hq
  let z := I.identify (T.tensor Q.algebra E) (H.separable Q.algebra E Q.separable hE)
    (P.cl (T.tensor Q.algebra E) (tensorProjection T Ftc (finiteCommon Q) p q)) ≫
    (H.coordinate J Q.separable E hE κ).hom
  change referenceSplit J T Ftc P I H U E hE z = _ at h
  have h₀ : z ≫ (U.first J H.exterior (actual E hE)).projection =
      I.identify E hE (P.matrixClass E n p - P.matrixClass E n q) :=
    (I.identify E hE).symm_apply_eq.mp (congrArg Prod.fst h)
  have h₁ : z - (z ≫ (U.first J H.exterior (actual E hE)).projection) ≫
      (U.first J H.exterior (actual E hE)).inclusion = 0 := congrArg Prod.snd h
  have hz := (sub_eq_zero.mp h₁).trans (congrArg
    (fun a => a ≫ (U.first J H.exterior (actual E hE)).inclusion) h₀)
  dsimp [z] at hz
  rw [I.projection _ _ _ (tensorProjection_projection T Ftc _ hp hq)] at hz
  exact hz

include C PE in
/-- Exact prescribed-unit equation at the actual recursive initial stage.
Together with prescribedRepresentatives, its representative equation is
derived from standard projection support and the coefficient equivalence. -/
theorem stageZero_projection_prescribed (n : ℕ)
    (R : ActualCoefficientKK.ReferenceInput J G UCT) (Rg : ReferenceGeneratorInput J G Rep UCT R)
    (S : CoefficientModelFromExtension.SplitUnitizationInput J)
    {F B : CoefficientModelFromExtension.Algebra.{u}} (hF : CoefficientModelFromExtension.Nuclear F)
    (ξ : J.object F ≅ J.object B) (unitB : K0 J B)
    {p q : coefficientMatrices (CoefficientSchedule.E F) n} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hrep : I.identify (CoefficientSchedule.E F) (unitizationSeparable F)
      (P.matrixClass (CoefficientSchedule.E F) n p - P.matrixClass (CoefficientSchedule.E F) n q) =
        (unitB ≫ ξ.inv) ≫ J.map (CoefficientModelFromExtension.unitizationInclusion F)) :
    J.map (projectionMap
      (actual (T.tensor (UniverseCone.Input.stagePresentation Gi (initialStage n)).algebra (CoefficientSchedule.E F))
        (H.separable _ _ (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable (unitizationSeparable F)))
      (tensorProjection T Ftc (finiteCommon (UniverseCone.Input.stagePresentation Gi (initialStage n))) p q)
      (tensorProjection_projection T Ftc _ hp hq)) ≫
      (H.coordinate J (UniverseCone.Input.stagePresentation Gi (initialStage n)).separable
        (CoefficientSchedule.E F) (unitizationSeparable F)
        (V.kappa J G Gi (initialStage n) R.bootstrap R.even R.odd)).hom =
      (unitB ≫ ξ.inv) ≫ (U.splitting J H.exterior S F hF).j := by
  rw [stageZero_projection_class J T Ftc P I G Rep N UCT V Rk C Gi H U PE
    n R Rg _ _ hp hq,hrep]
  exact Category.assoc _ _ _

end StageZero

end Suzuki.ActualUnitKK

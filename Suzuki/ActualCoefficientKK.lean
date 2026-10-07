import Suzuki.GraphChannelKKCalculation
import Suzuki.ActualGraphCoefficientSystem
import Suzuki.GraphCoefficientLimit

/-!
# Actual spatial coefficient bond classes

Universal standard parameters are explicit. `SpatialKKInput` identifies the
nonunital exterior tensor with the SAME `Spatial` tensor and maps used by the
constructed channels. No coefficient or target UCT is used. The scalar finite
cone interface is generalized to actual lifted finite blocks in universe u.

Sources and external interpretation obligations: Fima--Germain
arXiv:1510.02418v3, Theorem 4.1, for the actual comparison and cone naturality;
Rosenberg--Schochet Duke 55 (1987), Theorem 1.17/Proposition 7.1, for free-source
UCT; Meyer arXiv:math/0702145v2, Section 4.1 (minimal tensor extension and unit
constraints), Section 4.2 (split exactness), Section 4.3 (K-theory). Actual
KK objects/classes, chosen scalar generators, finite-cone signs, and actual
minimal-tensor equivalences remain external correspondence obligations.
-/
noncomputable section
open scoped CStarAlgebra ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 2000000
namespace Suzuki.ActualCoefficientKK
open CategoryTheory CategoryTheory.Preadditive
open TensorCoefficientChannels ActualGraphCoefficientSystem RecursiveGraphSequence
open GraphChannelKKCalculation
attribute [local irreducible] graphProduct graphFirst graphSecond
universe u v w t

/-- The actual separable unital algebra viewed in the nonunital KK domain. -/
abbrev actual (A : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) : CoefficientModelFromExtension.Algebra.{u} :=
  ⟨A, inferInstance, hA⟩

variable {K : Type v} [Category.{w} K] [Preadditive K]
variable (J : CoefficientModelFromExtension.KKInterpretation.{u,v,w} (K := K))

/-- An actual star algebra equivalence induces a KK isomorphism by functoriality. -/
def mapIso {A B : CoefficientModelFromExtension.Algebra.{u}} (e : A ≃⋆ₐ[ℂ] B) :
    J.object A ≅ J.object B where
  hom := J.map e.toNonUnitalStarAlgHom
  inv := J.map e.symm.toNonUnitalStarAlgHom
  hom_inv_id := by
    rw [← J.map_comp]
    have h : e.symm.toNonUnitalStarAlgHom.comp e.toNonUnitalStarAlgHom =
        NonUnitalStarAlgHom.id ℂ A := by ext a; exact e.symm_apply_apply a
    rw [h, J.map_id]
  inv_hom_id := by
    rw [← J.map_comp]
    have h : e.toNonUnitalStarAlgHom.comp e.symm.toNonUnitalStarAlgHom =
        NonUnitalStarAlgHom.id ℂ B := by ext b; exact e.apply_symm_apply b
    rw [h, J.map_id]

/-- The literal rank-one matrix-corner inclusion, at a specified finite index. -/
def matrixCorner (A : TensorCoefficientChannels.Algebra.{u}) (q : ℕ)
    (r : ULift.{u} (Fin q)) : A →⋆ₙₐ[ℂ] amplification A q where
  toFun a := CStarMatrix.ofMatrix (Matrix.single r r a)
  map_zero' := by change Matrix.single r r (0 : A) = (0 : Matrix _ _ A); simp
  map_add' a b := by change Matrix.single r r (a+b) = _; exact Matrix.single_add r r a b
  map_mul' a b := by change Matrix.single r r (a*b) = _; exact (Matrix.single_mul_single_same a r r r b).symm
  map_smul' z a := by change Matrix.single r r (z • a) = _; exact (Matrix.smul_single z r r a).symm
  map_star' a := by
    change Matrix.single r r (star a) = (Matrix.single r r a).conjTranspose
    exact (Matrix.conjTranspose_single r r a).symm


/-- Universal standard finite matrix support and rank-one Morita. RS 1987
Theorem 1.11(5) for stabilization; Blackadar K-Theory second edition,
17.8.2(c),17.8.8, for the actual a↦a⊗e_rr map; Meyer v2 stability.
This does not mention the constructed noise channel or its class. -/
structure MatrixInput where
  separable : ∀ (A : TensorCoefficientChannels.Algebra.{u}) q,
    TopologicalSpace.SeparableSpace A → TopologicalSpace.SeparableSpace (amplification A q)
  scalar_separable : ∀ q, TopologicalSpace.SeparableSpace (matrixAlgebra.{u} q)
  corner_isIso : ∀ (A : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) q (r : ULift.{u} (Fin q)),
    IsIso (J.map (A := actual A hA) (B := actual (amplification A q) (separable A q hA))
      (matrixCorner A q r))

theorem zero_of_corner (M : MatrixInput J) (A B : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) (hB : TopologicalSpace.SeparableSpace B)
    (q : ℕ) (r : ULift.{u} (Fin q)) (f : amplification A q →⋆ₙₐ[ℂ] B)
    (h : J.map (A := actual A hA) (B := actual B hB) (f.comp (matrixCorner A q r)) = 0) :
    J.map (A := actual (amplification A q) (M.separable A q hA)) (B := actual B hB) f = 0 := by
  let := M.corner_isIso A hA q r
  rw [J.map_comp (B := actual (amplification A q) (M.separable A q hA))] at h
  apply (cancel_epi (J.map (A := actual A hA)
    (B := actual (amplification A q) (M.separable A q hA)) (matrixCorner A q r))).mp
  simpa using h


/-- Universal P1/P3 supporting tensor facts. The comparison has a literal
map square for EVERY pair of actual maps, rather than a desired bond class. -/
structure SpatialKKInput (T : Spatial.{u}) where
  exterior : ExteriorInput J
  separable : ∀ (A B : TensorCoefficientChannels.Algebra.{u}),
    TopologicalSpace.SeparableSpace A → TopologicalSpace.SeparableSpace B →
      TopologicalSpace.SeparableSpace (T.tensor A B)
  equiv : ∀ (A B : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) (hB : TopologicalSpace.SeparableSpace B),
    exterior.tensor (actual A hA) (actual B hB) ≃⋆ₐ[ℂ]
      actual (T.tensor A B) (separable A B hA hB)
  naturality : ∀ (A B C D : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) (hB : TopologicalSpace.SeparableSpace B)
    (hC : TopologicalSpace.SeparableSpace C) (hD : TopologicalSpace.SeparableSpace D)
    (f : A →⋆ₙₐ[ℂ] B) (g : C →⋆ₙₐ[ℂ] D) (x),
    equiv B D hB hD (exterior.map (A := actual A hA) (B := actual B hB)
      (C := actual C hC) (D := actual D hD) f g x) =
    T.map f g (equiv A C hA hC x)

namespace SpatialKKInput
variable {T : Spatial.{u}} (H : SpatialKKInput J T)

def binding (A E : TensorCoefficientChannels.Algebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) (hE : TopologicalSpace.SeparableSpace E) :=
  mapIso J (H.equiv A E hA hE)

/-- The actual spatial map is the exterior class transported through the
explicit standard tensor equivalences. -/
theorem map_class {A B C D : TensorCoefficientChannels.Algebra.{u}}
    (hA : TopologicalSpace.SeparableSpace A) (hB : TopologicalSpace.SeparableSpace B)
    (hC : TopologicalSpace.SeparableSpace C) (hD : TopologicalSpace.SeparableSpace D)
    (f : A →⋆ₙₐ[ℂ] B) (g : C →⋆ₙₐ[ℂ] D) :
    (H.binding J A C hA hC).hom ≫
      J.map (A := actual (T.tensor A C) (H.separable A C hA hC))
        (B := actual (T.tensor B D) (H.separable B D hB hD)) (T.map f g) =
    H.exterior.product (J.map (A := actual A hA) (B := actual B hB) f)
      (J.map (A := actual C hC) (B := actual D hD) g) ≫
      (H.binding J B D hB hD).hom := by
  change J.map (H.equiv A C hA hC).toNonUnitalStarAlgHom ≫
    J.map (A := actual (T.tensor A C) (H.separable A C hA hC))
      (B := actual (T.tensor B D) (H.separable B D hB hD)) (T.map f g) = _
  rw [← H.exterior.map_class]
  change J.map (H.equiv A C hA hC).toNonUnitalStarAlgHom ≫
    J.map (A := actual (T.tensor A C) (H.separable A C hA hC))
      (B := actual (T.tensor B D) (H.separable B D hB hD)) (T.map f g) =
    J.map (H.exterior.map f g) ≫ J.map (H.equiv B D hB hD).toNonUnitalStarAlgHom
  rw [← J.map_comp, ← J.map_comp]
  congr 1
  ext x
  exact (H.naturality A B C D hA hB hC hD f g x).symm

/-- κ tensor the coefficient identity, on the actual spatial stage. -/
def coordinate {A : TensorCoefficientChannels.Algebra.{u}}
    (hA : TopologicalSpace.SeparableSpace A) (E : TensorCoefficientChannels.Algebra.{u})
    (hE : TopologicalSpace.SeparableSpace E)
    {R : CoefficientModelFromExtension.Algebra.{u}} (κ : J.object (actual A hA) ≅ J.object R) :
    J.object (actual (T.tensor A E) (H.separable A E hA hE)) ≅
      J.object (H.exterior.tensor R (actual E hE)) :=
  (H.binding J A E hA hE).symm ≪≫ H.exterior.tensorIso J κ (actual E hE)

theorem transport_map {A B E : TensorCoefficientChannels.Algebra.{u}}
    (hA : TopologicalSpace.SeparableSpace A) (hB : TopologicalSpace.SeparableSpace B)
    (hE : TopologicalSpace.SeparableSpace E)
    {R : CoefficientModelFromExtension.Algebra.{u}}
    (a : J.object (actual A hA) ≅ J.object R)
    (b : J.object (actual B hB) ≅ J.object R)
    (f : A →⋆ₙₐ[ℂ] B) (g : E →⋆ₙₐ[ℂ] E) :
    (H.coordinate J hA E hE a).inv ≫
      J.map (A := actual (T.tensor A E) (H.separable A E hA hE))
        (B := actual (T.tensor B E) (H.separable B E hB hE)) (T.map f g) ≫
      (H.coordinate J hB E hE b).hom =
    H.exterior.product (a.inv ≫ J.map (A := actual A hA) (B := actual B hB) f ≫ b.hom)
      (J.map (A := actual E hE) (B := actual E hE) g) := by
  simp only [coordinate, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [← Category.assoc (H.binding J A E hA hE).hom, H.map_class J hA hB hE hE,
    Category.assoc, (H.binding J B E hB hE).hom_inv_id_assoc]
  exact H.exterior.transport_product J a b _ _

/-- Exact orthogonal additivity for the constructed coefficient sum. -/
theorem phi_class {A B E : TensorCoefficientChannels.Algebra.{u}} {q : ℕ}
    (hA : TopologicalSpace.SeparableSpace A) (hB : TopologicalSpace.SeparableSpace B)
    (hE : TopologicalSpace.SeparableSpace E) (G : ScalarChannels A B q)
    (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E) (σ : E →⋆ₐ[ℂ] matrixAlgebra q) :
    J.map (A := actual (T.tensor A E) (H.separable A E hA hE))
      (B := actual (T.tensor B E) (H.separable B E hB hE))
      (G.phi T ε η σ).toNonUnitalStarAlgHom =
    ∑ c, J.map (A := actual (T.tensor A E) (H.separable A E hA hE))
      (B := actual (T.tensor B E) (H.separable B E hB hE)) (G.coefficient T ε η σ c) := by
  apply H.exterior.orthogonal_sum
  · intro c d hcd x y
    exact OrthogonalChannels.cross_mul (G.coefficient T ε η σ)
      (G.coefficient_orthogonal T ε η σ) c d hcd x y
  · intro x
    rfl

/-- The actual matrix-noise channel disappears by actual composition;
its zero scalar class is supplied by the finite-cone calculation below. -/
theorem noise_coefficient_zero {A B E : TensorCoefficientChannels.Algebra.{u}} {q : ℕ}
    (hA : TopologicalSpace.SeparableSpace A) (hB : TopologicalSpace.SeparableSpace B)
    (hE : TopologicalSpace.SeparableSpace E)
    (hM : TopologicalSpace.SeparableSpace (amplification A q))
    (hC : TopologicalSpace.SeparableSpace (T.tensor A (matrixAlgebra q)))
    (G : ScalarChannels A B q)
    (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E) (σ : E →⋆ₐ[ℂ] matrixAlgebra q)
    (hzero : J.map (A := actual (amplification A q) hM) (B := actual B hB) G.noise = 0) :
    J.map (A := actual (T.tensor A E) (H.separable A E hA hE))
      (B := actual (T.tensor B E) (H.separable B E hB hE))
      (G.coefficient T ε η σ .noise) = 0 := by
  change J.map (A := actual (T.tensor A E) (H.separable A E hA hE))
    (B := actual (T.tensor B E) (H.separable B E hB hE))
    ((T.left B E).toNonUnitalStarAlgHom.comp
    ((G.noise.comp (T.matrixEquiv A q).toStarAlgHom.toNonUnitalStarAlgHom).comp
      (T.map (StarAlgHom.id ℂ A).toNonUnitalStarAlgHom σ.toNonUnitalStarAlgHom))) = 0
  rw [J.map_comp (A := actual (T.tensor A E) (H.separable A E hA hE))
    (B := actual B hB)
    (C := actual (T.tensor B E) (H.separable B E hB hE))]
  rw [J.map_comp (A := actual (T.tensor A E) (H.separable A E hA hE))
    (B := actual (T.tensor A (matrixAlgebra q)) hC) (C := actual B hB)]
  rw [J.map_comp (A := actual (T.tensor A (matrixAlgebra q)) hC)
    (B := actual (amplification A q) hM) (C := actual B hB), hzero]
  simp

/-- Local assembly lemma. Its scalar premises are discharged by the actual
finite-cone theorems, rather than licensed as final published parameters. -/
theorem bond_of_scalar {A B E : TensorCoefficientChannels.Algebra.{u}} {q : ℕ}
    (hA : TopologicalSpace.SeparableSpace A) (hB : TopologicalSpace.SeparableSpace B)
    (hE : TopologicalSpace.SeparableSpace E) (M : MatrixInput J)
    (G : ScalarChannels A B q)
    (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E) (σ : E →⋆ₐ[ℂ] matrixAlgebra q)
    {R : CoefficientModelFromExtension.Algebra.{u}}
    (a : J.object (actual A hA) ≅ J.object R) (b : J.object (actual B hB) ≅ J.object R)
    (p : J.object R ⟶ J.object R)
    (hp : a.inv ≫ J.map (A := actual A hA) (B := actual B hB) G.plus ≫ b.hom = p)
    (hm : a.inv ≫ J.map (A := actual A hA) (B := actual B hB) G.minus ≫ b.hom = -p)
    (hz : J.map (A := actual (amplification A q) (M.separable A q hA))
      (B := actual B hB) G.noise = 0) :
    (H.coordinate J hA E hE a).inv ≫
      J.map (A := actual (T.tensor A E) (H.separable A E hA hE))
        (B := actual (T.tensor B E) (H.separable B E hB hE))
        (G.phi T ε η σ).toNonUnitalStarAlgHom ≫
      (H.coordinate J hB E hE b).hom =
    H.exterior.product p (𝟙 (J.object (actual E hE)) -
      J.map (A := actual E hE) (B := actual E hE) (η.comp ε).toNonUnitalStarAlgHom) := by
  rw [H.phi_class J hA hB hE, sum_channel]
  simp only [comp_add, add_comp]
  have hz' := H.noise_coefficient_zero J hA hB hE (M.separable A q hA)
    (H.separable A (matrixAlgebra q) hA (M.scalar_separable q)) G ε η σ hz
  rw [hz']
  simp only [Limits.comp_zero, Limits.zero_comp]
  change (H.coordinate J hA E hE a).inv ≫
      J.map (A := actual (T.tensor A E) (H.separable A E hA hE))
        (B := actual (T.tensor B E) (H.separable B E hB hE))
        (T.map G.plus (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom) ≫
      (H.coordinate J hB E hE b).hom +
    ((H.coordinate J hA E hE a).inv ≫
      J.map (A := actual (T.tensor A E) (H.separable A E hA hE))
        (B := actual (T.tensor B E) (H.separable B E hB hE))
        (T.map G.minus (η.comp ε).toNonUnitalStarAlgHom) ≫
      (H.coordinate J hB E hE b).hom) + 0 = _
  rw [H.transport_map J hA hB hE a b, H.transport_map J hA hB hE a b, hp, hm]
  have hi : J.map (A := actual E hE) (B := actual E hE)
      (StarAlgHom.id ℂ E).toNonUnitalStarAlgHom = 𝟙 (J.object (actual E hE)) :=
    J.map_id (actual E hE)
  rw [hi]
  exact H.exterior.signed_sum J p _

end SpatialKKInput

/-- Actual scalar algebra in the target carrier universe. -/
abbrev scalar : CoefficientModelFromExtension.Algebra.{u} := ⟨ULift.{u} ℂ, inferInstance, inferInstance⟩
/-- Actual scalar reference C⊕SC, including its nonunital suspension summand. -/
abbrev reference : CoefficientModelFromExtension.Algebra.{u} :=
  ⟨scalar.{u} × CoefficientModelFromExtension.suspension scalar.{u}, inferInstance, inferInstance⟩

def referenceInclusion : scalar.{u} →⋆ₙₐ[ℂ] reference.{u} where
  toFun z := (z, 0)
  map_zero' := rfl
  map_add' x y := by change (x+y, (0 : CoefficientModelFromExtension.suspension scalar)) = (x, 0)+(y,0); simp
  map_mul' x y := by change (x*y, (0 : CoefficientModelFromExtension.suspension scalar)) = (x, 0)*(y,0); simp
  map_smul' z x := by change (z • x, (0 : CoefficientModelFromExtension.suspension scalar)) = z • (x, 0); simp
  map_star' x := by
    change (star x, (0 : CoefficientModelFromExtension.suspension scalar)) =
      (star x, star (0 : CoefficientModelFromExtension.suspension scalar))
    rw [star_zero]

def referenceProjection : reference.{u} →⋆ₙₐ[ℂ] scalar.{u} where
  toFun z := z.1
  map_zero' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  map_smul' := by intros; rfl
  map_star' := by intros; rfl

def referenceMap : reference.{u} →⋆ₙₐ[ℂ] reference.{u} :=
  referenceInclusion.comp referenceProjection

@[simp] theorem reference_retract : referenceProjection.{u}.comp referenceInclusion =
    NonUnitalStarAlgHom.id ℂ scalar := by ext z; rfl

/-- Universal standard scalar-unit constraint for minimal exterior products.
It quantifies over every actual separable (possibly nonunital) coefficient. -/
structure ScalarTensorInput (X : ExteriorInput J) where
  unit : ∀ E : CoefficientModelFromExtension.Algebra.{u},
    J.object (X.tensor scalar E) ≅ J.object E
  naturality : ∀ {E F : CoefficientModelFromExtension.Algebra.{u}}
    (f : J.object E ⟶ J.object F),
    X.product (𝟙 (J.object scalar)) f ≫ (unit F).hom = (unit E).hom ≫ f

namespace ScalarTensorInput
variable (X : ExteriorInput J) (U : ScalarTensorInput J X)

def first (E : CoefficientModelFromExtension.Algebra.{u}) :
    ConditionalKK.FirstCoordinate (J.object E) (J.object (X.tensor reference E)) where
  inclusion := (U.unit E).inv ≫ X.product (J.map referenceInclusion) (𝟙 (J.object E))
  projection := X.product (J.map referenceProjection) (𝟙 (J.object E)) ≫ (U.unit E).hom
  retract := by
    rw [Category.assoc, ← Category.assoc (X.product _ _) (X.product _ _),
      ← X.product_comp, ← J.map_comp, reference_retract, J.map_id, Category.id_comp,
      X.product_id, Category.id_comp, (U.unit E).inv_hom_id]

theorem first_product (E : CoefficientModelFromExtension.Algebra.{u})
    (e : J.object E ⟶ J.object E) :
    (U.first J X E).projection ≫ e ≫ (U.first J X E).inclusion =
      X.product (J.map (A := reference) (B := reference) referenceMap) e := by
  change (X.product _ _ ≫ (U.unit E).hom) ≫ e ≫
    ((U.unit E).inv ≫ X.product _ _) = _
  rw [Category.assoc, ← Category.assoc (U.unit E).hom e, ← U.naturality,
    Category.assoc, (U.unit E).hom_inv_id_assoc]
  rw [← X.product_comp, ← X.product_comp, Category.id_comp, Category.comp_id,
    Category.id_comp, ← J.map_comp]
  rfl

def splitting (S : CoefficientModelFromExtension.SplitUnitizationInput J)
    (F : CoefficientModelFromExtension.Algebra.{u}) (hF : CoefficientModelFromExtension.Nuclear F) :
    ConditionalKK.Splitting (J.object F)
      (J.object (X.tensor reference (CoefficientModelFromExtension.unitization F))) :=
  (U.first J X (CoefficientModelFromExtension.unitization F)).splitting
    (J.map (CoefficientModelFromExtension.unitizationInclusion F))
    (CoefficientModelFromExtension.unitizationRetraction J S F hF)
    (CoefficientModelFromExtension.inclusion_retraction J S F hF)

theorem splitting_f (S : CoefficientModelFromExtension.SplitUnitizationInput J)
    (F : CoefficientModelFromExtension.Algebra.{u}) (hF : CoefficientModelFromExtension.Nuclear F) :
    (U.splitting J X S F hF).f =
      X.product (J.map (A := reference) (B := reference) referenceMap)
        (𝟙 (J.object (CoefficientModelFromExtension.unitization F)) -
          J.map (CoefficientModelFromExtension.scalarRetraction F)) := by
  change ((U.first J X _).projection ≫
    CoefficientModelFromExtension.unitizationRetraction J S F hF) ≫
    (J.map (CoefficientModelFromExtension.unitizationInclusion F) ≫
      (U.first J X _).inclusion) = _
  rw [Category.assoc, ← Category.assoc (CoefficientModelFromExtension.unitizationRetraction J S F hF),
    CoefficientModelFromExtension.retraction_inclusion]
  exact U.first_product J X _ _

end ScalarTensorInput


namespace UniverseCone
open Matrix PositiveLifting MultiplicityEmbeddings FiniteDiagram

/-- Carrier-universe generalization of the frozen Type-0 finite-presentation
interface. The finite block carriers use the actual existing UniverseLift. -/
structure Presentation {n : Type} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℤ) (k l : n → ℕ) where
  algebra : TensorCoefficientChannels.Algebra.{u}
  separable : TopologicalSpace.SeparableSpace algebra
  positive : Positive B
  k_pos : ∀ i, 0 < k i
  l_pos : ∀ i, 0 < l i
  left : UniverseLift.algebra.{u} (Blocks (k+l)) →⋆ₐ[ℂ] algebra
  right : UniverseLift.algebra.{u} (Blocks (k + natMatrix (1+B) *ᵥ l)) →⋆ₐ[ℂ] algebra
  full : CStarAmalgam.IsFullAmalgam (UniverseLift.map (firstInclusion k l))
    (UniverseLift.map (secondInclusion (natMatrix (1+B)) k l)) left right

abbrev Presentation.actual {n : Type} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℤ} {k l : n → ℕ} (P : Presentation.{u} B k l) :=
  ActualCoefficientKK.actual P.algebra P.separable

variable (G : KTheory.{u,v,w,t} J)

/-- Universal finite-cone/bootstrap theorem on actual lifted finite triples.
This is the same comparison, (-y,y) boundary and factor signs as the frozen
Type-0 interface. It is quantified over every compatible actual diagram;
no recursive/channel KK class is a field. F.action is the ordinary matrix
rank K0 action, and must agree with G on the actual lifted finite maps.
P4/P6: FG 1510.02418v3 Theorem 4.1 and ordinary cone naturality; RS 1.17/7.1.
Universe lifting preserves multiplication, star, norm and finite rank. -/
structure Input (F : FiniteK0Input) (U : FreeUCTInput J G) where
  coordinates : ∀ {n : Type} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℤ} {k l : n → ℕ} (P : Presentation.{u} B k l),
      GraphCoordinates J G P.actual B
  bootstrap : ∀ {n : Type} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℤ} {k l : n → ℕ} (P : Presentation.{u} B k l), U.bootstrap P.actual
  naturality : ∀ {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {B : Matrix n n ℤ} {B' : Matrix m m ℤ} {k l : n → ℕ} {k' l' : m → ℕ}
    (P : Presentation.{u} B k l) (Q : Presentation.{u} B' k' l')
    (γ : P.actual →⋆ₙₐ[ℂ] Q.actual)
    (d : Blocks (Sum.elim k l) →⋆ₙₐ[ℂ] Blocks (Sum.elim k' l'))
    (f : Blocks (k+l) →⋆ₙₐ[ℂ] Blocks (k'+l'))
    (g : Blocks (k+natMatrix (1+B)*ᵥl) →⋆ₙₐ[ℂ] Blocks (k'+natMatrix (1+B')*ᵥl')),
    (∀ a, f (firstInclusion k l a) = firstInclusion k' l' (d a)) →
    (∀ a, g (secondInclusion (natMatrix (1+B)) k l a) =
      secondInclusion (natMatrix (1+B')) k' l' (d a)) →
    (∀ a, γ (P.left (ULift.up a)) = Q.left (ULift.up (f a))) →
    (∀ a, γ (P.right (ULift.up a)) = Q.right (ULift.up (g a))) →
    (∀ x y, (coordinates Q).even
      (G.action false (J.map (A := P.actual) (B := Q.actual) γ)
        ((coordinates P).even.symm (pairClass B x y))) =
      pairClass B' (F.action f x) (F.action g y)) ∧
    (∀ x, Sum.elim (-((coordinates Q).odd
      (G.action true (J.map (A := P.actual) (B := Q.actual) γ) x)).val)
      ((coordinates Q).odd (G.action true (J.map (A := P.actual) (B := Q.actual) γ) x)).val =
      F.action d (Sum.elim (-((coordinates P).odd x).val) ((coordinates P).odd x).val))

namespace Input
variable {F : FiniteK0Input} {U : FreeUCTInput J G} (V : Input J G F U)

theorem recursive_naturality {P : Stage} {q : ℕ} (D : Lift P q) (c : RecursiveGraphSequence.Channel)
    (A : Presentation.{u} P.B (P.scaledK q c) (P.scaledL q c))
    (B : Presentation.{u} D.next.B D.next.k D.next.l)
    (γ : A.actual →⋆ₙₐ[ℂ] B.actual)
    (hl : ∀ a, γ (A.left (ULift.up a)) = B.left (ULift.up (D.aggregate.left c a)))
    (hr : ∀ a, γ (A.right (ULift.up a)) = B.right (ULift.up (D.aggregate.right c a))) :
    FiniteConeNaturality J G (V.coordinates A) (V.coordinates B) γ
      (D.S c) (D.H c) (D.Z c) := by
  obtain ⟨h₀,h₁⟩ := V.naturality A B γ (D.aggregate.common c) (D.aggregate.left c)
    (D.aggregate.right c) (D.aggregate.first_square c) (D.aggregate.second_square c) hl hr
  constructor
  · intro x y
    rw [h₀, Recursive.aggregate_left_K0 F D c, Recursive.aggregate_right_K0 F D c]
    rfl
  · intro x
    rw [h₁, Recursive.aggregate_common_K0 F D c]
    rfl

theorem recursive_class {P : Stage} {q : ℕ} (D : Lift P q) (c : RecursiveGraphSequence.Channel)
    (A : Presentation.{u} P.B (P.scaledK q c) (P.scaledL q c))
    (B : Presentation.{u} D.next.B D.next.k D.next.l)
    {R : CoefficientModelFromExtension.Algebra.{u}} (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ)
    (γ : A.actual →⋆ₙₐ[ℂ] B.actual)
    (hl : ∀ a, γ (A.left (ULift.up a)) = B.left (ULift.up (D.aggregate.left c a)))
    (hr : ∀ a, γ (A.right (ULift.up a)) = B.right (ULift.up (D.aggregate.right c a))) :
    (U.kappa J G (V.bootstrap A) hR
      ((V.coordinates A).even.trans P.cokernel.toAddEquiv)
      ((V.coordinates A).odd.trans P.kernel.toAddEquiv) r₀ r₁).inv ≫
      J.map (A := A.actual) (B := B.actual) γ ≫
      (U.kappa J G (V.bootstrap B) hR
        ((V.coordinates B).even.trans D.next.cokernel.toAddEquiv)
        ((V.coordinates B).odd.trans D.next.kernel.toAddEquiv) r₀ r₁).hom =
      sign c • U.referenceProjection J G hR r₀ r₁ :=
  recursive_scalar_class J G U D (V.coordinates A) (V.coordinates B)
    (V.bootstrap A) (V.bootstrap B) hR r₀ r₁ c γ
    (V.recursive_naturality J G D c A B γ hl hr)

end Input

def graphPresentation (H : GraphCoefficientLimit.GraphInput.{u}) (P : Stage)
    (k l : Vertex → ℕ) (hk : ∀ i, 0 < k i) (hl : ∀ i, 0 < l i) :
    Presentation.{u} P.B k l where
  algebra := graphProduct P.A k l
  separable := (H.corners P.A k l (stage_adjacency_positive P)
    (GraphCoefficientLimit.stage_two_loops P) hk hl).1
  positive := P.positive
  k_pos := hk
  l_pos := hl
  left := graphFirst P.A k l
  right := graphSecond P.A k l hk (stage_noSinks P)
  full := standardGraph_isFullAmalgam P.A k l hk hl (stage_noSinks P)


namespace Input
variable (G : KTheory.{u,v,w,t} J) {F : FiniteK0Input} {U : FreeUCTInput J G}
    (V : Input J G F U) (H : GraphCoefficientLimit.GraphInput.{u})

abbrev stagePresentation (P : Stage) := graphPresentation H P P.k P.l P.k_pos P.l_pos
abbrev stageActual (P : Stage) := (stagePresentation H P).actual

def kappa (P : Stage) {R : CoefficientModelFromExtension.Algebra.{u}} (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ) :
    J.object (stageActual H P) ≅ J.object R :=
  U.kappa J G (V.bootstrap (stagePresentation H P)) hR
    ((V.coordinates (stagePresentation H P)).even.trans P.cokernel.toAddEquiv)
    ((V.coordinates (stagePresentation H P)).odd.trans P.kernel.toAddEquiv) r₀ r₁

private theorem action_cast_left {P Q : Matrix Vertex Vertex ℕ}
    {k₀ l₀ k l k' l' : Vertex → ℕ} (D : ScalarBond P Q k₀ l₀ k' l')
    (hk : k₀ = k) (hl : l₀ = l) :
    F.action (D.castSource hk hl).left = F.action D.left := by subst k; subst l; rfl
private theorem action_cast_right {P Q : Matrix Vertex Vertex ℕ}
    {k₀ l₀ k l k' l' : Vertex → ℕ} (D : ScalarBond P Q k₀ l₀ k' l')
    (hk : k₀ = k) (hl : l₀ = l) :
    F.action (D.castSource hk hl).right = F.action D.right := by subst k; subst l; rfl
private theorem action_cast_common {P Q : Matrix Vertex Vertex ℕ}
    {k₀ l₀ k l k' l' : Vertex → ℕ} (D : ScalarBond P Q k₀ l₀ k' l')
    (hk : k₀ = k) (hl : l₀ = l) :
    F.action (D.castSource hk hl).common = F.action D.common := by subst k; subst l; rfl

private theorem scalarChannel_left_K0 {P : Stage} {q : ℕ} (D : Lift P q)
    (c : RecursiveGraphSequence.Channel) (hc : scale q c = 1) :
    F.action (D.scalarChannel c hc).left = (D.S c).mulVecLin := by
  rw [Lift.scalarChannel, action_cast_left]
  exact Recursive.aggregate_left_K0 F D c
private theorem scalarChannel_right_K0 {P : Stage} {q : ℕ} (D : Lift P q)
    (c : RecursiveGraphSequence.Channel) (hc : scale q c = 1) :
    F.action (D.scalarChannel c hc).right = (D.S c + D.next.B * D.Z c).mulVecLin := by
  rw [Lift.scalarChannel, action_cast_right]
  exact Recursive.aggregate_right_K0 F D c
private theorem scalarChannel_common_K0 {P : Stage} {q : ℕ} (D : Lift P q)
    (c : RecursiveGraphSequence.Channel) (hc : scale q c = 1) :
    F.action (D.scalarChannel c hc).common =
      (MatrixDiagrams.diagram P.B (D.S c) (D.H c) (D.Z c)).mulVecLin := by
  rw [Lift.scalarChannel, action_cast_common]
  exact Recursive.aggregate_common_K0 F D c

theorem scalar_naturality {P : Stage} {q : ℕ} (D : Lift P q)
    (c : RecursiveGraphSequence.Channel) (hc : scale q c = 1) :
    FiniteConeNaturality J G (V.coordinates (stagePresentation H P))
      (V.coordinates (stagePresentation H D.next))
      (scalarProductMap P.k_pos P.l_pos (stage_noSinks P) D.next.k_pos D.next.l_pos
        (stage_noSinks D.next) (D.scalarChannel c hc)) (D.S c) (D.H c) (D.Z c) := by
  let A := stagePresentation H P
  let B := stagePresentation H D.next
  let γ : A.actual →⋆ₙₐ[ℂ] B.actual := scalarProductMap P.k_pos P.l_pos (stage_noSinks P) D.next.k_pos D.next.l_pos
    (stage_noSinks D.next) (D.scalarChannel c hc)
  obtain ⟨h₀,h₁⟩ := V.naturality A B γ (D.scalarChannel c hc).common
    (D.scalarChannel c hc).left (D.scalarChannel c hc).right
    (D.scalarChannel c hc).first_square (D.scalarChannel c hc).second_square
    (fun a => scalarProductMap_left P.k_pos P.l_pos (stage_noSinks P) D.next.k_pos
      D.next.l_pos (stage_noSinks D.next) (D.scalarChannel c hc) (ULift.up a))
    (fun a => scalarProductMap_right P.k_pos P.l_pos (stage_noSinks P) D.next.k_pos
      D.next.l_pos (stage_noSinks D.next) (D.scalarChannel c hc) (ULift.up a))
  constructor
  · intro x y
    rw [h₀, scalarChannel_left_K0 D c hc, scalarChannel_right_K0 D c hc]
    rfl
  · intro x
    rw [h₁, scalarChannel_common_K0 D c hc]
    rfl

theorem scalar_class {P : Stage} {q : ℕ} (D : Lift P q)
    (c : RecursiveGraphSequence.Channel) (hc : scale q c = 1)
    {R : CoefficientModelFromExtension.Algebra.{u}} (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ) :
    (V.kappa J G H P hR r₀ r₁).inv ≫
      J.map (A := stageActual H P) (B := stageActual H D.next)
        (scalarProductMap P.k_pos P.l_pos (stage_noSinks P) D.next.k_pos D.next.l_pos
          (stage_noSinks D.next) (D.scalarChannel c hc)) ≫
      (V.kappa J G H D.next hR r₀ r₁).hom =
      sign c • U.referenceProjection J G hR r₀ r₁ :=
  recursive_scalar_class J G U D _ _ (V.bootstrap _) (V.bootstrap _) hR r₀ r₁ c _
    (V.scalar_naturality J G H D c hc)

end Input

/-- Exact entrywise universe-lift matrix equivalence. -/
def matrixDownEquiv (A : Type) [CStarAlgebra A] (q : ℕ) :
    amplification (UniverseLift.algebra.{u} A) q ≃⋆ₐ[ℂ]
      CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A :=
  StarAlgEquiv.ofNonUnitalStarAlgHom
    (CStarMatrix.mapₙₐ (UniverseLift.equiv A).toNonUnitalStarAlgHom)
    (CStarMatrix.mapₙₐ (UniverseLift.equiv A).symm.toNonUnitalStarAlgHom)
    (by apply NonUnitalStarAlgHom.ext; intro a; apply CStarMatrix.ext; intro i j; rfl)
    (by apply NonUnitalStarAlgHom.ext; intro a; apply CStarMatrix.ext; intro i j; rfl)

def matrixBlocksEquiv {A B : Type} [CStarAlgebra A] [CStarAlgebra B] (q : ℕ)
    (e : CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A ≃⋆ₐ[ℂ] B) :
    amplification (UniverseLift.algebra.{u} A) q ≃⋆ₐ[ℂ] UniverseLift.algebra.{u} B :=
  ((matrixDownEquiv A q).trans e).trans (UniverseLift.equiv B).symm

@[simp] theorem matrixBlocksEquiv_apply {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (q : ℕ) (e : CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A ≃⋆ₐ[ℂ] B)
    (a : amplification (UniverseLift.algebra.{u} A) q) :
    matrixBlocksEquiv q e a = ULift.up (e (matrixDown q a)) := rfl

/-- The actual amplified graph, expressed using the literal scaled finite
blocks and the SAME tripleAmplification used by the noise map. -/
def amplifiedPresentation (T : Spatial.{u}) (H : GraphCoefficientLimit.GraphInput.{u})
    (S : GraphCoefficientLimit.SupportInput T) (M : MatrixInput J) (P : Stage) (q : ℕ) (hq : 0 < q) :
    Presentation.{u} P.B (fun i => q*P.k i) (fun i => q*P.l i) := by
  let N := tripleAmplification P (Equiv.ulift : ULift.{u} (Fin q) ≃ Fin q)
  let eD := matrixBlocksEquiv q N.common
  let eA := matrixBlocksEquiv q N.left
  let eB := matrixBlocksEquiv q N.right
  let A := graphStage.{u} P
  have hs : TopologicalSpace.SeparableSpace (amplification A q) :=
    M.separable A q (GraphCoefficientLimit.stage_kirchberg H P).1
  let hf := amplification_isFullAmalgam T q (S.matrix_maximal q hq)
    (standardGraph_isFullAmalgam P.A P.k P.l P.k_pos P.l_pos (stage_noSinks P))
  have hf' := amalgam_transport hf eD eA eB (StarAlgEquiv.refl ℂ (amplification A q))
  have h₀ : eA.toStarAlgHom.comp ((T.amplifiedMap q
      (UniverseLift.map (firstInclusion P.k P.l))).comp eD.symm.toStarAlgHom) =
      UniverseLift.map (firstInclusion (fun i => q*P.k i) (fun i => q*P.l i)) := by
    ext a
    change ULift.up (N.left (matrixDown q (T.amplifiedMap q
      (UniverseLift.map (firstInclusion P.k P.l)) (eD.symm a)))) = _
    rw [matrixDown_natural, N.first_square]
    have he := congrArg ULift.down (eD.apply_symm_apply a)
    change N.common (matrixDown q (eD.symm a)) = a.down at he
    rw [he]
    rfl
  have h₁ : eB.toStarAlgHom.comp ((T.amplifiedMap q
      (UniverseLift.map (secondInclusion P.A P.k P.l))).comp eD.symm.toStarAlgHom) =
      UniverseLift.map (secondInclusion P.A (fun i => q*P.k i) (fun i => q*P.l i)) := by
    ext a
    change ULift.up (N.right (matrixDown q (T.amplifiedMap q
      (UniverseLift.map (secondInclusion P.A P.k P.l)) (eD.symm a)))) = _
    rw [matrixDown_natural, N.second_square]
    have he := congrArg ULift.down (eD.apply_symm_apply a)
    change N.common (matrixDown q (eD.symm a)) = a.down at he
    rw [he]
    rfl
  rw [h₀,h₁] at hf'
  exact ⟨amplification A q, hs, P.positive,
    (fun i => Nat.mul_pos hq (P.k_pos i)), (fun i => Nat.mul_pos hq (P.l_pos i)),
    (T.amplifiedMap q (graphFirst P.A P.k P.l)).comp eA.symm.toStarAlgHom,
    (T.amplifiedMap q (graphSecond P.A P.k P.l P.k_pos (stage_noSinks P))).comp eB.symm.toStarAlgHom,
    by
      have hleft : (StarAlgEquiv.refl ℂ (amplification A q)).toStarAlgHom.comp
        ((T.amplifiedMap q (graphFirst P.A P.k P.l)).comp eA.symm.toStarAlgHom) =
        (T.amplifiedMap q (graphFirst P.A P.k P.l)).comp eA.symm.toStarAlgHom := by ext a; rfl
      have hright : (StarAlgEquiv.refl ℂ (amplification A q)).toStarAlgHom.comp
        ((T.amplifiedMap q (graphSecond P.A P.k P.l P.k_pos (stage_noSinks P))).comp eB.symm.toStarAlgHom) =
        (T.amplifiedMap q (graphSecond P.A P.k P.l P.k_pos (stage_noSinks P))).comp eB.symm.toStarAlgHom := by ext a; rfl
      rw [hleft, hright] at hf'
      exact hf'⟩

namespace Input
variable (G : KTheory.{u,v,w,t} J) {F : FiniteK0Input} {U : FreeUCTInput J G}
    (V : Input J G F U) (H : GraphCoefficientLimit.GraphInput.{u})
    (T : Spatial.{u}) (S : GraphCoefficientLimit.SupportInput T) (M : MatrixInput J)

include V in
theorem noise_zero {P : Stage} {q : ℕ} (D : Lift P q)
    {R : CoefficientModelFromExtension.Algebra.{u}} (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ) :
    J.map (A := (amplifiedPresentation J T H S M P q D.q_pos).actual)
      (B := stageActual H D.next)
      (noiseProductMap T D (stage_noSinks P) (stage_noSinks D.next)
        (S.matrix_maximal q D.q_pos)) = 0 := by
  let A := amplifiedPresentation J T H S M P q D.q_pos
  let B := stagePresentation H D.next
  let γ := noiseProductMap T D (stage_noSinks P) (stage_noSinks D.next)
    (S.matrix_maximal q D.q_pos)
  have hl : ∀ a, γ (A.left (ULift.up a)) = B.left (ULift.up (D.aggregate.left 2 a)) := by
    intro a
    change γ (T.amplifiedMap q (graphFirst P.A P.k P.l)
      ((matrixBlocksEquiv q (tripleAmplification P Equiv.ulift).left).symm (ULift.up a))) = _
    rw [noiseProductMap_left]
    change graphFirst D.next.A D.next.k D.next.l
      (ULift.up (D.aggregate.left 2 ((tripleAmplification P Equiv.ulift).left
        (matrixDown q ((matrixBlocksEquiv q (tripleAmplification P Equiv.ulift).left).symm (ULift.up a)))))) = _
    have he0 := (matrixBlocksEquiv q
      (tripleAmplification P Equiv.ulift).left).apply_symm_apply (ULift.up a)
    rw [matrixBlocksEquiv_apply] at he0
    have he := ULift.up_injective he0
    exact congrArg (fun z => graphFirst D.next.A D.next.k D.next.l
      (ULift.up (D.aggregate.left 2 z))) he
  have hr : ∀ a, γ (A.right (ULift.up a)) = B.right (ULift.up (D.aggregate.right 2 a)) := by
    intro a
    change γ (T.amplifiedMap q (graphSecond P.A P.k P.l P.k_pos (stage_noSinks P))
      ((matrixBlocksEquiv q (tripleAmplification P Equiv.ulift).right).symm (ULift.up a))) = _
    rw [noiseProductMap_right]
    change graphSecond D.next.A D.next.k D.next.l D.next.k_pos (stage_noSinks D.next)
      (ULift.up (D.aggregate.right 2 ((tripleAmplification P Equiv.ulift).right
        (matrixDown q ((matrixBlocksEquiv q (tripleAmplification P Equiv.ulift).right).symm (ULift.up a)))))) = _
    have he0 := (matrixBlocksEquiv q
      (tripleAmplification P Equiv.ulift).right).apply_symm_apply (ULift.up a)
    rw [matrixBlocksEquiv_apply] at he0
    have he := ULift.up_injective he0
    exact congrArg (fun z => graphSecond D.next.A D.next.k D.next.l D.next.k_pos
      (stage_noSinks D.next) (ULift.up (D.aggregate.right 2 z))) he
  have h := V.recursive_class J G D 2 A B hR r₀ r₁ γ hl hr
  rw [show sign (2 : RecursiveGraphSequence.Channel) = 0 from rfl, zero_smul] at h
  have hc := congrArg (fun f =>
    (U.kappa J G (V.bootstrap A) hR
      ((V.coordinates A).even.trans P.cokernel.toAddEquiv)
      ((V.coordinates A).odd.trans P.kernel.toAddEquiv) r₀ r₁).hom ≫ f ≫
    (U.kappa J G (V.bootstrap B) hR
      ((V.coordinates B).even.trans D.next.cokernel.toAddEquiv)
      ((V.coordinates B).odd.trans D.next.kernel.toAddEquiv) r₀ r₁).inv) h
  have hraw : J.map (A := A.actual) (B := B.actual) γ = 0 := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id, Limits.comp_zero, Limits.zero_comp] using hc
  -- Restrict to the actual rank-one corner, then use standard matrix Morita.
  let r : ULift.{u} (Fin q) := ULift.up ⟨0, D.q_pos⟩
  have hcorner : J.map (A := stageActual H P) (B := stageActual H D.next)
      (γ.comp (matrixCorner (graphStage P) q r)) = 0 := by
    rw [J.map_comp (B := A.actual), hraw]
    simp
  exact zero_of_corner J M (graphStage P) (graphStage D.next)
    (GraphCoefficientLimit.stage_kirchberg H P).1
    (GraphCoefficientLimit.stage_kirchberg H D.next).1 q r γ hcorner


end Input

end UniverseCone

/-- P3/P4/P6: standard K-theory/UCT of the actual lifted C⊕SC reference.
Scalar/Bott generators and actual first-coordinate map must be matched
externally. No graph-channel class or coefficient UCT occurs here. -/
structure ReferenceInput (G : KTheory.{u,v,w,t} J) (U : FreeUCTInput J G) where
  bootstrap : U.bootstrap reference
  even : G.group false reference ≃+ ℤ
  odd : G.group true reference ≃+ ℤ
  map_even : G.action false (J.map (A := reference) (B := reference) referenceMap) =
    AddMonoidHom.id (G.group false reference)
  map_odd : G.action true (J.map (A := reference) (B := reference) referenceMap) = 0

namespace ReferenceInput
variable (G : KTheory.{u,v,w,t} J) {U : FreeUCTInput J G} (R : ReferenceInput J G U)
theorem projection_class : U.referenceProjection J G R.bootstrap R.even R.odd =
    J.map (A := reference) (B := reference) referenceMap := by
  symm
  apply U.map_eq_diagonal J G R.bootstrap R.even R.odd R.even 1 referenceMap
  · intro x; rw [R.map_even]; simp
  · intro x; rw [R.map_odd]; rfl
end ReferenceInput

namespace ActualBond
open UniverseCone
variable (G : KTheory.{u,v,w,t} J) (F₀ : FiniteK0Input) (U : FreeUCTInput J G)
  (V : UniverseCone.Input J G F₀ U) (R : ReferenceInput J G U)
  (T : Spatial.{u}) (H : GraphCoefficientLimit.GraphInput.{u})
  (S : GraphCoefficientLimit.SupportInput T) (M : MatrixInput J) (X : SpatialKKInput J T)

def scalarChannels {P : Stage} {q : ℕ} (D : Lift P q) :
    ScalarChannels (graphStage.{u} P) (graphStage.{u} D.next) q := by
  let : Nontrivial (graphProduct.{u} D.next.A D.next.k D.next.l) :=
    (GraphCoefficientLimit.stage_kirchberg H D.next).2.2.1.1
  exact graphScalarChannels T D (stage_noSinks P) (stage_noSinks D.next)
    (S.matrix_maximal q D.q_pos) (GraphCoefficientLimit.stage_kirchberg H P).2.2.1

abbrev coordinate (P : Stage) (E : TensorCoefficientChannels.Algebra.{u})
    (hE : TopologicalSpace.SeparableSpace E) :=
  X.coordinate J (GraphCoefficientLimit.stage_kirchberg H P).1 E hE
    (V.kappa J G H P R.bootstrap R.even R.odd)

include M

/-- The new actual coefficient bonding-map class. Every scalar channel class
is derived from the universal finite-cone input and the literal restrictions.
The coefficient object has no UCT or Kunneth premise. -/
theorem bond_class {P : Stage} {q : ℕ} (D : Lift P q)
    (E : TensorCoefficientChannels.Algebra.{u}) (hE : TopologicalSpace.SeparableSpace E)
    (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E) (σ : E →⋆ₐ[ℂ] matrixAlgebra q) :
    (coordinate J G F₀ U V R T H X P E hE).inv ≫
      J.map (A := actual (T.tensor (graphStage P) E)
        (X.separable (graphStage P) E (GraphCoefficientLimit.stage_kirchberg H P).1 hE))
      (B := actual (T.tensor (graphStage D.next) E)
        (X.separable (graphStage D.next) E (GraphCoefficientLimit.stage_kirchberg H D.next).1 hE))
      ((scalarChannels T H S D).phi T ε η σ).toNonUnitalStarAlgHom ≫
    (coordinate J G F₀ U V R T H X D.next E hE).hom =
    X.exterior.product (J.map (A := reference) (B := reference) referenceMap)
      (𝟙 (J.object (actual E hE)) -
        J.map (A := actual E hE) (B := actual E hE) (η.comp ε).toNonUnitalStarAlgHom) := by
  apply X.bond_of_scalar J (GraphCoefficientLimit.stage_kirchberg H P).1
    (GraphCoefficientLimit.stage_kirchberg H D.next).1 hE M (scalarChannels T H S D)
    ε η σ (V.kappa J G H P R.bootstrap R.even R.odd)
    (V.kappa J G H D.next R.bootstrap R.even R.odd)
  · have h := V.scalar_class J G H D 0 rfl R.bootstrap R.even R.odd
    rw [R.projection_class J G] at h
    rw [show sign (0 : RecursiveGraphSequence.Channel) = 1 from rfl, one_smul] at h
    simpa only [scalarChannels, graphScalarChannels, positiveProductMap, Lift.positiveChannel] using h
  · have h := V.scalar_class J G H D 1 rfl R.bootstrap R.even R.odd
    rw [R.projection_class J G] at h
    rw [show sign (1 : RecursiveGraphSequence.Channel) = -1 from rfl, neg_one_zsmul] at h
    simpa only [scalarChannels, graphScalarChannels, negativeProductMap, Lift.negativeChannel] using h
  · exact V.noise_zero J G H T S M D R.bootstrap R.even R.odd


abbrev coefficientSeparable (F : CoefficientModelFromExtension.Algebra.{u}) :
    TopologicalSpace.SeparableSpace (CoefficientSchedule.E F) :=
  (inferInstance : TopologicalSpace.SeparableSpace (Unitization ℂ F))

/-- The actual unitized-coefficient bond is the actual split idempotent. -/
theorem unitization_bond {P : Stage} {q : ℕ} (D : Lift P q)
    (F : CoefficientModelFromExtension.Algebra.{u}) (hF : CoefficientModelFromExtension.Nuclear F)
    (split : CoefficientModelFromExtension.SplitUnitizationInput J)
    (unit : ScalarTensorInput J X.exterior)
    (σ : CoefficientSchedule.E F →⋆ₐ[ℂ] matrixAlgebra q) :
    (coordinate J G F₀ U V R T H X P (CoefficientSchedule.E F) (coefficientSeparable F)).inv ≫
      J.map (A := actual (T.tensor (graphStage P) (CoefficientSchedule.E F))
        (X.separable (graphStage P) (CoefficientSchedule.E F)
          (GraphCoefficientLimit.stage_kirchberg H P).1 (coefficientSeparable F)))
      (B := actual (T.tensor (graphStage D.next) (CoefficientSchedule.E F))
        (X.separable (graphStage D.next) (CoefficientSchedule.E F)
          (GraphCoefficientLimit.stage_kirchberg H D.next).1 (coefficientSeparable F)))
      ((scalarChannels T H S D).phi T (CoefficientSchedule.quotient F)
        (CoefficientSchedule.sectionMap F) σ).toNonUnitalStarAlgHom ≫
    (coordinate J G F₀ U V R T H X D.next (CoefficientSchedule.E F) (coefficientSeparable F)).hom =
      (unit.splitting J X.exterior split F hF).f := by
  rw [bond_class J G F₀ U V R T H S M X D,
    unit.splitting_f J X.exterior split F hF]
  rfl

omit M

/-- Equality with the existing literal recursive scalar channel definition. -/
theorem systemScalarChannels_eq {sizes : ℕ → ℕ} {k l : Vertex → ℕ}
    (Q : System sizes k l) (h : ℕ) :
    systemGraphChannels T Q
      (fun h => S.matrix_maximal (sizes h) ((Q.step h).q_pos))
      (fun h => (GraphCoefficientLimit.stage_kirchberg H (Q.stage h)).2.2.1) h =
      Q.successor h ▸ scalarChannels T H S (Q.step h) := by
  unfold systemGraphChannels scalarChannels
  rfl

include M

private theorem transport_unitization_bond {P Q : Stage} {q : ℕ} (D : Lift P q)
    (e : D.next = Q)
    (F : CoefficientModelFromExtension.Algebra.{u}) (hF : CoefficientModelFromExtension.Nuclear F)
    (split : CoefficientModelFromExtension.SplitUnitizationInput J)
    (unit : ScalarTensorInput J X.exterior)
    (σ : CoefficientSchedule.E F →⋆ₐ[ℂ] matrixAlgebra q) :
    (coordinate J G F₀ U V R T H X P (CoefficientSchedule.E F) (coefficientSeparable F)).inv ≫
      J.map (A := actual (T.tensor (graphStage P) (CoefficientSchedule.E F))
        (X.separable (graphStage P) (CoefficientSchedule.E F)
          (GraphCoefficientLimit.stage_kirchberg H P).1 (coefficientSeparable F)))
      (B := actual (T.tensor (graphStage Q) (CoefficientSchedule.E F))
        (X.separable (graphStage Q) (CoefficientSchedule.E F)
          (GraphCoefficientLimit.stage_kirchberg H Q).1 (coefficientSeparable F)))
      (((e ▸ scalarChannels T H S D) : ScalarChannels (graphStage P) (graphStage Q) q).phi T
        (CoefficientSchedule.quotient F) (CoefficientSchedule.sectionMap F) σ).toNonUnitalStarAlgHom ≫
    (coordinate J G F₀ U V R T H X Q (CoefficientSchedule.E F) (coefficientSeparable F)).hom =
      (unit.splitting J X.exterior split F hF).f := by
  cases e
  exact unitization_bond J G F₀ U V R T H S M X D F hF split unit σ

/-- Exact recursive-system bond with the same actual source/target coordinates.
The successor transport is discharged internally; no bond-class premise occurs. -/
theorem system_bond {sizes : ℕ → ℕ} {k l : Vertex → ℕ}
    (Q : System sizes k l) (h : ℕ)
    (F : CoefficientModelFromExtension.Algebra.{u}) (hF : CoefficientModelFromExtension.Nuclear F)
    (split : CoefficientModelFromExtension.SplitUnitizationInput J)
    (unit : ScalarTensorInput J X.exterior)
    (σ : CoefficientSchedule.E F →⋆ₐ[ℂ] matrixAlgebra (sizes h)) :
    (coordinate J G F₀ U V R T H X (Q.stage h) (CoefficientSchedule.E F) (coefficientSeparable F)).inv ≫
      J.map (A := actual (T.tensor (graphStage (Q.stage h)) (CoefficientSchedule.E F))
        (X.separable (graphStage (Q.stage h)) (CoefficientSchedule.E F)
          (GraphCoefficientLimit.stage_kirchberg H (Q.stage h)).1 (coefficientSeparable F)))
      (B := actual (T.tensor (graphStage (Q.stage (h+1))) (CoefficientSchedule.E F))
        (X.separable (graphStage (Q.stage (h+1))) (CoefficientSchedule.E F)
          (GraphCoefficientLimit.stage_kirchberg H (Q.stage (h+1))).1 (coefficientSeparable F)))
      ((systemGraphChannels T Q
        (fun h => S.matrix_maximal (sizes h) ((Q.step h).q_pos))
        (fun h => (GraphCoefficientLimit.stage_kirchberg H (Q.stage h)).2.2.1) h).phi T
        (CoefficientSchedule.quotient F) (CoefficientSchedule.sectionMap F) σ).toNonUnitalStarAlgHom ≫
    (coordinate J G F₀ U V R T H X (Q.stage (h+1)) (CoefficientSchedule.E F) (coefficientSeparable F)).hom =
      (unit.splitting J X.exterior split F hF).f := by
  rw [systemScalarChannels_eq T H S Q h]
  exact transport_unitization_bond J G F₀ U V R T H S M X (Q.step h) (Q.successor h)
    F hF split unit σ

end ActualBond
end Suzuki.ActualCoefficientKK

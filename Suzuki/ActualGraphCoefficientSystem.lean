import Suzuki.TensorCoefficientChannels
import Suzuki.CommonCorner
import Suzuki.RecursiveGraphSequence
import Suzuki.Target
import Suzuki.PositiveMultiplicityFullness

/-!
# Actual scalar product maps for the coefficient construction

Nonunital extensions are derived from the proved full-amalgam universal
property by passing through the common support corner.
-/
noncomputable section
open scoped CStarAlgebra ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 2000000

namespace Suzuki.ActualGraphCoefficientSystem
open TensorCoefficientChannels Matrix
universe u

section Nonunital
variable {D A₀ A₁ P C : Type u}
  [CStarAlgebra D] [CStarAlgebra A₀] [CStarAlgebra A₁] [CStarAlgebra P]
  [CStarAlgebra C]
variable {i₀ : D →⋆ₐ[ℂ] A₀} {i₁ : D →⋆ₐ[ℂ] A₁}
  {j₀ : A₀ →⋆ₐ[ℂ] P} {j₁ : A₁ →⋆ₐ[ℂ] P}
  (h : CStarAmalgam.IsFullAmalgam i₀ i₁ j₀ j₁)
  (f₀ : A₀ →⋆ₙₐ[ℂ] C) (f₁ : A₁ →⋆ₙₐ[ℂ] C)
  (hf : f₀.comp i₀.toNonUnitalStarAlgHom = f₁.comp i₁.toNonUnitalStarAlgHom)

include hf in
theorem compatible_units : f₁ 1 = f₀ 1 := by
  simpa using (DFunLike.congr_fun hf 1).symm

private def cornerLeft : A₀ →⋆ₐ[ℂ] CommonCorner.Corner (CommonCorner.image_one_projection f₀) :=
  CommonCorner.toCornerHom f₀ _ rfl
private def cornerRight : A₁ →⋆ₐ[ℂ] CommonCorner.Corner (CommonCorner.image_one_projection f₀) :=
  CommonCorner.toCornerHom f₁ _ (compatible_units f₀ f₁ hf)
private theorem corner_compatible :
    (cornerLeft f₀).comp i₀ = (cornerRight f₀ f₁ hf).comp i₁ := by
  apply StarAlgHom.ext
  intro d
  exact Subtype.ext (DFunLike.congr_fun hf d)

def nonunitalLift : P →⋆ₙₐ[ℂ] C :=
  (CommonCorner.inclusion (CommonCorner.image_one_projection f₀)).comp
    (h.lift (cornerLeft f₀) (cornerRight f₀ f₁ hf)
      (corner_compatible f₀ f₁ hf)).toNonUnitalStarAlgHom

@[simp] theorem nonunitalLift_left (a : A₀) : nonunitalLift h f₀ f₁ hf (j₀ a) = f₀ a := by
  have ha := DFunLike.congr_fun (h.lift_left (cornerLeft f₀) (cornerRight f₀ f₁ hf)
      (corner_compatible f₀ f₁ hf)) a
  exact congrArg Subtype.val ha

@[simp] theorem nonunitalLift_right (a : A₁) : nonunitalLift h f₀ f₁ hf (j₁ a) = f₁ a := by
  have ha := DFunLike.congr_fun (h.lift_right (cornerLeft f₀) (cornerRight f₀ f₁ hf)
      (corner_compatible f₀ f₁ hf)) a
  exact congrArg Subtype.val ha

@[simp] theorem nonunitalLift_one : nonunitalLift h f₀ f₁ hf 1 = f₀ 1 := by
  simpa using nonunitalLift_left h f₀ f₁ hf 1

include h in
theorem nonunital_hom_ext {φ ψ : P →⋆ₙₐ[ℂ] C}
    (h₀ : ∀ a, φ (j₀ a) = ψ (j₀ a)) (h₁ : ∀ a, φ (j₁ a) = ψ (j₁ a)) : φ = ψ := by
  have hu : φ 1 = ψ 1 := by simpa using h₀ 1
  let hp := CommonCorner.image_one_projection ψ
  let φ' := CommonCorner.toCornerHom φ hp hu
  let ψ' := CommonCorner.toCornerHom ψ hp rfl
  have he : φ' = ψ' := h.hom_ext
    (StarAlgHom.ext fun a => Subtype.ext (h₀ a))
    (StarAlgHom.ext fun a => Subtype.ext (h₁ a))
  exact NonUnitalStarAlgHom.ext fun x => congrArg Subtype.val (DFunLike.congr_fun he x)

end Nonunital

/-- The tensor amplification equals the ordinary entrywise matrix map. -/
theorem amplifiedMap_entrywise (T : Spatial.{u}) {A B : Algebra.{u}}
    (q : ℕ) (f : A →⋆ₐ[ℂ] B) (x : amplification A q) (r s : ULift.{u} (Fin q)) :
    T.amplifiedMap q f x r s = f (x r s) := by
  let g := CStarMatrix.mapₙₐ (n := ULift.{u} (Fin q)) f.toNonUnitalStarAlgHom
  have he : ((T.amplifiedMap q f).toNonUnitalStarAlgHom.comp
      (T.matrixEquiv A q).toStarAlgHom.toNonUnitalStarAlgHom) =
      g.comp (T.matrixEquiv A q).toStarAlgHom.toNonUnitalStarAlgHom := by
    apply T.hom_ext
    intro a m
    apply CStarMatrix.ext
    intro i j
    change (T.amplifiedMap q f (T.matrixEquiv A q (T.pure a m))) i j = _
    rw [T.amplifiedMap_matrixEquiv]
    change (T.matrixEquiv B q (T.pure (f a) m)) i j =
      f ((T.matrixEquiv A q (T.pure a m)) i j)
    simp only [Spatial.pure, T.matrixEquiv_pure, map_smul]
  have hx := DFunLike.congr_fun he ((T.matrixEquiv A q).symm x)
  change T.amplifiedMap q f (T.matrixEquiv A q ((T.matrixEquiv A q).symm x)) =
    g (T.matrixEquiv A q ((T.matrixEquiv A q).symm x)) at hx
  have hx' : T.amplifiedMap q f x = g x := by simpa only [StarAlgEquiv.apply_symm_apply] using hx
  exact congrArg (fun z => z r s) hx'

section Coordinates
open MultiplicityEmbeddings WeightedGraphAmalgam
variable {V : Type} [Fintype V] [DecidableEq V]

def piStarEquiv {A B : V → Type} [∀ v, CStarAlgebra (A v)] [∀ v, CStarAlgebra (B v)]
    (e : ∀ v, A v ≃⋆ₐ[ℂ] B v) : (∀ v, A v) ≃⋆ₐ[ℂ] (∀ v, B v) where
  toFun a v := e v (a v)
  invFun b v := (e v).symm (b v)
  left_inv a := funext fun v => (e v).symm_apply_apply (a v)
  right_inv a := funext fun v => (e v).apply_symm_apply (a v)
  map_mul' a b := funext fun v => map_mul (e v) (a v) (b v)
  map_add' a b := funext fun v => map_add (e v) (a v) (b v)
  map_smul' z a := funext fun v => map_smul (e v) z (a v)
  map_star' a := funext fun v => map_star (e v) (a v)

def castBlocks {w d : V → ℕ} (h : w = d) : Blocks w ≃⋆ₐ[ℂ] Blocks d :=
  h ▸ StarAlgEquiv.refl ℂ (Blocks w)

omit [Fintype V] [DecidableEq V] in
theorem castBlocks_multiplicity {W : Type} [Fintype W] [DecidableEq W]
    (w : W → ℕ) (M : Matrix V W ℕ) (d : V → ℕ) (hd : targetSize w M = d) (a : Blocks w) :
    castBlocks hd (multiplicityHom w M a) = intoDimensions w M d hd a := by
  subst d
  rfl

def firstCoordinates (k l : V → ℕ) : FirstFactor k l ≃⋆ₐ[ℂ] Blocks (k+l) :=
  (piStarEquiv fun v => CStarMatrix.reindexₐ ℂ ℂ
    (GraphCommonInclusions.first_standard_coordinates k l v).choose).trans
      (castBlocks (first_targetSize k l))

def secondRowCoordinates (M : Matrix V V ℕ) (k l : V → ℕ) (v : V) :
    CStarMatrix (BlockIndex (source := GraphRelations.matrixSource M)
      (target := GraphRelations.matrixTarget M) k l v)
      (BlockIndex (source := GraphRelations.matrixSource M)
      (target := GraphRelations.matrixTarget M) k l v) ℂ ≃⋆ₐ[ℂ]
    CStarMatrix (Fin (targetSize (Sum.elim k l) (secondMultiplicity M) v))
      (Fin (targetSize (Sum.elim k l) (secondMultiplicity M) v)) ℂ :=
  CStarMatrix.reindexₐ ℂ ℂ (GraphCommonInclusions.second_standard_coordinates k l M v).choose

def secondCoordinates (M : Matrix V V ℕ) (k l : V → ℕ) :
    Factor (source := GraphRelations.matrixSource M) (target := GraphRelations.matrixTarget M) k l
      ≃⋆ₐ[ℂ] Blocks (k+M*ᵥl) :=
  (piStarEquiv (A := fun v => CStarMatrix
    (BlockIndex (source := GraphRelations.matrixSource M) (target := GraphRelations.matrixTarget M) k l v)
    (BlockIndex (source := GraphRelations.matrixSource M) (target := GraphRelations.matrixTarget M) k l v) ℂ)
    (B := fun v => CStarMatrix (Fin (targetSize (Sum.elim k l) (secondMultiplicity M) v))
      (Fin (targetSize (Sum.elim k l) (secondMultiplicity M) v)) ℂ)
    (secondRowCoordinates M k l)).trans
      (castBlocks (second_targetSize M k l))

@[simp] theorem firstCoordinates_inclusion (k l : V → ℕ) (a : Blocks (Sum.elim k l)) :
    firstCoordinates k l (GraphCommonInclusions.first k l a) = firstInclusion k l a := by
  change castBlocks _ ((piStarEquiv _) (GraphCommonInclusions.first k l a)) = _
  have hh : (piStarEquiv fun v => CStarMatrix.reindexₐ ℂ ℂ
      (GraphCommonInclusions.first_standard_coordinates k l v).choose)
      (GraphCommonInclusions.first k l a) = multiplicityHom (Sum.elim k l) firstMultiplicity a := by
    funext v
    exact (GraphCommonInclusions.first_standard_coordinates k l v).choose_spec a
  rw [hh]
  exact castBlocks_multiplicity _ _ _ _ _

@[simp] theorem secondCoordinates_inclusion (M : Matrix V V ℕ) (k l : V → ℕ)
    (a : Blocks (Sum.elim k l)) :
    secondCoordinates M k l
      (GraphCommonInclusions.second (GraphRelations.matrixSource M) (GraphRelations.matrixTarget M) k l a) =
      secondInclusion M k l a := by
  change castBlocks _ ((piStarEquiv (secondRowCoordinates M k l)) _) = _
  have hh : (piStarEquiv (secondRowCoordinates M k l))
      (GraphCommonInclusions.second (GraphRelations.matrixSource M) (GraphRelations.matrixTarget M) k l a) =
        multiplicityHom (Sum.elim k l) (secondMultiplicity M) a := by
    funext v
    exact (GraphCommonInclusions.second_standard_coordinates k l M v).choose_spec a
  rw [hh]
  exact castBlocks_multiplicity _ _ _ _ _

end Coordinates

/-- Lift an actual coordinate equivalence without restricting its carrier universe. -/
def liftEquiv {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (e : A ≃⋆ₐ[ℂ] B) : UniverseLift.algebra.{u} A ≃⋆ₐ[ℂ] UniverseLift.algebra.{u} B :=
  ((UniverseLift.equiv A).trans e).trans (UniverseLift.equiv B).symm

section StandardGraph
open MultiplicityEmbeddings WeightedGraphAmalgam GraphCornerIdentification
variable {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℕ) (k l : V → ℕ)
    (hk : ∀ v, 0 < k v) (hl : ∀ v, 0 < l v)
    (hns : ∀ w, ∃ v, 0 < M v w)

local instance : PartialOrder (GraphUniversal.Algebra.{u}
    (GraphRelations.matrixSource M) (GraphRelations.matrixTarget M)) :=
  CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (GraphUniversal.Algebra.{u}
    (GraphRelations.matrixSource M) (GraphRelations.matrixTarget M)) :=
  CStarAlgebra.spectralOrderedRing _

def graphProduct : Algebra.{u} := UniverseLift.algebra
  (graphCorner.{u} (source := GraphRelations.matrixSource M)
    (target := GraphRelations.matrixTarget M) k l)

def graphFirst : UniverseLift.algebra.{u} (Blocks (k+l)) →⋆ₐ[ℂ] graphProduct.{u} M k l :=
  (UniverseLift.map (firstFactorHom
    (graphFamily.{u} (source := GraphRelations.matrixSource M)
      (target := GraphRelations.matrixTarget M)) k l)).comp
      (liftEquiv (firstCoordinates k l)).symm.toStarAlgHom

def graphSecond : UniverseLift.algebra.{u} (Blocks (k+M*ᵥl)) →⋆ₐ[ℂ] graphProduct.{u} M k l :=
  (UniverseLift.map (factorHom
    (graphFamily.{u} (source := GraphRelations.matrixSource M)
      (target := GraphRelations.matrixTarget M)) k l hk
      ((GraphRelations.matrix_noSinks_iff M).mpr hns))).comp
      (liftEquiv (secondCoordinates M k l)).symm.toStarAlgHom

include hl in
/-- The manuscript's literal standard block inclusions have the actual graph
corner as their full amalgam, in every coefficient universe. -/
theorem standardGraph_isFullAmalgam :
    CStarAmalgam.IsFullAmalgam
      (UniverseLift.map.{u} (firstInclusion k l))
      (UniverseLift.map.{u} (secondInclusion M k l))
      (graphFirst.{u} M k l) (graphSecond.{u} M k l hk hns) := by
  let h := graph_isFullAmalgam.{u} (GraphRelations.matrixSource M)
    (GraphRelations.matrixTarget M) k l hk hl ((GraphRelations.matrix_noSinks_iff M).mpr hns)
  have H := amalgam_transport h (StarAlgEquiv.refl ℂ _)
    (liftEquiv (firstCoordinates k l)) (liftEquiv (secondCoordinates M k l))
    (StarAlgEquiv.refl ℂ _)
  have h₀ : (liftEquiv.{u} (firstCoordinates k l)).toStarAlgHom.comp
      ((UniverseLift.map.{u} (GraphCommonInclusions.first k l)).comp
        (StarAlgEquiv.refl ℂ _).symm.toStarAlgHom) = UniverseLift.map.{u} (firstInclusion k l) := by
    apply StarAlgHom.ext
    intro a
    apply ULift.down_injective
    exact firstCoordinates_inclusion k l a.down
  have h₁ : (liftEquiv.{u} (secondCoordinates M k l)).toStarAlgHom.comp
      ((UniverseLift.map.{u} (GraphCommonInclusions.second (GraphRelations.matrixSource M)
        (GraphRelations.matrixTarget M) k l)).comp
        (StarAlgEquiv.refl ℂ _).symm.toStarAlgHom) = UniverseLift.map.{u} (secondInclusion M k l) := by
    apply StarAlgHom.ext
    intro a
    apply ULift.down_injective
    exact secondCoordinates_inclusion M k l a.down
  rw [h₀, h₁] at H
  simpa [graphFirst, graphSecond] using H

end StandardGraph

attribute [local irreducible] graphProduct graphFirst graphSecond

/-- A nonzero nonunital map out of a simple C*-algebra is injective. -/
theorem injective_of_simple {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Target.IsSimple ⟨A, inferInstance⟩) (f : A →⋆ₙₐ[ℂ] B) (hf : f 1 ≠ 0) :
    Function.Injective f := by
  apply (TwoSidedIdeal.ker_eq_bot f).mp
  have hc : IsClosed (TwoSidedIdeal.ker f : Set A) := by
    have he : (TwoSidedIdeal.ker f : Set A) = f ⁻¹' {0} := by
      ext a
      exact TwoSidedIdeal.mem_ker f
    rw [he]
    exact isClosed_singleton.preimage (map_continuous f)
  rcases hA.2 (TwoSidedIdeal.ker f) hc with h | h
  · exact h
  · exact (hf ((TwoSidedIdeal.mem_ker f).mp (h ▸ (show (1 : A) ∈ (⊤ : TwoSidedIdeal A) from trivial)))).elim

section ConcreteBond
open MultiplicityEmbeddings RecursiveGraphSequence
variable {M N : Matrix Vertex Vertex ℕ} {k l k' l' : Vertex → ℕ}
    (hk : ∀ v, 0 < k v) (hl : ∀ v, 0 < l v) (hM : ∀ w, ∃ v, 0 < M v w)
    (hk' : ∀ v, 0 < k' v) (hl' : ∀ v, 0 < l' v) (hN : ∀ w, ∃ v, 0 < N v w)
    (D : ScalarBond M N k l k' l')

include hl' in
private theorem scalarBond_compatible :
    ((graphFirst.{u} N k' l').toNonUnitalStarAlgHom.comp (UniverseLift.nonUnitalMap D.left)).comp
      (UniverseLift.map (firstInclusion k l)).toNonUnitalStarAlgHom =
    ((graphSecond.{u} N k' l' hk' hN).toNonUnitalStarAlgHom.comp (UniverseLift.nonUnitalMap D.right)).comp
      (UniverseLift.map (secondInclusion M k l)).toNonUnitalStarAlgHom := by
  apply NonUnitalStarAlgHom.ext
  intro a
  change graphFirst N k' l' (ULift.up (D.left (firstInclusion k l a.down))) =
    graphSecond N k' l' hk' hN (ULift.up (D.right (secondInclusion M k l a.down)))
  rw [D.first_square, D.second_square]
  have hc := (standardGraph_isFullAmalgam.{u} N k' l' hk' hl' hN).commutes
  exact DFunLike.congr_fun hc (ULift.up (D.common a.down))

/-- The scalar product map induced by one of the actual finite diagrams. -/
def scalarProductMap : graphProduct.{u} M k l →⋆ₙₐ[ℂ] graphProduct.{u} N k' l' :=
  nonunitalLift (standardGraph_isFullAmalgam M k l hk hl hM)
    ((graphFirst N k' l').toNonUnitalStarAlgHom.comp (UniverseLift.nonUnitalMap D.left))
    ((graphSecond N k' l' hk' hN).toNonUnitalStarAlgHom.comp (UniverseLift.nonUnitalMap D.right))
    (scalarBond_compatible hk' hl' hN D)

@[simp] theorem scalarProductMap_left (a : UniverseLift.algebra.{u} (Blocks (k+l))) :
    scalarProductMap hk hl hM hk' hl' hN D (graphFirst M k l a) =
      graphFirst N k' l' (UniverseLift.nonUnitalMap D.left a) :=
  nonunitalLift_left _ _ _ _ _

@[simp] theorem scalarProductMap_right (a : UniverseLift.algebra.{u} (Blocks (k+M*ᵥl))) :
    scalarProductMap hk hl hM hk' hl' hN D (graphSecond M k l hk hM a) =
      graphSecond N k' l' hk' hN (UniverseLift.nonUnitalMap D.right a) :=
  nonunitalLift_right _ _ _ _ _

@[simp] theorem scalarProductMap_one :
    scalarProductMap.{u} hk hl hM hk' hl' hN D 1 =
      graphFirst N k' l' (UniverseLift.nonUnitalMap D.left 1) :=
  nonunitalLift_one _ _ _ _

end ConcreteBond

section LiftMatrix
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

def matrixDown (q : ℕ) : amplification (UniverseLift.algebra.{u} A) q →⋆ₙₐ[ℂ]
    CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A :=
  CStarMatrix.mapₙₐ (UniverseLift.equiv A).toNonUnitalStarAlgHom

@[simp] theorem matrixDown_apply (q : ℕ) (x : amplification (UniverseLift.algebra.{u} A) q)
    (i j : ULift.{u} (Fin q)) : matrixDown q x i j = (x i j).down := rfl

@[simp] theorem matrixDown_one (q : ℕ) : matrixDown.{u} (A := A) q 1 = 1 := by
  apply CStarMatrix.ext
  intro i j
  change (if i = j then (1 : UniverseLift.algebra.{u} A) else 0).down =
    if i = j then (1 : A) else 0
  split_ifs <;> rfl

theorem matrixDown_injective (q : ℕ) : Function.Injective (matrixDown (A := A) q) := by
  intro x y h
  apply CStarMatrix.ext
  intro i j
  apply ULift.down_injective
  exact congrArg (fun z => z i j) h

def liftMatrixHom (q : ℕ)
    (f : CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A →⋆ₙₐ[ℂ] B) :
    amplification (UniverseLift.algebra.{u} A) q →⋆ₙₐ[ℂ] UniverseLift.algebra.{u} B :=
  (UniverseLift.equiv B).symm.toNonUnitalStarAlgHom.comp (f.comp (matrixDown q))

@[simp] theorem liftMatrixHom_one (q : ℕ)
    (f : CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A →⋆ₙₐ[ℂ] B) :
    liftMatrixHom q f 1 = ULift.up (f 1) := by
  change ULift.up (f (matrixDown q 1)) = _
  rw [matrixDown_one]

theorem liftMatrixHom_injective (q : ℕ)
    (f : CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A →⋆ₙₐ[ℂ] B)
    (hf : Function.Injective f) : Function.Injective (liftMatrixHom q f) :=
  (UniverseLift.equiv B).symm.injective.comp (hf.comp (matrixDown_injective q))

end LiftMatrix

/-- Full finite-block support stays nonzero under every unital map to a
nonzero C*-algebra. This removes any need to assume factor-map injectivity. -/
theorem full_blocks_map_ne_zero {V : Type*} [Fintype V] [DecidableEq V]
    {C : Type*} [CStarAlgebra C] [Nontrivial C] (d : V → ℕ)
    (f : MultiplicityEmbeddings.Blocks d →⋆ₐ[ℂ] C)
    (x : MultiplicityEmbeddings.Blocks d) (hx : ∀ v, x v ≠ 0) : f x ≠ 0 := by
  intro he
  have ht := PositiveMultiplicityFullness.ambient_ideal_eq_top d f (TwoSidedIdeal.ker (StarAlgHom.id ℂ C))
    ((TwoSidedIdeal.mem_ker _).mpr he) hx
  have hm : (1 : C) ∈ TwoSidedIdeal.ker (StarAlgHom.id ℂ C) := ht ▸ TwoSidedIdeal.mem_top _
  exact one_ne_zero ((TwoSidedIdeal.mem_ker _).mp hm)

/-- Entrywise universe transport commutes with the actual tensor amplification. -/
theorem matrixDown_natural (T : Spatial.{u}) {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (q : ℕ) (f : A →⋆ₐ[ℂ] B) (x : amplification (UniverseLift.algebra.{u} A) q) :
    matrixDown q (T.amplifiedMap q (UniverseLift.map f) x) =
      CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom (matrixDown q x) := by
  apply CStarMatrix.ext
  intro i j
  change (T.amplifiedMap q (UniverseLift.map f) x i j).down = f ((x i j).down)
  rw [amplifiedMap_entrywise]
  rfl

section ConcreteNoise
open MultiplicityEmbeddings RecursiveGraphSequence
variable (T : Spatial.{u}) {P : Stage} {q : ℕ} (D : Lift P q)
  (hP : ∀ w, ∃ v, 0 < P.A v w) (hQ : ∀ w, ∃ v, 0 < D.next.A v w)
  (Mq : MaximalOn T (matrixAlgebra q))

private theorem noise_compatible :
    ((graphFirst.{u} D.next.A D.next.k D.next.l).toNonUnitalStarAlgHom.comp
      (liftMatrixHom q (D.noiseLeft Equiv.ulift))).comp
        (T.amplifiedMap q (UniverseLift.map (firstInclusion P.k P.l))).toNonUnitalStarAlgHom =
    ((graphSecond.{u} D.next.A D.next.k D.next.l D.next.k_pos hQ).toNonUnitalStarAlgHom.comp
      (liftMatrixHom q (D.noiseRight Equiv.ulift))).comp
        (T.amplifiedMap q (UniverseLift.map (secondInclusion P.A P.k P.l))).toNonUnitalStarAlgHom := by
  apply NonUnitalStarAlgHom.ext
  intro a
  change graphFirst D.next.A D.next.k D.next.l
      (ULift.up (D.noiseLeft Equiv.ulift (matrixDown q (T.amplifiedMap q _ a)))) =
    graphSecond D.next.A D.next.k D.next.l D.next.k_pos hQ
      (ULift.up (D.noiseRight Equiv.ulift (matrixDown q (T.amplifiedMap q _ a))))
  rw [matrixDown_natural, matrixDown_natural, D.noise_first_square, D.noise_second_square]
  exact DFunLike.congr_fun
    (standardGraph_isFullAmalgam D.next.A D.next.k D.next.l D.next.k_pos D.next.l_pos hQ).commutes
    (ULift.up (D.noiseCommon Equiv.ulift (matrixDown q a)))

def noiseProductMap : amplification (graphProduct.{u} P.A P.k P.l) q →⋆ₙₐ[ℂ]
    graphProduct.{u} D.next.A D.next.k D.next.l :=
  nonunitalLift (amplification_isFullAmalgam T q Mq
    (standardGraph_isFullAmalgam P.A P.k P.l P.k_pos P.l_pos hP))
    ((graphFirst D.next.A D.next.k D.next.l).toNonUnitalStarAlgHom.comp
      (liftMatrixHom q (D.noiseLeft Equiv.ulift)))
    ((graphSecond D.next.A D.next.k D.next.l D.next.k_pos hQ).toNonUnitalStarAlgHom.comp
      (liftMatrixHom q (D.noiseRight Equiv.ulift)))
    (noise_compatible T D hQ)

@[simp] theorem noiseProductMap_left
    (a : amplification (UniverseLift.algebra.{u} (Blocks (P.k+P.l))) q) :
    noiseProductMap T D hP hQ Mq (T.amplifiedMap q (graphFirst P.A P.k P.l) a) =
      graphFirst D.next.A D.next.k D.next.l (liftMatrixHom q (D.noiseLeft Equiv.ulift) a) :=
  nonunitalLift_left _ _ _ _ _

@[simp] theorem noiseProductMap_right
    (a : amplification (UniverseLift.algebra.{u} (Blocks (P.k+P.A*ᵥP.l))) q) :
    noiseProductMap T D hP hQ Mq (T.amplifiedMap q (graphSecond P.A P.k P.l P.k_pos hP) a) =
      graphSecond D.next.A D.next.k D.next.l D.next.k_pos hQ
        (liftMatrixHom q (D.noiseRight Equiv.ulift) a) :=
  nonunitalLift_right _ _ _ _ _

@[simp] theorem noiseProductMap_one : noiseProductMap T D hP hQ Mq 1 =
    graphFirst D.next.A D.next.k D.next.l (ULift.up (D.noiseLeft (I := ULift.{u} (Fin q)) Equiv.ulift 1)) := by
  rw [noiseProductMap, nonunitalLift_one]
  change graphFirst D.next.A D.next.k D.next.l (liftMatrixHom q _ 1) = _
  rw [liftMatrixHom_one]

end ConcreteNoise

section GraphChannels
open MultiplicityEmbeddings RecursiveGraphSequence

def graphCommonSmall (P : Stage) : Blocks (Sum.elim P.k P.l) →⋆ₐ[ℂ] graphProduct.{u} P.A P.k P.l :=
  (graphFirst P.A P.k P.l).comp
    ((UniverseLift.equiv (Blocks (P.k+P.l))).symm.toStarAlgHom.comp (firstInclusion P.k P.l))

variable (T : Spatial.{u}) {P : Stage} {q : ℕ} (D : Lift P q)
  (hP : ∀ w, ∃ v, 0 < P.A v w) (hQ : ∀ w, ∃ v, 0 < D.next.A v w)
  (Mq : MaximalOn T (matrixAlgebra q))

def positiveProductMap : graphProduct.{u} P.A P.k P.l →⋆ₙₐ[ℂ] graphProduct.{u} D.next.A D.next.k D.next.l :=
  scalarProductMap P.k_pos P.l_pos hP D.next.k_pos D.next.l_pos hQ D.positiveChannel

def negativeProductMap : graphProduct.{u} P.A P.k P.l →⋆ₙₐ[ℂ] graphProduct.{u} D.next.A D.next.k D.next.l :=
  scalarProductMap P.k_pos P.l_pos hP D.next.k_pos D.next.l_pos hQ D.negativeChannel

@[simp] theorem positiveProductMap_one : positiveProductMap.{u} D hP hQ 1 =
    graphCommonSmall D.next (D.diagram.common 0 1) := by
  rw [positiveProductMap, scalarProductMap_one]
  change graphFirst D.next.A D.next.k D.next.l (ULift.up (D.positiveChannel.left 1)) = _
  have he := D.positiveChannel.first_square 1
  rw [map_one] at he
  rw [he]
  change graphCommonSmall D.next (D.positiveChannel.common 1) = _
  unfold Lift.positiveChannel
  rw [Lift.scalarChannel_common_one]

@[simp] theorem negativeProductMap_one : negativeProductMap.{u} D hP hQ 1 =
    graphCommonSmall D.next (D.diagram.common 1 1) := by
  rw [negativeProductMap, scalarProductMap_one]
  change graphFirst D.next.A D.next.k D.next.l (ULift.up (D.negativeChannel.left 1)) = _
  have he := D.negativeChannel.first_square 1
  rw [map_one] at he
  rw [he]
  change graphCommonSmall D.next (D.negativeChannel.common 1) = _
  unfold Lift.negativeChannel
  rw [Lift.scalarChannel_common_one]

private theorem matrixMap_one {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {I : Type*} [Fintype I] [DecidableEq I] (f : A →⋆ₐ[ℂ] B) :
    CStarMatrix.mapₙₐ (n := I) f.toNonUnitalStarAlgHom 1 = 1 := by
  apply CStarMatrix.ext
  intro i j
  change f (if i = j then 1 else 0) = if i = j then 1 else 0
  split_ifs <;> simp

@[simp] theorem noiseProductMap_common_one : noiseProductMap T D hP hQ Mq 1 =
    graphCommonSmall D.next (D.diagram.common 2 1) := by
  rw [noiseProductMap_one]
  have he := D.noise_first_square (I := ULift.{u} (Fin q)) Equiv.ulift 1
  rw [matrixMap_one] at he
  rw [he]
  change graphCommonSmall D.next (D.noiseCommon Equiv.ulift 1) = _
  rw [D.noiseCommon_one]

theorem positiveProductMap_injective
    (hS : Target.IsSimple ⟨graphProduct.{u} P.A P.k P.l, inferInstance⟩)
    [Nontrivial (graphProduct.{u} D.next.A D.next.k D.next.l)] :
    Function.Injective (positiveProductMap.{u} D hP hQ) := by
  apply injective_of_simple hS
  rw [positiveProductMap_one]
  exact full_blocks_map_ne_zero _ (graphCommonSmall D.next) _ (D.all_common_supports_nonzero 0)

theorem noiseProductMap_injective
    (hS : Target.IsSimple ⟨amplification (graphProduct.{u} P.A P.k P.l) q, inferInstance⟩)
    [Nontrivial (graphProduct.{u} D.next.A D.next.k D.next.l)] :
    Function.Injective (noiseProductMap T D hP hQ Mq) := by
  apply injective_of_simple hS
  rw [noiseProductMap_common_one]
  exact full_blocks_map_ne_zero _ (graphCommonSmall D.next) _ (D.all_common_supports_nonzero 2)

/-- All three product channels are constructed from the actual finite diagrams.
The only extra hypothesis here is ordinary scalar graph simplicity; no channel
correctness or amalgam identity is a field or external theorem premise. -/
def graphScalarChannels
    (hS : Target.IsSimple ⟨graphProduct.{u} P.A P.k P.l, inferInstance⟩)
    [Nontrivial (graphProduct.{u} D.next.A D.next.k D.next.l)] :
    ScalarChannels (graphProduct.{u} P.A P.k P.l) (graphProduct.{u} D.next.A D.next.k D.next.l) q where
  plus := positiveProductMap D hP hQ
  minus := negativeProductMap D hP hQ
  noise := noiseProductMap T D hP hQ Mq
  plus_injective := positiveProductMap_injective D hP hQ hS
  orthogonal c d hcd := by
    let f := graphCommonSmall.{u} D.next
    have hh (a b : Fin 3) (hab : a ≠ b) : f (D.diagram.common a 1) * f (D.diagram.common b 1) = 0 := by
      rw [← map_mul, D.diagram.common_orthogonal a b hab, map_zero]
    cases c <;> cases d <;>
      simp only [positiveProductMap_one, negativeProductMap_one, noiseProductMap_common_one]
    all_goals first | exact (hcd rfl).elim | exact hh _ _ (by decide)
  unit_sum := by
    rw [positiveProductMap_one, negativeProductMap_one, noiseProductMap_common_one,
      ← map_add, ← map_add]
    have he : D.diagram.common 0 1 + D.diagram.common 1 1 + D.diagram.common 2 1 = 1 := by
      simpa [Fin.sum_univ_succ, add_assoc] using D.diagram.common_unit_sum
    rw [he, map_one]

end GraphChannels

section Sequence
open RecursiveGraphSequence

def graphStage (P : Stage) : Algebra.{u} := graphProduct.{u} P.A P.k P.l

theorem stage_adjacency_positive (P : Stage) (v w : Vertex) : 0 < P.A v w := by
  have hp := P.positive v w
  change 0 < P.B v w at hp
  change 0 < Int.toNat ((1 : Matrix Vertex Vertex ℤ) v w + P.B v w)
  have hb : (0 : ℤ) < (1 : Matrix Vertex Vertex ℤ) v w + P.B v w := by
    by_cases hvw : v = w
    · subst w
      simpa using (show (0 : ℤ) < 1 + P.B v v by omega)
    · simpa [Matrix.one_apply, hvw] using hp
  omega

theorem stage_noSinks (P : Stage) : ∀ w, ∃ v, 0 < P.A v w :=
  fun w => ⟨w, stage_adjacency_positive P w w⟩

/-- Actual graph product channels for every step of the constructed recursion.
The local simplicity premise is the ordinary graph-algebra property still to
be instantiated from the separately documented P2 input. -/
def systemGraphChannels (T : Spatial.{u}) {q : ℕ → ℕ} {k l : Vertex → ℕ}
    (S : System q k l) (Mq : ∀ n, MaximalOn T (matrixAlgebra (q n)))
    (hS : ∀ n, Target.IsSimple ⟨graphStage.{u} (S.stage n), inferInstance⟩) (n : ℕ) :
    ScalarChannels (graphStage.{u} (S.stage n)) (graphStage.{u} (S.stage (n+1))) (q n) := by
  let D := S.step n
  have hn : D.next = S.stage (n+1) := S.successor n
  have hnext : Nontrivial (graphStage.{u} D.next) := by
    rw [hn]
    exact (hS (n+1)).1
  letI : Nontrivial (graphProduct.{u} D.next.A D.next.k D.next.l) := hnext
  let G := graphScalarChannels T D (stage_noSinks _) (stage_noSinks _) (Mq n) (hS n)
  exact hn ▸ G

private theorem stage_transport_noise_injective {A : Algebra.{u}} {q : ℕ} {P Q : Stage}
    (e : P = Q) (G : ScalarChannels A (graphStage.{u} P) q) (hG : Function.Injective G.noise) :
    Function.Injective (e ▸ G).noise := by
  cases e
  exact hG

theorem systemGraphChannels_noise_injective (T : Spatial.{u}) {q : ℕ → ℕ} {k l : Vertex → ℕ}
    (S : System q k l) (Mq : ∀ n, MaximalOn T (matrixAlgebra (q n)))
    (hS : ∀ n, Target.IsSimple ⟨graphStage.{u} (S.stage n), inferInstance⟩)
    (hMS : ∀ n, Target.IsSimple ⟨amplification (graphStage.{u} (S.stage n)) (q n), inferInstance⟩)
    (n : ℕ) : Function.Injective (systemGraphChannels T S Mq hS n).noise := by
  have hnext : Nontrivial (graphProduct.{u} (S.step n).next.A (S.step n).next.k (S.step n).next.l) := by
    change Nontrivial (graphStage.{u} (S.step n).next)
    rw [S.successor n]
    exact (hS (n+1)).1
  let := hnext
  unfold systemGraphChannels
  dsimp only
  apply stage_transport_noise_injective
  exact noiseProductMap_injective T (S.step n) (stage_noSinks _) (stage_noSinks _) (Mq n) (hMS n)

end Sequence

section FiniteChannels
open MultiplicityEmbeddings RecursiveGraphSequence
local instance blocksOrder {V : Type*} [Fintype V] (w : V → ℕ) : PartialOrder (Blocks w) :=
  CStarAlgebra.spectralOrder _
local instance blocksStarOrderedRing {V : Type*} [Fintype V] (w : V → ℕ) :
    StarOrderedRing (Blocks w) := CStarAlgebra.spectralOrderedRing _

def channelIndex : TensorCoefficientChannels.Channel → Fin 3
  | .plus => 0 | .minus => 1 | .noise => 2

theorem channelIndex_injective : Function.Injective channelIndex := by
  intro c d h
  cases c <;> cases d <;> simp_all [channelIndex]

private def liftedChannels {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (q : ℕ) (p m : A →⋆ₙₐ[ℂ] B)
    (n : CStarMatrix (ULift.{u} (Fin q)) (ULift.{u} (Fin q)) A →⋆ₙₐ[ℂ] B)
    (hp : Function.Injective p)
    (ho : ∀ c d : TensorCoefficientChannels.Channel, c ≠ d →
      (match c with | .plus => p 1 | .minus => m 1 | .noise => n 1) *
      (match d with | .plus => p 1 | .minus => m 1 | .noise => n 1) = 0)
    (hs : p 1 + m 1 + n 1 = 1) :
    ScalarChannels (UniverseLift.algebra.{u} A) (UniverseLift.algebra.{u} B) q where
  plus := UniverseLift.nonUnitalMap p
  minus := UniverseLift.nonUnitalMap m
  noise := liftMatrixHom q n
  plus_injective := UniverseLift.nonUnitalMap_injective p hp
  orthogonal c d hcd := by
    cases c <;> cases d <;> simp only [liftMatrixHom_one]
    all_goals exact congrArg ULift.up (ho _ _ hcd)
  unit_sum := by
    rw [liftMatrixHom_one]
    exact congrArg ULift.up hs

variable {P : Stage} {q : ℕ} (D : Lift P q)

def commonScalarChannels : ScalarChannels
    (UniverseLift.algebra.{u} (Blocks (Sum.elim P.k P.l)))
    (UniverseLift.algebra.{u} (Blocks (Sum.elim D.next.k D.next.l))) q :=
  liftedChannels q D.positiveChannel.common D.negativeChannel.common (D.noiseCommon Equiv.ulift)
    D.positiveChannel.common_isometry.injective (by
      intro c d hcd
      have he := (D.channel_supports_orthogonal Equiv.ulift (channelIndex c) (channelIndex d)
        (fun h => hcd (channelIndex_injective h))).1
      cases c <;> cases d <;> exact he)
    (D.common_channel_units Equiv.ulift)

def leftScalarChannels : ScalarChannels
    (UniverseLift.algebra.{u} (Blocks (P.k+P.l)))
    (UniverseLift.algebra.{u} (Blocks (D.next.k+D.next.l))) q :=
  liftedChannels q D.positiveChannel.left D.negativeChannel.left (D.noiseLeft Equiv.ulift)
    D.positiveChannel.left_isometry.injective (by
      intro c d hcd
      have he := (D.channel_supports_orthogonal Equiv.ulift (channelIndex c) (channelIndex d)
        (fun h => hcd (channelIndex_injective h))).2.1
      cases c <;> cases d <;> exact he)
    (D.left_channel_units Equiv.ulift)

def rightScalarChannels : ScalarChannels
    (UniverseLift.algebra.{u} (Blocks (P.k+P.A*ᵥP.l)))
    (UniverseLift.algebra.{u} (Blocks (D.next.k+D.next.A*ᵥD.next.l))) q :=
  liftedChannels q D.positiveChannel.right D.negativeChannel.right (D.noiseRight Equiv.ulift)
    D.positiveChannel.right_isometry.injective (by
      intro c d hcd
      have he := (D.channel_supports_orthogonal Equiv.ulift (channelIndex c) (channelIndex d)
        (fun h => hcd (channelIndex_injective h))).2.2
      cases c <;> cases d <;> exact he)
    (D.right_channel_units Equiv.ulift)

theorem commonScalarChannels_noise_injective : Function.Injective (commonScalarChannels.{u} D).noise :=
  liftMatrixHom_injective _ _ (D.noise_isometries Equiv.ulift).1.injective

theorem leftScalarChannels_noise_injective : Function.Injective (leftScalarChannels.{u} D).noise :=
  liftMatrixHom_injective _ _ (D.noise_isometries Equiv.ulift).2.1.injective

theorem rightScalarChannels_noise_injective : Function.Injective (rightScalarChannels.{u} D).noise :=
  liftMatrixHom_injective _ _ (D.noise_isometries Equiv.ulift).2.2.injective

variable (T : Spatial.{u}) {E : Algebra.{u}}
    (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E) (σ : E →⋆ₐ[ℂ] matrixAlgebra.{u} q)

theorem common_left_phi_square :
    ((leftScalarChannels D).phi T ε η σ).comp
      (T.unitalMap (UniverseLift.map (firstInclusion P.k P.l)) (StarAlgHom.id ℂ E)) =
    (T.unitalMap (UniverseLift.map (firstInclusion D.next.k D.next.l)) (StarAlgHom.id ℂ E)).comp
      ((commonScalarChannels D).phi T ε η σ) := by
  apply ScalarChannels.phi_square
  · intro a
    exact congrArg ULift.up (D.positiveChannel.first_square a.down)
  · intro a
    exact congrArg ULift.up (D.negativeChannel.first_square a.down)
  · intro a
    change ULift.up (D.noiseLeft Equiv.ulift (matrixDown q (T.amplifiedMap q _ a))) =
      ULift.up (firstInclusion D.next.k D.next.l (D.noiseCommon Equiv.ulift (matrixDown q a)))
    rw [matrixDown_natural, D.noise_first_square]

theorem common_right_phi_square :
    ((rightScalarChannels D).phi T ε η σ).comp
      (T.unitalMap (UniverseLift.map (secondInclusion P.A P.k P.l)) (StarAlgHom.id ℂ E)) =
    (T.unitalMap (UniverseLift.map (secondInclusion D.next.A D.next.k D.next.l)) (StarAlgHom.id ℂ E)).comp
      ((commonScalarChannels D).phi T ε η σ) := by
  apply ScalarChannels.phi_square
  · intro a
    exact congrArg ULift.up (D.positiveChannel.second_square a.down)
  · intro a
    exact congrArg ULift.up (D.negativeChannel.second_square a.down)
  · intro a
    change ULift.up (D.noiseRight Equiv.ulift (matrixDown q (T.amplifiedMap q _ a))) =
      ULift.up (secondInclusion D.next.A D.next.k D.next.l (D.noiseCommon Equiv.ulift (matrixDown q a)))
    rw [matrixDown_natural, D.noise_second_square]

def commonStage (P : Stage) : Algebra.{u} := UniverseLift.algebra (Blocks (Sum.elim P.k P.l))
def leftStage (P : Stage) : Algebra.{u} := UniverseLift.algebra (Blocks (P.k+P.l))
def rightStage (P : Stage) : Algebra.{u} := UniverseLift.algebra (Blocks (P.k+P.A*ᵥP.l))

variable {sizes : ℕ → ℕ} {k l : Vertex → ℕ}

def systemCommonScalarChannels (S : System sizes k l) (n : ℕ) :
    ScalarChannels (commonStage.{u} (S.stage n)) (commonStage.{u} (S.stage (n+1))) (sizes n) :=
  S.successor n ▸ commonScalarChannels (S.step n)

def systemLeftScalarChannels (S : System sizes k l) (n : ℕ) :
    ScalarChannels (leftStage.{u} (S.stage n)) (leftStage.{u} (S.stage (n+1))) (sizes n) :=
  S.successor n ▸ leftScalarChannels (S.step n)

def systemRightScalarChannels (S : System sizes k l) (n : ℕ) :
    ScalarChannels (rightStage.{u} (S.stage n)) (rightStage.{u} (S.stage (n+1))) (sizes n) :=
  S.successor n ▸ rightScalarChannels (S.step n)

private theorem transport_noise_injective (F : Stage → Algebra.{u}) {A : Algebra.{u}}
    {q : ℕ} {P Q : Stage} (e : P = Q) (G : ScalarChannels A (F P) q)
    (hG : Function.Injective G.noise) : Function.Injective (e ▸ G).noise := by
  cases e
  exact hG

theorem systemCommonScalarChannels_noise_injective (S : System sizes k l) (n : ℕ) :
    Function.Injective (systemCommonScalarChannels.{u} S n).noise :=
  transport_noise_injective commonStage (S.successor n) _ (commonScalarChannels_noise_injective (S.step n))

theorem systemLeftScalarChannels_noise_injective (S : System sizes k l) (n : ℕ) :
    Function.Injective (systemLeftScalarChannels.{u} S n).noise :=
  transport_noise_injective leftStage (S.successor n) _ (leftScalarChannels_noise_injective (S.step n))

theorem systemRightScalarChannels_noise_injective (S : System sizes k l) (n : ℕ) :
    Function.Injective (systemRightScalarChannels.{u} S n).noise :=
  transport_noise_injective rightStage (S.successor n) _ (rightScalarChannels_noise_injective (S.step n))

end FiniteChannels

section ActualProductIdentity
open MultiplicityEmbeddings RecursiveGraphSequence
variable (T : Spatial.{u}) {P : Stage} {q : ℕ} (D : Lift P q)
  (hP : ∀ w, ∃ v, 0 < P.A v w) (hQ : ∀ w, ∃ v, 0 < D.next.A v w)
  (Mq : MaximalOn T (matrixAlgebra q)) {E : Algebra.{u}} (ME : MaximalOn T E)
  (hS : Target.IsSimple ⟨graphProduct.{u} P.A P.k P.l, inferInstance⟩)
  [Nontrivial (graphProduct.{u} D.next.A D.next.k D.next.l)]
  (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E) (σ : E →⋆ₐ[ℂ] matrixAlgebra.{u} q)

/-- The literal coefficient channel sum on the actual graph product is exactly
 the induced full-amalgam map of the actual two finite factor channel sums. -/
theorem actual_phi_is_full_product_map :
    ∃ hf,
      (tensor_isFullAmalgam T ME
        (standardGraph_isFullAmalgam P.A P.k P.l P.k_pos P.l_pos hP)).lift
          ((T.unitalMap (graphFirst D.next.A D.next.k D.next.l) (StarAlgHom.id ℂ E)).comp
            ((leftScalarChannels D).phi T ε η σ))
          ((T.unitalMap (graphSecond D.next.A D.next.k D.next.l D.next.k_pos hQ)
            (StarAlgHom.id ℂ E)).comp ((rightScalarChannels D).phi T ε η σ)) hf =
          (graphScalarChannels T D hP hQ Mq hS).phi T ε η σ := by
  apply phi_is_full_product_map T ME _ _ _ _
    (standardGraph_isFullAmalgam P.A P.k P.l P.k_pos P.l_pos hP)
  · intro a
    exact scalarProductMap_left P.k_pos P.l_pos hP D.next.k_pos D.next.l_pos hQ D.positiveChannel a
  · intro a
    exact scalarProductMap_left P.k_pos P.l_pos hP D.next.k_pos D.next.l_pos hQ D.negativeChannel a
  · intro a
    exact noiseProductMap_left T D hP hQ Mq a
  · intro a
    exact scalarProductMap_right P.k_pos P.l_pos hP D.next.k_pos D.next.l_pos hQ D.positiveChannel a
  · intro a
    exact scalarProductMap_right P.k_pos P.l_pos hP D.next.k_pos D.next.l_pos hQ D.negativeChannel a
  · intro a
    exact noiseProductMap_right T D hP hQ Mq a

end ActualProductIdentity

end Suzuki.ActualGraphCoefficientSystem

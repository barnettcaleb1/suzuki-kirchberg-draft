import Suzuki.CoefficientModelFromExtension
import Suzuki.RecursiveGraphSequence
import Suzuki.TensorCoefficientChannels
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Graph channel K-theory and its faithful free-K KK calculation

Integer calculations are internal. The degree-zero/one K-theory functor and
graph/reference free-source UCT are explicit universal published interfaces.
No new scalar or coefficient channel class is an external field.

Sources: Fima--Germain arXiv:1510.02418v3 (27 Dec 2016), Theorem 4.1;
Rosenberg--Schochet Duke 55 (1987), Theorem 1.17 and
Proposition 7.1; Meyer arXiv:math/0702145v2 (26 Feb 2007), Section 4.
Actual-KK, K-theory, minimal-projection and cone-boundary correspondence are
external. Local finite-cone naturality witnesses are identified explicitly
and are not licensed final mathematical inputs until obtained from the
constructed literal finite diagrams and the universal source interfaces.
-/

noncomputable section
open scoped CStarAlgebra ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Suzuki.GraphChannelKKCalculation
open Matrix PositiveLifting CategoryTheory
open CoefficientModelFromExtension

section IntegerCalculation
variable {n m : Type*} [Fintype n] [Fintype m]

/-- The actual chain map induced on integer cokernels. -/
def onCokernel (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (S H : Matrix m n ℤ) (h : S * B = B' * H) :
    Cokernel B →ₗ[ℤ] Cokernel B' :=
  (LinearMap.range B.mulVecLin).liftQ ((quotient B').comp S.mulVecLin) (by
    rintro x ⟨y, rfl⟩
    change quotient B' (S *ᵥ (B *ᵥ y)) = 0
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨H *ᵥ y, rfl⟩)

@[simp] theorem onCokernel_quotient (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (S H : Matrix m n ℤ) (h : S * B = B' * H) (x : n → ℤ) :
    onCokernel B B' S H h (quotient B x) = quotient B' (S *ᵥ x) := rfl

/-- The actual chain map induced on integer kernels. -/
def onKernel (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (S H : Matrix m n ℤ) (h : S * B = B' * H) :
    Kernel B →ₗ[ℤ] Kernel B' :=
  (H.mulVecLin.comp (Kernel B).subtype).codRestrict (Kernel B') (by
    intro x
    change B' *ᵥ (H *ᵥ x.val) = 0
    have hx : B *ᵥ x.val = 0 := x.property
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero])

@[simp] theorem onKernel_val (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (S H : Matrix m n ℤ) (h : S * B = B' * H) (x : Kernel B) :
    (onKernel B B' S H h x).val = H *ᵥ x.val := rfl

/-- Signed factor coordinates for the finite-cone exact sequence. The first
factor is positive; using v-u would reverse the K0 convention. -/
def pairClass (B : Matrix n n ℤ) (u v : n → ℤ) : Cokernel B := quotient B (u-v)

/-- The extra B'Z in the second factor disappears in the actual cokernel.
This calculates the K0 action from the TWO factor multiplicities, instead
of assuming the desired action as an external channel law. -/
theorem factor_action (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (S H Z : Matrix m n ℤ) (h : S * B = B' * H) (u v : n → ℤ) :
    pairClass B' (S *ᵥ u) ((S + B' * Z) *ᵥ v) =
      onCokernel B B' S H h (pairClass B u v) := by
  unfold pairClass
  rw [onCokernel_quotient, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_sub]
  have he : S *ᵥ u - (S *ᵥ v + B' *ᵥ (Z *ᵥ v)) =
      (S *ᵥ u - S *ᵥ v) - B' *ᵥ (Z *ᵥ v) := by abel
  rw [he, map_sub]
  have hz : quotient B' (B' *ᵥ (Z *ᵥ v)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨Z *ᵥ v, rfl⟩
  rw [hz, sub_zero]

/-- The K1 boundary uses (-y,y); the existing literal block calculation
therefore gives H, independently of all homotopy adjustments Z. -/
theorem boundary_action [DecidableEq n] (B : Matrix n n ℤ) (B' : Matrix m m ℤ)
    (S H Z : Matrix m n ℤ) (h : S * B = B' * H) (y : Kernel B) :
    MatrixDiagrams.diagram B S H Z *ᵥ Sum.elim (-y.val) y.val =
      Sum.elim (-(onKernel B B' S H h y).val) (onKernel B B' S H h y).val :=
  MatrixDiagrams.kernel_action B S H Z y.val y.property

end IntegerCalculation

namespace Recursive
open RecursiveGraphSequence
variable {P : Stage} {q : ℕ} (D : Lift P q)

/-- The chain map calculated from the actual S/H matrices has the recursive
signed cokernel coordinate, for every class (not only a chosen generator). -/
theorem cokernel_coordinate (c : Channel) (x : Cokernel P.B) :
    D.next.cokernel (onCokernel P.B D.next.B (D.S c) (D.H c) (D.chain c) x) =
      sign c * P.cokernel x := by
  refine Submodule.Quotient.induction_on (LinearMap.range P.B.mulVecLin) x ?_
  intro x
  exact D.signed_cokernel c x

theorem kernel_zero (c : Channel) :
    onKernel P.B D.next.B (D.S c) (D.H c) (D.chain c) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact D.kernel_map c x

end Recursive

universe u v w t
variable {K : Type v} [Category.{w} K] [Preadditive K]

/-- EXTERNAL P3. Actual two-degree K-theory of the actual algebra objects,
and the additive action of every KK class. Sources: RS Theorem 1.11 and
the natural map in Theorem 1.17; Meyer v2 Section 4.3. The groups and action
must be interpreted as K_i(A) and Kasparov composition, not arbitrary data. -/
structure KTheory (J : KKInterpretation.{u, v, w} (K := K)) where
  group : Bool → Algebra.{u} → Type t
  abelian : ∀ d A, AddCommGroup (group d A)
  action : ∀ d {A B}, (J.object A ⟶ J.object B) →+
    (group d A →+ group d B)
  action_id : ∀ d A, action d (𝟙 (J.object A)) = AddMonoidHom.id (group d A)
  action_comp : ∀ d {A B C} (f : J.object A ⟶ J.object B)
    (g : J.object B ⟶ J.object C), action d (f ≫ g) = (action d g).comp (action d f)

attribute [instance] KTheory.abelian

variable (J : KKInterpretation.{u, v, w} (K := K)) (G : KTheory.{u,v,w,t} J)

/-- Actual graded action, used as the UCT quotient map. -/
def evaluation {A B : Algebra.{u}} (f : J.object A ⟶ J.object B) :=
  (G.action false f, G.action true f)

/-- EXTERNAL P6. `bootstrap` means membership of the published bootstrap
category, with explicit external semantic correspondence. For each bootstrap
SOURCE with both K-groups isomorphic to Z, Ext vanishes and the graded action
is bijective, for every separable target. RS Theorem 1.17/Prop.7.1. No target
or coefficient UCT is imposed. Graph/reference membership must be supplied
from the actual finite-cone/bootstrap argument; it is not inferred from free K.
This field does not name any channel or prescribe any class. -/
structure FreeUCTInput where
  bootstrap : Algebra.{u} → Prop
  bijective : ∀ (A B : Algebra.{u}), bootstrap A →
    (G.group false A ≃+ ℤ) → (G.group true A ≃+ ℤ) →
    Function.Bijective (evaluation J G (A := A) (B := B))

namespace FreeUCTInput
variable (U : FreeUCTInput J G)

theorem ext {A B : Algebra.{u}} (hA : U.bootstrap A)
    (e₀ : G.group false A ≃+ ℤ) (e₁ : G.group true A ≃+ ℤ)
    {f g : J.object A ⟶ J.object B}
    (h₀ : G.action false f = G.action false g)
    (h₁ : G.action true f = G.action true g) : f = g :=
  (U.bijective A B hA e₀ e₁).injective (Prod.ext h₀ h₁)

/-- Lifting arbitrary prescribed graded maps is generic free-source UCT. -/
def lift {A B : Algebra.{u}} (hA : U.bootstrap A)
    (e₀ : G.group false A ≃+ ℤ) (e₁ : G.group true A ≃+ ℤ)
    (f₀ : G.group false A →+ G.group false B)
    (f₁ : G.group true A →+ G.group true B) : J.object A ⟶ J.object B :=
  Classical.choose ((U.bijective A B hA e₀ e₁).surjective (f₀,f₁))

theorem lift_even {A B : Algebra.{u}} (hA : U.bootstrap A)
    (e₀ : G.group false A ≃+ ℤ) (e₁ : G.group true A ≃+ ℤ)
    (f₀ : G.group false A →+ G.group false B)
    (f₁ : G.group true A →+ G.group true B) :
    G.action false (U.lift J G hA e₀ e₁ f₀ f₁) = f₀ :=
  congrArg Prod.fst (Classical.choose_spec ((U.bijective A B hA e₀ e₁).surjective (f₀,f₁)))

theorem lift_odd {A B : Algebra.{u}} (hA : U.bootstrap A)
    (e₀ : G.group false A ≃+ ℤ) (e₁ : G.group true A ≃+ ℤ)
    (f₀ : G.group false A →+ G.group false B)
    (f₁ : G.group true A →+ G.group true B) :
    G.action true (U.lift J G hA e₀ e₁ f₀ f₁) = f₁ :=
  congrArg Prod.snd (Classical.choose_spec ((U.bijective A B hA e₀ e₁).surjective (f₀,f₁)))

/-- Construct BOTH inverse classes from UCT, once for each bootstrap source.
Freeness alone is never used to infer a KK inverse. -/
def iso {A B : Algebra.{u}} (hA : U.bootstrap A) (hB : U.bootstrap B)
    (a₀ : G.group false A ≃+ ℤ) (a₁ : G.group true A ≃+ ℤ)
    (b₀ : G.group false B ≃+ ℤ) (b₁ : G.group true B ≃+ ℤ)
    (e₀ : G.group false A ≃+ G.group false B)
    (e₁ : G.group true A ≃+ G.group true B) : J.object A ≅ J.object B where
  hom := U.lift J G hA a₀ a₁ e₀.toAddMonoidHom e₁.toAddMonoidHom
  inv := U.lift J G hB b₀ b₁ e₀.symm.toAddMonoidHom e₁.symm.toAddMonoidHom
  hom_inv_id := by
    apply U.ext J G hA a₀ a₁
    · rw [G.action_comp, U.lift_even, U.lift_even, G.action_id]
      ext x; exact e₀.symm_apply_apply x
    · rw [G.action_comp, U.lift_odd, U.lift_odd, G.action_id]
      ext x; exact e₁.symm_apply_apply x
  inv_hom_id := by
    apply U.ext J G hB b₀ b₁
    · rw [G.action_comp, U.lift_even, U.lift_even, G.action_id]
      ext x; exact e₀.apply_symm_apply x
    · rw [G.action_comp, U.lift_odd, U.lift_odd, G.action_id]
      ext x; exact e₁.apply_symm_apply x

end FreeUCTInput

/-- A presentation of the ACTUAL K-groups by the finite-cone homology groups.
These coordinates are local construction data until the graph/corner-to-cone
comparison is instantiated. Fima--Germain Theorem 4.1 supplies an invertible
comparison for unital inclusions with conditional expectations; the finite
matrix coordinates, signs, and compatibility with actual maps remain required.
This is not a theorem asserting that arbitrary algebras have these K-groups. -/
structure GraphCoordinates (A : Algebra.{u}) {n : Type*} [Fintype n]
    (B : Matrix n n ℤ) where
  even : G.group false A ≃+ Cokernel B
  odd : G.group true A ≃+ Kernel B

/-- LOCAL, NOT AN ACCEPTABLE FINAL INPUT. These are the two raw squares of
the finite-cone naturality diagram for an actual star homomorphism. They must
be obtained using the actual factor maps, their retained multiplicity
certificates, and the natural comparison map of the FG cone. In particular
this is not claimed to be a published theorem about the new channels. The
consequences below, including the S/H action and scalar KK class, are proved.
The even square retains BOTH factor maps S and S+B'Z; the odd square retains
the full 2-by-2 block matrix, rather than assuming a desired homology map. -/
structure FiniteConeNaturality {A A' : Algebra.{u}}
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    {B : Matrix n n ℤ} {B' : Matrix m m ℤ}
    (C : GraphCoordinates J G A B) (C' : GraphCoordinates J G A' B')
    (γ : A →⋆ₙₐ[ℂ] A') (S H Z : Matrix m n ℤ) where
  factors : ∀ u v, C'.even (G.action false (J.map (A := A) (B := A') γ)
      (C.even.symm (pairClass B u v))) =
    pairClass B' (S *ᵥ u) ((S + B' * Z) *ᵥ v)
  boundary : ∀ x, Sum.elim (-(C'.odd (G.action true (J.map (A := A) (B := A') γ) x)).val)
      (C'.odd (G.action true (J.map (A := A) (B := A') γ) x)).val =
    MatrixDiagrams.diagram B S H Z *ᵥ Sum.elim (-(C.odd x).val) (C.odd x).val

namespace FiniteConeNaturality
variable {A A' : Algebra.{u}}
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    {B : Matrix n n ℤ} {B' : Matrix m m ℤ}
    {C : GraphCoordinates J G A B} {C' : GraphCoordinates J G A' B'}
    {γ : A →⋆ₙₐ[ℂ] A'} {S H Z : Matrix m n ℤ}
    (N : FiniteConeNaturality J G C C' γ S H Z) (h : S * B = B' * H)

include N in
theorem even_action (x : G.group false A) :
    C'.even (G.action false (J.map (A := A) (B := A') γ) x) =
      onCokernel B B' S H h (C.even x) := by
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_surjective (LinearMap.range B.mulVecLin)) (C.even x)
  have he : C.even.symm (pairClass B y 0) = x := by
    apply C.even.injective
    simpa [pairClass] using hy
  rw [← he, N.factors, factor_action B B' S H Z h, C.even.apply_symm_apply]

include N in
theorem odd_action (x : G.group true A) :
    C'.odd (G.action true (J.map (A := A) (B := A') γ) x) =
      onKernel B B' S H h (C.odd x) := by
  apply Subtype.ext
  funext i
  have hh := N.boundary x
  rw [boundary_action B B' S H Z h] at hh
  exact congrFun hh (Sum.inr i)

end FiniteConeNaturality

namespace Recursive
open RecursiveGraphSequence
variable {P : Stage} {q : ℕ} (D : Lift P q)
    {A A' : Algebra.{u}}
    (C : GraphCoordinates J G A P.B) (C' : GraphCoordinates J G A' D.next.B)
    (c : Channel) (γ : A →⋆ₙₐ[ℂ] A')
    (N : FiniteConeNaturality J G C C' γ (D.S c) (D.H c) (D.Z c))

def evenCoordinate : G.group false A ≃+ ℤ := C.even.trans P.cokernel.toAddEquiv
def oddCoordinate : G.group true A ≃+ ℤ := C.odd.trans P.kernel.toAddEquiv

include N in
theorem signed_even (x : G.group false A) :
    (C'.even.trans D.next.cokernel.toAddEquiv)
      (G.action false (J.map (A := A) (B := A') γ) x) =
        sign c * (C.even.trans P.cokernel.toAddEquiv) x := by
  change D.next.cokernel (C'.even (G.action false (J.map (A := A) (B := A') γ) x)) =
    sign c * P.cokernel (C.even x)
  rw [N.even_action J G (D.chain c)]
  exact cokernel_coordinate D c (C.even x)

include N in
theorem zero_odd (x : G.group true A) :
    G.action true (J.map (A := A) (B := A') γ) x = 0 := by
  apply C'.odd.injective
  rw [N.odd_action J G (D.chain c), kernel_zero D c, LinearMap.zero_apply, map_zero]

end Recursive

/-- The unique graded map which multiplies the even coordinate by z. -/
def coordinateHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (a : A ≃+ ℤ) (b : B ≃+ ℤ) (z : ℤ) : A →+ B :=
  b.symm.toAddMonoidHom.comp (z • a.toAddMonoidHom)

@[simp] theorem coordinateHom_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (a : A ≃+ ℤ) (b : B ≃+ ℤ) (z : ℤ) (x : A) :
    coordinateHom a b z x = b.symm (z * a x) := by
  simp [coordinateHom]

namespace FreeUCTInput
variable (U : FreeUCTInput J G)

/-- The class is CONSTRUCTED by the universal UCT quotient, not an external
input. Only its source is required to belong to the bootstrap category. -/
def diagonal {A B : Algebra.{u}} (hA : U.bootstrap A)
    (a₀ : G.group false A ≃+ ℤ) (a₁ : G.group true A ≃+ ℤ)
    (b₀ : G.group false B ≃+ ℤ) (z : ℤ) : J.object A ⟶ J.object B :=
  U.lift J G hA a₀ a₁ (coordinateHom a₀ b₀ z) 0

theorem map_eq_diagonal {A B : Algebra.{u}} (hA : U.bootstrap A)
    (a₀ : G.group false A ≃+ ℤ) (a₁ : G.group true A ≃+ ℤ)
    (b₀ : G.group false B ≃+ ℤ) (z : ℤ) (γ : A →⋆ₙₐ[ℂ] B)
    (h₀ : ∀ x, b₀ (G.action false (J.map (A := A) (B := B) γ) x) = z * a₀ x)
    (h₁ : ∀ x, G.action true (J.map (A := A) (B := B) γ) x = 0) :
    J.map (A := A) (B := B) γ = U.diagonal J G hA a₀ a₁ b₀ z := by
  apply U.ext J G hA a₀ a₁
  · rw [diagonal, U.lift_even]
    ext x
    apply b₀.injective
    simpa using h₀ x
  · rw [diagonal, U.lift_odd]
    ext x
    exact h₁ x

/-- Generic reference even-coordinate projection, constructed from UCT. Its
identification with the actual projection C⊕SC→C⊕SC requires only the
standard scalar/suspension K-computation, by `map_eq_diagonal`. -/
def referenceProjection {R : Algebra.{u}} (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ) :
    J.object R ⟶ J.object R := U.diagonal J G hR r₀ r₁ r₀ 1

theorem referenceProjection_idempotent {R : Algebra.{u}} (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ) :
    U.referenceProjection J G hR r₀ r₁ ≫ U.referenceProjection J G hR r₀ r₁ =
      U.referenceProjection J G hR r₀ r₁ := by
  apply U.ext J G hR r₀ r₁
  · simp only [G.action_comp, referenceProjection, diagonal, U.lift_even]
    ext x
    simp
  · simp only [G.action_comp, referenceProjection, diagonal, U.lift_odd]
    ext x
    simp

/-- Both directions of kappa are obtained using source UCT, once for A and
once for R. This is not an inference from freeness of K-groups alone. -/
def kappa {A R : Algebra.{u}} (hA : U.bootstrap A) (hR : U.bootstrap R)
    (a₀ : G.group false A ≃+ ℤ) (a₁ : G.group true A ≃+ ℤ)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ) :
    J.object A ≅ J.object R :=
  U.iso J G hA hR a₀ a₁ r₀ r₁ (a₀.trans r₀.symm) (a₁.trans r₁.symm)

theorem kappa_even {A R : Algebra.{u}} (hA : U.bootstrap A) (hR : U.bootstrap R)
    (a₀ : G.group false A ≃+ ℤ) (a₁ : G.group true A ≃+ ℤ)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ) (x : G.group false A) :
    r₀ (G.action false (U.kappa J G hA hR a₀ a₁ r₀ r₁).hom x) = a₀ x := by
  simp [kappa, iso, U.lift_even]

theorem kappa_odd {A R : Algebra.{u}} (hA : U.bootstrap A) (hR : U.bootstrap R)
    (a₀ : G.group false A ≃+ ℤ) (a₁ : G.group true A ≃+ ℤ)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ) (x : G.group true A) :
    r₁ (G.action true (U.kappa J G hA hR a₀ a₁ r₀ r₁).hom x) = a₁ x := by
  simp [kappa, iso, U.lift_odd]

theorem conjugate_diagonal {A B R : Algebra.{u}}
    (hA : U.bootstrap A) (hB : U.bootstrap B) (hR : U.bootstrap R)
    (a₀ : G.group false A ≃+ ℤ) (a₁ : G.group true A ≃+ ℤ)
    (b₀ : G.group false B ≃+ ℤ) (b₁ : G.group true B ≃+ ℤ)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ) (z : ℤ) :
    (U.kappa J G hA hR a₀ a₁ r₀ r₁).inv ≫
      U.diagonal J G hA a₀ a₁ b₀ z ≫
      (U.kappa J G hB hR b₀ b₁ r₀ r₁).hom =
        z • U.referenceProjection J G hR r₀ r₁ := by
  apply U.ext J G hR r₀ r₁
  · simp only [G.action_comp, kappa, iso, diagonal, referenceProjection,
      U.lift_even, map_zsmul]
    ext x
    apply r₀.injective
    simp [coordinateHom]
  · simp only [G.action_comp, kappa, iso, diagonal, referenceProjection,
      U.lift_odd, map_zsmul]
    ext x
    simp

end FreeUCTInput

/-- The complete scalar-channel conclusion of the checked integer reduction
and source UCT. `N` is explicitly local finite-cone correspondence, not an
external assumption on the desired channel class. -/
theorem recursive_scalar_class (U : FreeUCTInput J G)
    {P : RecursiveGraphSequence.Stage} {q : ℕ} (D : RecursiveGraphSequence.Lift P q)
    {A A' R : Algebra.{u}} (C : GraphCoordinates J G A P.B)
    (C' : GraphCoordinates J G A' D.next.B)
    (hA : U.bootstrap A) (hA' : U.bootstrap A') (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ)
    (c : RecursiveGraphSequence.Channel) (γ : A →⋆ₙₐ[ℂ] A')
    (N : FiniteConeNaturality J G C C' γ (D.S c) (D.H c) (D.Z c)) :
    (U.kappa J G hA hR (C.even.trans P.cokernel.toAddEquiv)
      (C.odd.trans P.kernel.toAddEquiv) r₀ r₁).inv ≫
      J.map (A := A) (B := A') γ ≫
      (U.kappa J G hA' hR (C'.even.trans D.next.cokernel.toAddEquiv)
        (C'.odd.trans D.next.kernel.toAddEquiv) r₀ r₁).hom =
      RecursiveGraphSequence.sign c • U.referenceProjection J G hR r₀ r₁ := by
  rw [U.map_eq_diagonal J G hA _ (C.odd.trans P.kernel.toAddEquiv) _ _ γ
    (Recursive.signed_even J G D C C' c γ N)
    (Recursive.zero_odd J G D C C' c γ N)]
  exact U.conjugate_diagonal J G hA hA' hR _ _ _ _ r₀ r₁ _

end Suzuki.GraphChannelKKCalculation

namespace Suzuki.GraphChannelKKCalculation
open Matrix PositiveLifting CategoryTheory CoefficientModelFromExtension
open MultiplicityEmbeddings FiniteDiagram OrthogonalFiniteDiagrams RecursiveGraphSequence

/-! The finite rank and finite-cone interfaces below are deliberately Type 0:
the actual finite graphs are small. Transport to ULift coefficient universes
is separate and is not silently claimed by these declarations. -/

/-- EXTERNAL elementary finite-dimensional K0 support. On strictly positive
block dimensions `action f` is the actual induced K0 map in minimal-projection
coordinates. On zero-sized presentations its value is unspecified; no law
below may be used without the displayed positivity hypotheses. `multiplicity`
is invariance under unitary conjugation/reindexing and additivity of ranks.
`rowCorner` is the rank-one matrix-corner rule, for arbitrary row permutations.
These are universal statements about finite matrix maps, with no graph or
channel conclusion. Source: Blackadar, Operator Algebras, author revision
8 February 2017, V.1.1.1, .4, .6(i), .7, .9, .15--.17 (unitary invariance,
orthogonal addition, finite matrix rank, functoriality and direct sums); the exact
finite-coordinate correspondence remains an explicit external obligation. -/
structure FiniteK0Input where
  action : ∀ {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {k : n → ℕ} {l : m → ℕ}, (Blocks k →⋆ₙₐ[ℂ] Blocks l) →
      ((n → ℤ) →ₗ[ℤ] (m → ℤ))
  comp : ∀ {n m r : Type} [Fintype n] [Fintype m] [Fintype r]
    [DecidableEq n] [DecidableEq m] [DecidableEq r]
    {k : n → ℕ} {l : m → ℕ} {d : r → ℕ}
    (_hk : ∀ i, 0 < k i) (_hl : ∀ i, 0 < l i) (_hd : ∀ i, 0 < d i)
    (f : Blocks k →⋆ₙₐ[ℂ] Blocks l) (g : Blocks l →⋆ₙₐ[ℂ] Blocks d),
      action (g.comp f) = (action g).comp (action f)
  multiplicity : ∀ {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {k : n → ℕ} {l : m → ℕ} (_hk : ∀ i, 0 < k i) (_hl : ∀ i, 0 < l i)
    (M : Matrix m n ℕ) (f : Blocks k →⋆ₐ[ℂ] Blocks l),
      HasMultiplicity k M l f → action f.toNonUnitalStarAlgHom = (M.map Int.ofNat).mulVecLin
  rowCorner : ∀ {C n : Type} [Fintype C] [Fintype n] [DecidableEq C] [DecidableEq n]
    (w : C → n → ℕ) (d : n → ℕ) (c : C)
    (_hw : ∀ i, 0 < w c i) (_hd : ∀ i, 0 < d i)
    (E : ∀ i, (Σ a, Fin (w a i)) ≃ Fin (d i))
    (f : Blocks (w c) →⋆ₙₐ[ℂ] Blocks d),
    (∀ a i, f a i = CStarMatrix.reindexₐ ℂ ℂ (E i)
      (copyHom (fun a => w a i) id (Pi.single c (a i)))) →
    action f = LinearMap.id

namespace FiniteK0Input
variable (F : FiniteK0Input)

theorem factorStack_action {C n m : Type} [Fintype C] [Fintype n] [Fintype m]
    [DecidableEq C] [DecidableEq n] [DecidableEq m]
    (w : C → n → ℕ) (H : Matrix m n ℕ) (c : C)
    (hs : ∀ i, 0 < targetSize (w c) H i)
    (ht : ∀ i, 0 < targetSize (total w) H i) :
    F.action (channel (fun c => Blocks (targetSize (w c) H)) (factorStack w H) c) =
      LinearMap.id := by
  apply F.rowCorner (fun c => targetSize (w c) H) _ c hs ht (factorEquiv w H)
  intro a i
  change CStarMatrix.reindexₐ ℂ ℂ (factorEquiv w H i)
    (copyHom (fun c => targetSize (w c) H i) id
      (fun d => (Pi.single c a : Family (fun c => targetSize (w c) H)) d i)) = _
  congr 2
  funext d
  by_cases h : d = c
  · subst d; simp
  · simp [Pi.single_eq_of_ne h]

theorem canonicalFactor_action {C n m : Type} [Fintype C] [Fintype n] [Fintype m]
    [DecidableEq C] [DecidableEq n] [DecidableEq m]
    (w : C → n → ℕ) (D : n → ℕ) (hD : total w = D)
    (H : Matrix m n ℕ) (d : C → m → ℕ) (hd : ∀ c, targetSize (w c) H = d c)
    (f : m → ℕ) (hf : targetSize D H = f) (c : C)
    (hs : ∀ i, 0 < d c i) (ht : ∀ i, 0 < f i) :
    F.action (channel (fun c => Blocks (d c)) (canonicalFactor w D hD H d hd f hf) c) =
      LinearMap.id := by
  subst D
  have hd' : (fun c => targetSize (w c) H) = d := funext hd
  subst d
  subst f
  exact F.factorStack_action w H c hs ht

theorem stackInto_action {C n : Type} [Fintype C] [Fintype n]
    [DecidableEq C] [DecidableEq n] (w : C → n → ℕ) (D : n → ℕ)
    (hD : total w = D) (c : C) (hs : ∀ i, 0 < w c i) (ht : ∀ i, 0 < D i) :
    F.action (channel (fun c => Blocks (w c)) (stackInto w D hD) c) =
      LinearMap.id := by
  subst D
  apply F.rowCorner _ _ c hs ht (channelEquiv w)
  intro a i
  change CStarMatrix.reindexₐ ℂ ℂ (channelEquiv w i)
    (copyHom (fun c => w c i) id (fun d => (Pi.single c a : Family w) d i)) = _
  congr 2
  funext d
  by_cases h : d = c
  · subst d; simp
  · simp [Pi.single_eq_of_ne h]

theorem commonAggregate_action {C n : Type} [Fintype C] [Fintype n]
    [DecidableEq C] [DecidableEq n] (k l : C → n → ℕ) (c : C)
    (hs : ∀ i, 0 < commonWeights k l c i)
    (ht : ∀ i, 0 < Sum.elim (total k) (total l) i) :
    F.action (channel (fun c => Blocks (commonWeights k l c)) (commonAggregate k l) c) =
      LinearMap.id := F.stackInto_action _ _ (total_commonWeights k l) c hs ht

end FiniteK0Input

namespace Recursive
variable (F : FiniteK0Input) {P : Stage} {q : ℕ} (D : Lift P q)

theorem aggregate_left_K0 (c : Channel) :
    F.action (D.aggregate.left c) = (D.S c).mulVecLin := by
  have hs : ∀ i, 0 < (P.scaledK q c + P.scaledL q c) i :=
    fun i => Nat.add_pos_left (Nat.mul_pos (scale_pos q D.q_pos c) (P.k_pos i)) _
  have hm : ∀ i, 0 < (D.K c + D.L c) i :=
    fun i => Nat.add_pos_left ((D.channel_dimensions_positive c).1 i) _
  have ht : ∀ i, 0 < (D.next.k + D.next.l) i :=
    fun i => Nat.add_pos_left (D.next.k_pos i) _
  rw [D.aggregate_left, F.comp hs hm ht]
  have hh := F.canonicalFactor_action (commonWeights D.K D.L) _ (total_commonWeights D.K D.L)
    firstMultiplicity _ (fun c => first_targetSize (D.K c) (D.L c)) _
    (first_targetSize (total D.K) (total D.L)) c hm ht
  change F.action (channel (fun c => Blocks (D.K c + D.L c)) (canonicalFirst D.K D.L) c) = _ at hh
  rw [hh, LinearMap.id_comp, F.multiplicity hs hm _ _ (D.realization c).left_multiplicity]
  congr 1
  exact natMatrix_cast _ (fun i j => (D.S_pos c i j).le)

theorem aggregate_right_K0 (c : Channel) :
    F.action (D.aggregate.right c) = (D.S c + D.next.B * D.Z c).mulVecLin := by
  have hs : ∀ i, 0 < (P.scaledK q c + P.A *ᵥ P.scaledL q c) i :=
    fun i => Nat.add_pos_left (Nat.mul_pos (scale_pos q D.q_pos c) (P.k_pos i)) _
  have hm : ∀ i, 0 < (D.K c + D.next.A *ᵥ D.L c) i :=
    fun i => Nat.add_pos_left ((D.channel_dimensions_positive c).1 i) _
  have ht : ∀ i, 0 < (D.next.k + D.next.A *ᵥ D.next.l) i :=
    fun i => Nat.add_pos_left (D.next.k_pos i) _
  rw [D.aggregate_right, F.comp hs hm ht]
  have hh := F.canonicalFactor_action (commonWeights D.K D.L) _ (total_commonWeights D.K D.L)
    (secondMultiplicity D.next.A) _ (fun c => second_targetSize D.next.A (D.K c) (D.L c)) _
    (second_targetSize D.next.A (total D.K) (total D.L)) c hm ht
  change F.action (channel (fun c => Blocks (D.K c + D.next.A *ᵥ D.L c))
    (canonicalSecond D.K D.L D.next.A) c) = _ at hh
  rw [hh, LinearMap.id_comp, F.multiplicity hs hm _ _ (D.realization c).right_multiplicity]
  congr 1
  exact natMatrix_cast _ (fun i j => (D.R_pos c i j).le)

theorem aggregate_common_K0 (c : Channel) :
    F.action (D.aggregate.common c) =
      (MatrixDiagrams.diagram P.B (D.S c) (D.H c) (D.Z c)).mulVecLin := by
  have hs : ∀ i, 0 < Sum.elim (P.scaledK q c) (P.scaledL q c) i := by
    intro i; cases i with
    | inl i => exact Nat.mul_pos (scale_pos q D.q_pos c) (P.k_pos i)
    | inr i => exact Nat.mul_pos (scale_pos q D.q_pos c) (P.l_pos i)
  have hm : ∀ i, 0 < commonWeights D.K D.L c i := by
    intro i; cases i with
    | inl i => exact (D.channel_dimensions_positive c).1 i
    | inr i => exact (D.channel_dimensions_positive c).2 i
  have ht : ∀ i, 0 < Sum.elim D.next.k D.next.l i := by
    intro i; cases i with
    | inl i => exact D.next.k_pos i
    | inr i => exact D.next.l_pos i
  rw [D.aggregate_common, F.comp hs hm ht, F.commonAggregate_action D.K D.L c hm ht,
    LinearMap.id_comp, F.multiplicity hs hm _ _ (D.realization c).common_multiplicity]
  congr 1
  exact natMatrix_cast _ (fun i j => (D.T_pos c i j).le)

end Recursive

end Suzuki.GraphChannelKKCalculation

namespace Suzuki.GraphChannelKKCalculation
open Matrix PositiveLifting CategoryTheory CoefficientModelFromExtension
open MultiplicityEmbeddings FiniteDiagram OrthogonalFiniteDiagrams RecursiveGraphSequence

/-- Actual small finite full amalgam, with strictly positive matrix-block
sizes. It is local presentation data, not an external existence theorem. -/
structure FinitePresentation {n : Type} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℤ) (k l : n → ℕ) where
  Carrier : Type
  cstar : CStarAlgebra Carrier
  separable : TopologicalSpace.SeparableSpace Carrier
  positive : Positive B
  k_pos : ∀ i, 0 < k i
  l_pos : ∀ i, 0 < l i
  left : Blocks (k+l) →⋆ₐ[ℂ] Carrier
  right : Blocks (k + natMatrix (1+B) *ᵥ l) →⋆ₐ[ℂ] Carrier
  full : CStarAmalgam.IsFullAmalgam (firstInclusion k l)
    (secondInclusion (natMatrix (1+B)) k l) left right

attribute [instance] FinitePresentation.cstar FinitePresentation.separable
instance {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℤ) (k l : n → ℕ) :
    CoeSort (FinitePresentation B k l) Type := ⟨FinitePresentation.Carrier⟩

def FinitePresentation.actual {n : Type} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℤ} {k l : n → ℕ} (P : FinitePresentation B k l) : Algebra :=
  ⟨P, inferInstance, inferInstance⟩

universe v w t
variable {K : Type v} [Category.{w} K] [Preadditive K]
variable (J : KKInterpretation.{0,v,w} (K := K)) (G : KTheory.{0,v,w,t} J)

/-- EXTERNAL P4/P6, universal finite-cone comparison and naturality. Source:
Fima--Germain 1510.02418v3, Theorem 4.1 (actual inclusion of its D into SP),
ordinary mapping-cone six-term exact-sequence naturality, and RS 1.17/7.1.
Finite-dimensional faithful inclusions have conditional expectations. The
first factor is positive and the second negative in the factor-to-cokernel
map; the K1 boundary is (-y,y). `naturality` quantifies over arbitrary actual
nonunital maps of finite triples and arbitrary compatible actual product maps.
It neither mentions the recursive system nor prescribes S/H/signs/KK classes.

The required EXTERNAL correspondence is stronger than citing FG group
isomorphism alone: coordinates must be chosen from its actual comparison,
and its comparison must commute with the cone map of EVERY displayed square.
No claim is made that the paper explicitly packages this all-diagram law;
it combines that theorem with standard functoriality of the actual cone and
its inclusion. This correspondence must be audited in any final input instance.
The finite-rank action is the SAME actual K0 action as `G`, under matrix-rank
coordinates. No coefficient/target UCT appears. -/
structure FiniteConeInput (F : FiniteK0Input) (U : FreeUCTInput J G) where
  coordinates : ∀ {n : Type} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℤ} {k l : n → ℕ} (P : FinitePresentation B k l),
      GraphCoordinates J G P.actual B
  bootstrap : ∀ {n : Type} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℤ} {k l : n → ℕ} (P : FinitePresentation B k l), U.bootstrap P.actual
  naturality : ∀ {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {B : Matrix n n ℤ} {B' : Matrix m m ℤ} {k l : n → ℕ} {k' l' : m → ℕ}
    (P : FinitePresentation B k l) (Q : FinitePresentation B' k' l')
    (γ : P.actual →⋆ₙₐ[ℂ] Q.actual)
    (d : Blocks (Sum.elim k l) →⋆ₙₐ[ℂ] Blocks (Sum.elim k' l'))
    (f : Blocks (k+l) →⋆ₙₐ[ℂ] Blocks (k'+l'))
    (g : Blocks (k+natMatrix (1+B)*ᵥl) →⋆ₙₐ[ℂ] Blocks (k'+natMatrix (1+B')*ᵥl')),
    (∀ a, f (firstInclusion k l a) = firstInclusion k' l' (d a)) →
    (∀ a, g (secondInclusion (natMatrix (1+B)) k l a) =
      secondInclusion (natMatrix (1+B')) k' l' (d a)) →
    (∀ a, γ (P.left a) = Q.left (f a)) →
    (∀ a, γ (P.right a) = Q.right (g a)) →
    (∀ u v, (coordinates Q).even
      (G.action false (J.map (A := P.actual) (B := Q.actual) γ)
        ((coordinates P).even.symm (pairClass B u v))) =
      pairClass B' (F.action f u) (F.action g v)) ∧
    (∀ x, Sum.elim (-((coordinates Q).odd
      (G.action true (J.map (A := P.actual) (B := Q.actual) γ) x)).val)
      ((coordinates Q).odd (G.action true (J.map (A := P.actual) (B := Q.actual) γ) x)).val =
      F.action d (Sum.elim (-((coordinates P).odd x).val) ((coordinates P).odd x).val))

namespace FiniteConeInput
variable {F : FiniteK0Input} {U : FreeUCTInput J G} (V : FiniteConeInput J G F U)

/-- The local cone witness is now DERIVED from universal naturality, all
three computed finite K0 maps, and the actual product restrictions. Only the
construction of the actual product map/restrictions remains local here. -/
theorem recursive_naturality {P : Stage} {q : ℕ} (D : Lift P q) (c : Channel)
    (A : FinitePresentation P.B (P.scaledK q c) (P.scaledL q c))
    (B : FinitePresentation D.next.B D.next.k D.next.l)
    (γ : A.actual →⋆ₙₐ[ℂ] B.actual)
    (hl : ∀ a, γ (A.left a) = B.left (D.aggregate.left c a))
    (hr : ∀ a, γ (A.right a) = B.right (D.aggregate.right c a)) :
    FiniteConeNaturality J G (V.coordinates A) (V.coordinates B) γ
      (D.S c) (D.H c) (D.Z c) := by
  obtain ⟨h₀,h₁⟩ := V.naturality A B γ (D.aggregate.common c) (D.aggregate.left c)
    (D.aggregate.right c) (D.aggregate.first_square c) (D.aggregate.second_square c) hl hr
  constructor
  · intro u v
    rw [h₀, Recursive.aggregate_left_K0 F D c, Recursive.aggregate_right_K0 F D c]
    rfl
  · intro x
    rw [h₁, Recursive.aggregate_common_K0 F D c]
    rfl

/-- The scalar channel class for ANY actual compatible extension of the
certified finite diagrams. No cone square or new channel class is a hypothesis. -/
theorem recursive_class {P : Stage} {q : ℕ} (D : Lift P q) (c : Channel)
    (A : FinitePresentation P.B (P.scaledK q c) (P.scaledL q c))
    (B : FinitePresentation D.next.B D.next.k D.next.l)
    {R : Algebra} (hR : U.bootstrap R)
    (r₀ : G.group false R ≃+ ℤ) (r₁ : G.group true R ≃+ ℤ)
    (γ : A.actual →⋆ₙₐ[ℂ] B.actual)
    (hl : ∀ a, γ (A.left a) = B.left (D.aggregate.left c a))
    (hr : ∀ a, γ (A.right a) = B.right (D.aggregate.right c a)) :
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

end FiniteConeInput
end Suzuki.GraphChannelKKCalculation

namespace Suzuki.GraphChannelKKCalculation
open CategoryTheory CoefficientModelFromExtension

/-- The literal scalar reference algebra C direct-sum S(C). -/
def scalar : Algebra.{0} := ⟨ℂ, inferInstance, inferInstance⟩
def reference : Algebra.{0} := ⟨ℂ × suspension scalar, inferInstance, inferInstance⟩

/-- The actual first-coordinate endomorphism of the scalar reference. -/
def referenceMap : reference →⋆ₙₐ[ℂ] reference where
  toFun x := (x.1, 0)
  map_zero' := rfl
  map_add' x y := by
    change (x.1+y.1, (0 : suspension scalar)) = (x.1+y.1, 0+0)
    simp
  map_mul' x y := by
    change (x.1*y.1, (0 : suspension scalar)) = (x.1*y.1, 0*0)
    simp
  map_smul' z x := by
    change (z • x.1, (0 : suspension scalar)) = (z • x.1, z • 0)
    simp
  map_star' x := by
    change (star x.1, (0 : suspension scalar)) = (star x.1, star 0)
    simp

universe v w t
variable {K : Type v} [Category.{w} K] [Preadditive K]
variable (J : KKInterpretation.{0,v,w} (K := K)) (G : KTheory.{0,v,w,t} J)

/-- EXTERNAL standard scalar K-theory, suspension, and finite direct sums.
Blackadar 8 February 2017, V.1.1.9/.16(i), V.1.2.3(i); Meyer v2 Theorem 50 (Bott),
and RS bootstrap closure before Theorem 1.17. The map is the ACTUAL displayed
projection, not a newly constructed graph channel. The choice of generators
fixes scalar class 1 and the compatible Bott class. No coefficient UCT. -/
structure ReferenceInput (U : FreeUCTInput J G) where
  bootstrap : U.bootstrap reference
  even : G.group false reference ≃+ ℤ
  odd : G.group true reference ≃+ ℤ
  map_even : G.action false (J.map (A := reference) (B := reference) referenceMap) =
    AddMonoidHom.id (G.group false reference)
  map_odd : G.action true (J.map (A := reference) (B := reference) referenceMap) = 0

namespace ReferenceInput
variable {U : FreeUCTInput J G} (R : ReferenceInput J G U)

/-- The UCT-constructed reference idempotent is the class of the actual
first-coordinate star homomorphism. -/
theorem projection_class :
    U.referenceProjection J G R.bootstrap R.even R.odd =
      J.map (A := reference) (B := reference) referenceMap := by
  symm
  apply U.map_eq_diagonal J G R.bootstrap R.even R.odd R.even 1 referenceMap
  · intro x
    rw [R.map_even]
    simp
  · intro x
    rw [R.map_odd]
    rfl

end ReferenceInput
end Suzuki.GraphChannelKKCalculation

namespace Suzuki.GraphChannelKKCalculation
open CategoryTheory CategoryTheory.Preadditive CoefficientModelFromExtension
universe u v w
variable {K : Type v} [Category.{w} K] [Preadditive K]
variable (J : KKInterpretation.{u,v,w} (K := K))

/-- EXTERNAL P3: degree-zero exterior product on actual separable spatial
tensor algebras, with bilinearity, composition, identity and star-map
correspondence. Meyer math/0702145v2, Section 4.1, p.20, extends the
minimal tensor bifunctor to KK and states the monoidal constraints; RS 1.11(5)
is the product-intersection pairing in its nuclear scope. No Kunneth or UCT
assumption occurs. `tensor`/`map` must be the actual spatial tensor objects/maps
(in particular the same maps as TensorCoefficientChannels when assembled).
Orthogonal additivity is generic for actual maps with pointwise zero cross
products; the supplied sum is an actual star homomorphism. -/
structure ExteriorInput where
  tensor : Algebra.{u} → Algebra.{u} → Algebra.{u}
  map : ∀ {A B C D : Algebra.{u}}, (A →⋆ₙₐ[ℂ] B) → (C →⋆ₙₐ[ℂ] D) →
    (tensor A C →⋆ₙₐ[ℂ] tensor B D)
  product : ∀ {A B C D : Algebra.{u}}, (J.object A ⟶ J.object B) →+
    ((J.object C ⟶ J.object D) →+ (J.object (tensor A C) ⟶ J.object (tensor B D)))
  product_id : ∀ A C, product (𝟙 (J.object A)) (𝟙 (J.object C)) = 𝟙 (J.object (tensor A C))
  product_comp : ∀ {A B C D E F : Algebra.{u}}
    (f : J.object A ⟶ J.object B) (g : J.object B ⟶ J.object C)
    (h : J.object D ⟶ J.object E) (k : J.object E ⟶ J.object F),
    product (f ≫ g) (h ≫ k) = product f h ≫ product g k
  map_class : ∀ {A B C D : Algebra.{u}} (f : A →⋆ₙₐ[ℂ] B) (g : C →⋆ₙₐ[ℂ] D),
    J.map (A := tensor A C) (B := tensor B D) (map f g) =
      product (J.map (A := A) (B := B) f) (J.map (A := C) (B := D) g)
  orthogonal_sum : ∀ {A B : Algebra.{u}} {n : Type} [Fintype n]
    (f : n → A →⋆ₙₐ[ℂ] B) (φ : A →⋆ₙₐ[ℂ] B),
    (∀ i j, i ≠ j → ∀ x y, f i x * f j y = 0) →
    (∀ x, φ x = ∑ i, f i x) →
    J.map (A := A) (B := B) φ = ∑ i, J.map (A := A) (B := B) (f i)

namespace ExteriorInput
variable (T : ExteriorInput J)

def tensorIso {A B : Algebra.{u}} (e : J.object A ≅ J.object B) (E : Algebra.{u}) :
    J.object (T.tensor A E) ≅ J.object (T.tensor B E) where
  hom := T.product e.hom (𝟙 (J.object E))
  inv := T.product e.inv (𝟙 (J.object E))
  hom_inv_id := by rw [← T.product_comp, e.hom_inv_id, Category.id_comp, T.product_id]
  inv_hom_id := by rw [← T.product_comp, e.inv_hom_id, Category.id_comp, T.product_id]

/-- The exterior tensor calculation transports actual scalar classes; its
input is the scalar result already derived above, never coefficient UCT. -/
theorem transport_product {A B R E : Algebra.{u}}
    (a : J.object A ≅ J.object R) (b : J.object B ≅ J.object R)
    (f : J.object A ⟶ J.object B) (g : J.object E ⟶ J.object E) :
    (T.tensorIso J a E).inv ≫ T.product f g ≫ (T.tensorIso J b E).hom =
      T.product (a.inv ≫ f ≫ b.hom) g := by
  change T.product a.inv (𝟙 _) ≫ T.product f g ≫ T.product b.hom (𝟙 _) = _
  rw [← T.product_comp, ← T.product_comp, Category.comp_id, Category.id_comp]

/-- Bilinearity computes the signed plus/minus/zero sum. This is a generic
calculation on exterior classes, not an assertion identifying a new bond. -/
theorem signed_sum {R E : Algebra.{u}} (p : J.object R ⟶ J.object R)
    (e : J.object E ⟶ J.object E) :
    T.product p (𝟙 (J.object E)) + T.product (-p) e + 0 =
      T.product p (𝟙 (J.object E) - e) := by
  rw [(T.product p).map_sub, map_neg, AddMonoidHom.neg_apply, add_zero]
  exact (sub_eq_add_neg _ _).symm

theorem reduced_product_idempotent {R E : Algebra.{u}}
    (p : J.object R ⟶ J.object R) (e : J.object E ⟶ J.object E)
    (hp : p ≫ p = p) (he : e ≫ e = e) :
    T.product p (𝟙 (J.object E)-e) ≫ T.product p (𝟙 (J.object E)-e) =
      T.product p (𝟙 (J.object E)-e) := by
  rw [← T.product_comp, hp]
  congr 1
  simp only [sub_comp, comp_sub, Category.id_comp, Category.comp_id, he]
  abel

/-- Actual tensor star-map classes obey the transported scalar calculation. -/
theorem transport_map {A B R E : Algebra.{u}}
    (a : J.object A ≅ J.object R) (b : J.object B ≅ J.object R)
    (f : A →⋆ₙₐ[ℂ] B) (g : E →⋆ₙₐ[ℂ] E) :
    (T.tensorIso J a E).inv ≫
      J.map (A := T.tensor A E) (B := T.tensor B E) (T.map f g) ≫
      (T.tensorIso J b E).hom =
    T.product (a.inv ≫ J.map (A := A) (B := B) f ≫ b.hom)
      (J.map (A := E) (B := E) g) := by
  rw [T.map_class, T.transport_product]

/-- Actual zero-class channels remain zero after arbitrary actual pre/post
composition. This is how the amplified noise channel disappears in KK. -/
theorem zero_channel {A B C D : Algebra.{u}}
    (pre : A →⋆ₙₐ[ℂ] B) (f : B →⋆ₙₐ[ℂ] C) (post : C →⋆ₙₐ[ℂ] D)
    (hf : J.map (A := B) (B := C) f = 0) :
    J.map (A := A) (B := D) (post.comp (f.comp pre)) = 0 := by
  rw [J.map_comp, J.map_comp, hf, Limits.comp_zero, Limits.zero_comp]

end ExteriorInput
end Suzuki.GraphChannelKKCalculation

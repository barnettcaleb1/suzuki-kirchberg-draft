import Suzuki.ConditionalKK

/-!
# Transport of the analytic Milnor sequence and the prescribed class

The external input here is the analytic Milnor sequence for the *varying*
stage objects.  The change of coordinates to the manuscript's fixed object
`X = E ⊕ SE` is proved, not included in that input.  Likewise the inverse
class is restricted back to the actual stage coordinates explicitly.

This is an abstract KK interface, with the same external correspondence
obligation as `ConditionalKK`.  Actual stage algebras, their nuclearity,
the channel-class equation, and the common projection's coordinate class
are internal construction obligations, not published inputs or conclusions
of this module.  No UCT condition on the coefficient or target is present.
-/

noncomputable section
namespace Suzuki.ConditionalKKTransport
open CategoryTheory CategoryTheory.Preadditive Suzuki.ConditionalKK

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- EXTERNAL INPUT: product-boundary formulation of the analytic Milnor
sequence for a sequential system.  Its use with actual KK theory requires
separable nuclear stages, an actual sequential C*-limit and its canonical
maps, and the usual suspension identification of degree-one groups.
The three fields say descent through coker(1-shift), exactness at the limit
Hom group, and surjectivity onto compatible families. -/
structure AnalyticMilnorInput (S : C → C) (Q : ℕ → C)
    (bond : ∀ n, Q n ⟶ Q (n+1)) {L : C} (stage : ∀ n, Q n ⟶ L) where
  boundary : ∀ Z : C, (∀ n, Q n ⟶ S Z) →+ (L ⟶ Z)
  boundary_coboundary : ∀ (Z : C) (a : ∀ n, Q n ⟶ S Z),
    boundary Z (fun n => a n - bond n ≫ a (n+1)) = 0
  kernel : ∀ (Z : C) (a : L ⟶ Z), (∀ n, stage n ≫ a = 0) →
    ∃ b : ∀ n, Q n ⟶ S Z, boundary Z b = a
  onto : ∀ (Z : C) (x : ∀ n, Q n ⟶ Z),
    (∀ n, bond n ≫ x (n+1) = x n) → ∃ a : L ⟶ Z, ∀ n, stage n ≫ a = x n

variable {Q : ℕ → C} {X L : C} (coordinate : ∀ n, Q n ≅ X)
variable (bond : ∀ n, Q n ⟶ Q (n+1)) (stage : ∀ n, Q n ⟶ L)
variable (f : X ⟶ X)

/-- A sequence of coordinate classes is pulled back to the original stages. -/
def fromCoordinates (Z : C) : (ℕ → (X ⟶ Z)) →+ (∀ n, Q n ⟶ Z) where
  toFun x n := (coordinate n).hom ≫ x n
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

def coordinateStage (n : ℕ) : X ⟶ L := (coordinate n).inv ≫ stage n

omit [Preadditive C] in
theorem recover_stage (n : ℕ) :
    (coordinate n).hom ≫ coordinateStage coordinate stage n = stage n := by
  simp [coordinateStage, ← Category.assoc]

variable (hbond : ∀ n, bond n ≫ (coordinate (n+1)).hom = (coordinate n).hom ≫ f)
variable (hstage : ∀ n, bond n ≫ stage (n+1) = stage n)

omit [Preadditive C] in
include hbond in
/-- Inverting the actual coordinate isomorphisms transports the bonding map. -/
theorem inverse_bond (n : ℕ) :
    (coordinate n).inv ≫ bond n = f ≫ (coordinate (n+1)).inv := by
  apply (cancel_mono (coordinate (n+1)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hbond n, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

omit [Preadditive C] in
include hbond hstage in
/-- The actual stage compatibility implies the fixed-coordinate compatibility. -/
theorem coordinateStage_compatible (n : ℕ) :
    f ≫ coordinateStage coordinate stage (n+1) = coordinateStage coordinate stage n := by
  simp only [coordinateStage]
  rw [← Category.assoc, ← inverse_bond coordinate bond f hbond n,
    Category.assoc, hstage n]

variable (S : C → C) (M : AnalyticMilnorInput S Q bond stage)

include hbond in
/-- Transport of the published sequence is a proof, with all coordinate
and bonding equations visible in the type. -/
def toFixedMilnor : MilnorInput S f (coordinateStage coordinate stage) where
  boundary Z := (M.boundary Z).comp (fromCoordinates coordinate (S Z))
  boundary_coboundary Z a := by
    change M.boundary Z (fun n => (coordinate n).hom ≫ (a n - f ≫ a (n+1))) = 0
    have he : (fun n => (coordinate n).hom ≫ (a n - f ≫ a (n+1))) =
        (fun n => (coordinate n).hom ≫ a n - bond n ≫ ((coordinate (n+1)).hom ≫ a (n+1))) := by
      funext n
      rw [comp_sub, ← Category.assoc (bond n), hbond n, Category.assoc]
    rw [he]
    exact M.boundary_coboundary Z (fun n => (coordinate n).hom ≫ a n)
  kernel Z a ha := by
    have hz : ∀ n, stage n ≫ a = 0 := by
      intro n
      rw [← recover_stage coordinate stage n, Category.assoc, ha n]
      simp
    obtain ⟨b, hb⟩ := M.kernel Z a hz
    refine ⟨fun n => (coordinate n).inv ≫ b n, ?_⟩
    change M.boundary Z (fun n => (coordinate n).hom ≫ ((coordinate n).inv ≫ b n)) = a
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hb
  onto Z x hx := by
    have hc : ∀ n, bond n ≫ ((coordinate (n+1)).hom ≫ x (n+1)) =
        (coordinate n).hom ≫ x n := by
      intro n
      rw [← Category.assoc, hbond n, Category.assoc, hx n]
    obtain ⟨a, ha⟩ := M.onto Z (fun n => (coordinate n).hom ≫ x n) hc
    refine ⟨a, fun n => ?_⟩
    rw [coordinateStage, Category.assoc, ha n, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]

variable {F : C} (R : Splitting F X)

/-- The resulting invertible class is obtained from the actual stage sequence,
conditional on its explicitly stated channel-coordinate and Milnor inputs. -/
def limitIso
    (hb : ∀ n, bond n ≫ (coordinate (n+1)).hom = (coordinate n).hom ≫ R.f)
    (hs : ∀ n, bond n ≫ stage (n+1) = stage n) : F ≅ L :=
  R.iso S (coordinateStage coordinate stage)
    (coordinateStage_compatible coordinate bond stage R.f hb hs)
    (toFixedMilnor coordinate bond stage R.f hb S M)

variable (hb : ∀ n, bond n ≫ (coordinate (n+1)).hom = (coordinate n).hom ≫ R.f)
variable (hs : ∀ n, bond n ≫ stage (n+1) = stage n)

/-- Crucial restriction formula in the original, varying stage coordinates. -/
theorem inverse_stage (n : ℕ) :
    stage n ≫ (limitIso coordinate bond stage S M R hb hs).inv =
      (coordinate n).hom ≫ R.s := by
  rw [← recover_stage coordinate stage n, Category.assoc]
  congr 1
  exact R.inverse_stage S (coordinateStage coordinate stage)
    (coordinateStage_compatible coordinate bond stage R.f hb hs)
    (toFixedMilnor coordinate bond stage R.f hb S M) n

/-- Once the *actual* common projection's stage class has the claimed
coordinate, the inverse sends it to the prescribed reduced coefficient class.
The coordinate equation is an internal obligation, not a licensed input. -/
theorem prescribed_class {K : C} (n : ℕ) (a : K ⟶ Q n) (u : K ⟶ F)
    (ha : a ≫ (coordinate n).hom = u ≫ R.j) :
    (a ≫ stage n) ≫ (limitIso coordinate bond stage S M R hb hs).inv = u := by
  rw [Category.assoc, inverse_stage coordinate bond stage S M R hb hs n,
    ← Category.assoc, ha, Category.assoc, R.retract, Category.comp_id]

end Suzuki.ConditionalKKTransport

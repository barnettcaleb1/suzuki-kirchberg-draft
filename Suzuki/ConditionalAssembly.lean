import Suzuki.ConditionalKKTransport
import Suzuki.ConditionalClassification

/-!
# Assembly of the prescribed common corner

This connects the proved varying-stage Milnor argument to the exact
unit-preserving classification input. In particular, unit preservation of
the *final* KK equivalence is proved from the initial projection's coordinate;
it is not an additional classification hypothesis supplied by the caller.

This is not `fullTheoremConditional`. The actual Kirchberg corner, its finite
amalgam presentation, the graph/channel coordinate equations and the actual
common projection must still be constructed. These are visible local
construction hypotheses, not approved external theorem parameters. The
abstract category's actual-KK interpretation remains an external obligation.
-/

noncomputable section
namespace Suzuki.ConditionalAssembly
open CategoryTheory Suzuki.ConditionalKK Suzuki.ConditionalKKTransport

universe u v w
variable {C : Type v} [Category.{w} C] [Preadditive C]
variable (object : Target.UnitalAlgebra.{u} → C) (scalar : C)
variable (unit : ∀ A : Target.UnitalAlgebra.{u}, scalar ⟶ object A)
variable {Q : ℕ → C} {X F L : C}
variable (coordinate : ∀ n, Q n ≅ X)
variable (bond : ∀ n, Q n ⟶ Q (n+1)) (stage : ∀ n, Q n ⟶ L)
variable (S : C → C) (M : AnalyticMilnorInput S Q bond stage) (R : Splitting F X)
variable (hb : ∀ n, bond n ≫ (coordinate (n+1)).hom = (coordinate n).hom ≫ R.f)
variable (hs : ∀ n, bond n ≫ stage (n+1) = stage n)
variable (A B : Target.UnitalAlgebra.{u})
variable (corner : object A ≅ L) (coefficient : F ≅ object B)

/-- The explicit composite: full-corner inclusion, inverse Milnor class,
then the coefficient model's equivalence to the target. -/
def finalIso : object A ≅ object B :=
  (corner.trans (limitIso coordinate bond stage S M R hb hs).symm).trans coefficient

variable (n : ℕ) (projection : scalar ⟶ Q n) (prescribed : scalar ⟶ F)
variable (hcorner : unit A ≫ corner.hom = projection ≫ stage n)
variable (hprojection : projection ≫ (coordinate n).hom = prescribed ≫ R.j)
variable (hprescribed : prescribed ≫ coefficient.hom = unit B)

include hcorner hprojection hprescribed in
/-- The unit calculation uses the proved inverse-stage restriction, not
an assumed unit-preserving final equivalence. -/
theorem finalIso_unit :
    unit A ≫ (finalIso object coordinate bond stage S M R hb hs A B corner coefficient).hom =
      unit B := by
  change unit A ≫ ((corner.hom ≫ (limitIso coordinate bond stage S M R hb hs).inv) ≫
    coefficient.hom) = unit B
  rw [← Category.assoc, ← Category.assoc, hcorner]
  rw [prescribed_class coordinate bond stage S M R hb hs n projection prescribed hprojection,
    hprescribed]

include M hb hs hcorner hprojection hprescribed in
/-- Final classification of a constructed common corner. This theorem does
not construct its local Kirchberg and presentation hypotheses, and therefore
does not itself discharge the manuscript's main construction. -/
theorem classifyConstructedCorner
    (classify : ConditionalClassification.ClassificationInput object scalar unit)
    (hA : Target.IsKirchberg A) (hB : Target.IsKirchberg B)
    (presentation : Target.HasFiniteAmalgam A) : Target.HasFiniteAmalgam B :=
  ConditionalClassification.conclude object scalar unit classify A B hA hB presentation
    (finalIso object coordinate bond stage S M R hb hs A B corner coefficient)
    (finalIso_unit object scalar unit coordinate bond stage S M R hb hs A B corner coefficient
      n projection prescribed hcorner hprojection hprescribed)

end Suzuki.ConditionalAssembly

import Suzuki.ActualUnitKK
import Suzuki.ConditionalMainConstruction
import Suzuki.ConditionalClassification
import Suzuki.CornerPureInfiniteness

/-! Actual full-corner KK and unit-preserving classification interfaces.
Morita equivalence and classification are universal published inputs. The unit
transport along the actual corner inclusion is proved pointwise. No target or
coefficient UCT is present. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Suzuki.ActualKKCornerClassification
open CategoryTheory CoefficientModelFromExtension ActualUnitKK
open scoped CStarAlgebra ComplexOrder
universe u v w
variable {K : Type v} [Category.{w} K] [Preadditive K]
variable (J : KKInterpretation.{u,v,w} (K := K))

/-- The distinguished unit is the class of the actual scalar unital map. -/
def unitClass (A : Target.UnitalAlgebra.{u}) (hA : TopologicalSpace.SeparableSpace A) :
    J.object ActualUnitKK.scalar ⟶ J.object (ofUnital A hA) :=
  J.map (projectionMap (ofUnital A hA) (1 : A) (IsStarProjection.one A))

def cornerTarget (A : Target.UnitalAlgebra.{u}) {p : A} (hp : IsStarProjection p) :
    Target.UnitalAlgebra.{u} := ⟨CommonCorner.Corner hp, inferInstance⟩

theorem cornerSeparable (A : Target.UnitalAlgebra.{u}) (hA : TopologicalSpace.SeparableSpace A)
    {p : A} (hp : IsStarProjection p) : TopologicalSpace.SeparableSpace (cornerTarget A hp) := by
  let : TopologicalSpace.SeparableSpace A := hA
  exact CornerFiniteness.corner_separable hp

/-- EXTERNAL P4: the actual inclusion of every full projection corner is a
KK equivalence. Meyer math/0702145v2, Sections 4.1--4.2 (stability/Morita);
Rosenberg--Schochet Duke 55 (1987), Theorem 1.11(5), in its nuclear scope, for stabilization; full-corner
Morita is the standard consequence described by Meyer.
The explicit full-projection predicate is norm-closed ideal fullness. Actual
KK interpretation and its agreement with this concrete corner remain external.
The input names no manuscript projection or constructed limit. -/
structure FullCornerKKInput : Prop where
  inclusion : ∀ (A : Target.UnitalAlgebra.{u})
    (hA : TopologicalSpace.SeparableSpace A), Target.HasCPApproximation A →
    ∀ (p : A) (hp : IsStarProjection p), CommonCorner.FullProjection p →
      IsIso (J.map (A := ofUnital (cornerTarget A hp) (cornerSeparable A hA hp))
        (B := ofUnital A hA) (CommonCorner.inclusion hp))

def cornerIso (M : FullCornerKKInput J) (A : Target.UnitalAlgebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) (hN : Target.HasCPApproximation A)
    {p : A} (hp : IsStarProjection p) (hfull : CommonCorner.FullProjection p) :
    J.object (ofUnital (cornerTarget A hp) (cornerSeparable A hA hp)) ≅ J.object (ofUnital A hA) := by
  letI := M.inclusion A hA hN p hp hfull
  exact asIso (J.map (A := ofUnital (cornerTarget A hp) (cornerSeparable A hA hp))
    (B := ofUnital A hA) (CommonCorner.inclusion hp))

omit [Preadditive K] in
/-- Unit transport is a literal equality of scalar star-map classes. -/
theorem unit_inclusion (A : Target.UnitalAlgebra.{u})
    (hA : TopologicalSpace.SeparableSpace A) {p : A} (hp : IsStarProjection p) :
    unitClass J (cornerTarget A hp) (cornerSeparable A hA hp) ≫
      J.map (A := ofUnital (cornerTarget A hp) (cornerSeparable A hA hp))
        (B := ofUnital A hA) (CommonCorner.inclusion hp) =
      J.map (projectionMap (ofUnital A hA) p hp) := by
  unfold unitClass
  rw [← J.map_comp]
  apply congrArg (fun f => J.map (A := ActualUnitKK.scalar) (B := ofUnital A hA) f)
  ext z
  change z.down • p = z.down • p
  rfl

/-- EXTERNAL P9: the exact unit-preserving Kirchberg classification statement.
Phillips funct-an/9506010v2, Corollary 4.2.2, p.42. Both algebras are separable,
nuclear, nonzero simple and purely infinite in Target's exact conventions.
The equivalence is a KK equivalence and the unit classes are the actual scalar
maps above. There is no UCT premise. Predicate/actual-KK correspondence is an
explicit external obligation, rather than a kernel-axiom assertion. -/
structure ClassificationInput : Prop where
  classify : ∀ (A B : Target.UnitalAlgebra.{u})
    (hA : Target.IsKirchberg A) (hB : Target.IsKirchberg B),
    ∀ ξ : J.object (ofUnital A hA.1) ≅ J.object (ofUnital B hB.1),
      unitClass J A hA.1 ≫ ξ.hom = unitClass J B hB.1 → Nonempty (A ≃⋆ₐ[ℂ] B)

omit [Preadditive K] in
/-- Final local assembly: its projection and KK-coordinate hypotheses are
construction obligations. They are not fields of either published input. -/
theorem classifyCorner (M : FullCornerKKInput J) (C : ClassificationInput J)
    (A B : Target.UnitalAlgebra.{u}) (hA : Target.IsKirchberg A) (hB : Target.IsKirchberg B)
    {p : A} (hp : IsStarProjection p) (hne : p ≠ 0)
    (presentation : Target.HasFiniteAmalgam (cornerTarget A hp))
    (ξ : J.object (ofUnital A hA.1) ≅ J.object (ofUnital B hB.1))
    (hunit : J.map (projectionMap (ofUnital A hA.1) p hp) ≫ ξ.hom = unitClass J B hB.1) :
    Target.HasFiniteAmalgam B := by
  have hc : Target.IsKirchberg (cornerTarget A hp) :=
    CornerPureInfiniteness.isKirchberg A hA hp hne
  let θ := (cornerIso J M A hA.1 hA.2.1 hp
    (SimpleFullness.full_of_nonzero hA.2.2.1.2 hne)).trans ξ
  have hu : unitClass J (cornerTarget A hp) hc.1 ≫ θ.hom = unitClass J B hB.1 := by
    change unitClass J (cornerTarget A hp) (cornerSeparable A hA.1 hp) ≫
      J.map (A := ofUnital (cornerTarget A hp) (cornerSeparable A hA.1 hp))
        (B := ofUnital A hA.1) (CommonCorner.inclusion hp) ≫ ξ.hom = _
    rw [← Category.assoc,unit_inclusion,hunit]
  obtain ⟨e⟩ := C.classify (cornerTarget A hp) B hc hB θ hu
  exact ConditionalClassification.hasFiniteAmalgam_of_equiv presentation e

end Suzuki.ActualKKCornerClassification

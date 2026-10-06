import Suzuki.SequentialCStarLimit
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Finiteness of the constructed injective limit

The argument uses two simultaneous stage approximations and the Neumann series.
Stage finiteness is currently expressed by the ring-theoretic one-sided inverse
condition. RFD stages satisfy this stronger condition by the preceding module.
-/

noncomputable section

namespace Suzuki.LimitFiniteness

open InductiveAmalgam SequentialCStarLimit

universe u

variable {I : Type*} (A : I → Type*) [∀ i, CStarAlgebra (A i)]
variable {B : Type*} [CStarAlgebra B]

/-- A dense family of pairs from complete finite subalgebras forces finiteness.
The supplied maps are actual isometric embeddings of C⋆-algebras. -/
theorem of_dense_pairs (e : ∀ i, A i →⋆ₐ[ℂ] B)
    (he : ∀ i, Function.Injective (e i))
    (hd : DenseRange (fun p : Σ i, A i × A i => (e p.1 p.2.1, e p.1 p.2.2)))
    [∀ i, IsDedekindFiniteMonoid (A i)] : IsDedekindFiniteMonoid B :=
    ⟨fun {x y} hxy => by
  let U : Set (B × B) := {p | ‖1 - p.1 * p.2‖ < 1 ∧ ‖1 - x * p.2‖ < 1}
  have hU : IsOpen U := by
    have h₁ : Continuous (fun p : B × B => ‖1 - p.1 * p.2‖) := by fun_prop
    have h₂ : Continuous (fun p : B × B => ‖1 - x * p.2‖) := by fun_prop
    exact (isOpen_lt h₁ continuous_const).inter (isOpen_lt h₂ continuous_const)
  have hne : U.Nonempty := ⟨(x, y), by simp [U, hxy]⟩
  obtain ⟨⟨n, a, b⟩, hz⟩ := hd.exists_mem_open hU hne
  change ‖1 - e n a * e n b‖ < 1 ∧ ‖1 - x * e n b‖ < 1 at hz
  have habnorm : ‖1 - a * b‖ < 1 := by
    rw [← NonUnitalStarAlgHom.norm_map (e n) (he n) (1 - a * b),
      map_sub, map_one, map_mul]
    exact hz.1
  have hab : IsUnit (a * b) := by
    simpa only [Units.val_oneSub, sub_sub_cancel] using
      (Units.oneSub (1 - a * b) habnorm).isUnit
  obtain ⟨c, hc⟩ := hab.exists_left_inv
  have hb : IsUnit b := IsUnit.of_mul_eq_one_right (c * a) (by
    simpa only [mul_assoc] using hc)
  have hxb : IsUnit (x * e n b) := by
    simpa only [Units.val_oneSub, sub_sub_cancel] using
      (Units.oneSub (1 - x * e n b) hz.2).isUnit
  obtain ⟨v, hv⟩ := hb.map (e n)
  have hx : IsUnit x := (Units.isUnit_mul_units x v).mp (by simpa only [hv] using hxb)
  obtain ⟨c, hc⟩ := hx.exists_left_inv
  rw [← left_inv_eq_right_inv hc hxy]
  exact hc⟩

variable (S : System.{u}) [Fact (∀ n, Function.Injective (S.step n))]

/-- Pairs of limit elements can be simultaneously approximated at one stage. -/
theorem dense_stage_pairs :
    DenseRange (fun p : Σ n, S.obj n × S.obj n => (stage S p.1 p.2.1, stage S p.1 p.2.2)) := by
  have hd := (UniformSpace.Completion.denseRange_coe
    (α := DirectedCStarLimit.Algebraic S.obj (transition S))).prodMap
      (UniformSpace.Completion.denseRange_coe
        (α := DirectedCStarLimit.Algebraic S.obj (transition S)))
  apply hd.mono
  rintro z ⟨⟨a, b⟩, rfl⟩
  obtain ⟨n, a, b, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (transition S) a b
  exact ⟨⟨n, a, b⟩, rfl⟩

/-- The constructed injective limit is finite if every complete stage is finite. -/
theorem dedekindFinite [∀ n, IsDedekindFiniteMonoid (S.obj n)] :
    IsDedekindFiniteMonoid (Limit S) :=
  of_dense_pairs S.obj (stage S) (stage_injective S) (dense_stage_pairs S)

end Suzuki.LimitFiniteness

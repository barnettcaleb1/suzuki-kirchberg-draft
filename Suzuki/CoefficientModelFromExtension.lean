import Suzuki.CoefficientModelConditional
import Suzuki.ConditionalKK
import Suzuki.Target

/-!
# The coefficient model derived from the original published extension

The conclusion of the coefficient-model lemma is proved here from universal
published inputs. It is not a field of any input. The algebra is literally
`Cone theta`; its forward class is literally the quotient-induced path map
followed by Bott. All algebras have genuine Cstar norms and all nuclearity
statements use CPC finite-matrix approximation, including the nonunital ones.

External source contracts (not global axioms):
* Dadarlat, January 2002 author version, Lemma 2.4 pp.2--3 and the construction
  of (11), p.8. Only the original extension is supplied. The later assumption
  K_*(B)=0, and every UCT assumption, are absent.
* Blackadar, Operator Algebras, author revision 8 February 2017, IV.3.1.1--6,
  IV.3.2.4--5: nuclearity permanence/CPAP and Choi--Effros lifting. Matrix
  direct sums are injective limits of finite sums; suspension is the spatial
  tensor with C_0(0,1); external unitization is extension by the scalars.
* Rosenberg--Schochet, Duke 55 (1987), Theorem 1.11; Meyer, Categorical
  aspects of bivariant K-theory, arXiv:math/0702145v2, Section 4.2,
  Definition 55 and Theorem 56: KK functoriality, semisplit extension/cone
  triangles and Bott. The generic map-level cone correspondence is explicitly
  external: it refers to the PARTICULAR pointwise-quotient map below, for
  EVERY exact semisplit extension, not a newly constructed coefficient model.

The checked source excerpts and field-by-field correspondence/residual access
limitations are recorded in the accompanying worker report. An instance of
these interfaces is not constructed here; in particular a kernel axiom audit
does not certify their interpretation as actual Kasparov theory.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Suzuki.CoefficientModelFromExtension
open CategoryTheory
open scoped CStarAlgebra ComplexOrder
open CoefficientConeModel CoefficientModelConditional

universe u v w

/-- Actual separable, possibly nonunital, complex Cstar algebras. -/
structure Algebra where
  Carrier : Type u
  cstar : NonUnitalCStarAlgebra Carrier
  separable : TopologicalSpace.SeparableSpace Carrier

attribute [instance] Algebra.cstar Algebra.separable
instance : CoeSort Algebra.{u} (Type u) := ⟨Algebra.Carrier⟩
instance (A : Algebra) : PartialOrder A := CStarAlgebra.spectralOrder A
instance (A : Algebra) : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- The same finite-matrix CPC approximation convention as `Target`, extended
to nonunital algebras. Both maps are contractive at the Cstar norm. -/
def Nuclear (A : Algebra) : Prop :=
  ∀ (s : Finset A) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (_ : 0 < n)
      (φ : A →CP CStarMatrix (Fin n) (Fin n) ℂ)
      (ψ : CStarMatrix (Fin n) (Fin n) ℂ →CP A),
      (∀ a, ‖φ a‖ ≤ ‖a‖) ∧ (∀ m, ‖ψ m‖ ≤ ‖m‖) ∧
      ∀ a ∈ s, ‖ψ (φ a) - a‖ < ε

def ofUnital (B : Target.UnitalAlgebra.{u})
    (hB : TopologicalSpace.SeparableSpace B) : Algebra.{u} :=
  ⟨B, inferInstance, hB⟩

theorem nuclear_ofUnital_iff (B : Target.UnitalAlgebra.{u})
    (hB : TopologicalSpace.SeparableSpace B) :
    Nuclear (ofUnital B hB) ↔ Target.HasCPApproximation B := Iff.rfl

def suspension (A : Algebra.{u}) : Algebra.{u} :=
  ⟨Suspension A, inferInstance, inferInstance⟩

def cone {I H : Algebra.{u}} (θ : I →⋆ₙₐ[ℂ] H) : Algebra.{u} :=
  ⟨Cone θ, inferInstance, inferInstance⟩

def unitization (A : Algebra.{u}) : Algebra.{u} :=
  ⟨Unitization ℂ A, inferInstance, inferInstance⟩

def unitalUnitization (A : Algebra.{u}) : Target.UnitalAlgebra.{u} :=
  ⟨Unitization ℂ A, inferInstance⟩

/-- Exactness of the actual maps, with the actual two-sided ideal kernel. -/
structure ExactExtension {I H Q : Algebra.{u}}
    (θ : I →⋆ₙₐ[ℂ] H) (q : H →⋆ₙₐ[ℂ] Q) : Prop where
  injective : Function.Injective θ
  range_kernel : Set.range θ = (TwoSidedIdeal.ker q : Set H)
  surjective : Function.Surjective q

theorem ExactExtension.zero {I H Q : Algebra.{u}}
    {θ : I →⋆ₙₐ[ℂ] H} {q : H →⋆ₙₐ[ℂ] Q} (e : ExactExtension θ q) (x : I) :
    q (θ x) = 0 := by
  have hx : θ x ∈ (TwoSidedIdeal.ker q : Set H) := by
    rw [← e.range_kernel]
    exact ⟨x, rfl⟩
  exact (TwoSidedIdeal.mem_ker q).mp hx

/-- A semisplitting means an actual completely positive contractive right
inverse, not merely a linear or set-theoretic section. -/
structure CPCSection {H Q : Algebra.{u}} (q : H →⋆ₙₐ[ℂ] Q) where
  sectionMap : Q →CP H
  right_inverse : Function.RightInverse sectionMap q
  contractive : ∀ x, ‖sectionMap x‖ ≤ ‖x‖

/-- Concrete coordinates specifying precisely a countable c0 direct sum of
nonzero finite matrix algebras. The image is ALL norm-null sequences and the
norm is their supremum; no opaque AF/nuclear predicate is substituted. -/
structure MatrixSumCoordinates (I : Algebra.{u}) where
  size : ℕ → ℕ
  positive : ∀ n, 0 < size n
  coordinate : ∀ n, I →⋆ₙₐ[ℂ] CStarMatrix (Fin (size n)) (Fin (size n)) ℂ
  separates : Function.Injective (fun x : I => fun n => coordinate n x)
  null : ∀ x : I, ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n, N ≤ n → ‖coordinate n x‖ < ε
  onto : ∀ y : (n : ℕ) → CStarMatrix (Fin (size n)) (Fin (size n)) ℂ,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ‖y n‖ < ε) →
    ∃ x : I, ∀ n, coordinate n x = y n
  norm_eq : ∀ x : I, ‖x‖ = ⨆ n, ‖coordinate n x‖

/-- EXTERNAL P0, universally quantified standard nuclearity permanence.
Sources: Blackadar 2017 IV.3.1 introductory permanence paragraph and
IV.3.1.1/3/5/6. `matrix_sum` uses the concrete c0 coordinates;
`suspension` includes the endpoint-path versus C_0(0,1) spatial-tensor
identification; `extension` includes the standard quotient identification
for the injective/surjective exact maps. No new-model conclusion is a field. -/
structure NuclearityInput : Prop where
  matrix_sum : ∀ I : Algebra.{u}, MatrixSumCoordinates I → Nuclear I
  suspension : ∀ A : Algebra.{u}, Nuclear A → Nuclear (suspension A)
  extension : ∀ (I H Q : Algebra.{u}) (θ : I →⋆ₙₐ[ℂ] H) (q : H →⋆ₙₐ[ℂ] Q),
    ExactExtension θ q → Nuclear I → Nuclear Q → Nuclear H
  unitization : ∀ A : Algebra.{u}, Nuclear A → Nuclear (unitization A)

/-- EXTERNAL P0, Choi--Effros applied to the identity of a separable nuclear
quotient: Blackadar 2017 IV.3.2.4--5, originally Choi--Effros, Ann. Math.
104 (1976), 585--609, Theorem 3.10. Surjective star maps identify their target
with the Cstar quotient by the closed kernel; that identification is included
in the standard theorem's correspondence to this formulation. -/
structure LiftingInput : Prop where
  lift : ∀ (H Q : Algebra.{u}) (q : H →⋆ₙₐ[ℂ] Q),
    Function.Surjective q → Nuclear Q → Nonempty (CPCSection q)

/-- Original Dadarlat extension data ONLY. Nuclearity of the middle algebra,
semisplitting, the new cone and any KK equivalence are deliberately derived.
The separability fields are in the actual bundled algebras. -/
structure OriginalExtension (B : Algebra.{u}) where
  ideal : Algebra.{u}
  middle : Algebra.{u}
  ideal_coordinates : MatrixSumCoordinates ideal
  inclusion : ideal →⋆ₙₐ[ℂ] middle
  quotient : middle →⋆ₙₐ[ℂ] suspension B
  exact : ExactExtension inclusion quotient
  middle_rfd : UnitizationRFD.IsRFD middle

/-- EXTERNAL P5. For every separable nuclear B, the pullback for the external
unitization of SB, restricted to SB, gives (11). Dadarlat January 2002,
Lemma 2.4 and proof of Theorem 1.2. It has no K-theory, UCT, coefficient-model
or cone-equivalence premise or conclusion. Restriction/model correspondence
to the concrete coordinates is an explicit external instantiation obligation. -/
structure DadarlatInput : Prop where
  original_extension : ∀ B : Algebra.{u}, Nuclear B → Nonempty (OriginalExtension B)

variable {K : Type v} [Category.{w} K]

/-- EXTERNAL P3 actual-KK interpretation. `object A` denotes A in KK and
`map f` the degree-zero class of the actual star map f. These correspondences
must be supplied externally; the functor laws are explicit, not postulated
as global axioms. No cycles are rebuilt here. -/
structure KKInterpretation where
  object : Algebra.{u} → K
  map : ∀ {A B : Algebra.{u}}, (A →⋆ₙₐ[ℂ] B) → (object A ⟶ object B)
  map_id : ∀ A : Algebra.{u}, map (NonUnitalStarAlgHom.id ℂ A) = 𝟙 (object A)
  map_comp : ∀ {A B C : Algebra.{u}} (f : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] C),
    map (g.comp f) = map f ≫ map g

/-- EXTERNAL P4, the UNIVERSAL semisplit inclusion-cone theorem and Bott.
For each exact semisplit I→H→Q, the specified map is (f,x)↦q∘f into S(Q).
Meyer 2007 Section 4.2 supplies extension/cone triangles; identification of
this explicit map with the standard rotated triangle comparison remains the
named external map-level correspondence. Bott is RS 1987 Theorem 1.11(3).
The compact interval endpoint model must correspond to the standard S functor.
This interface does not mention Dadarlat or a coefficient-model conclusion. -/
structure ConeBottInput (J : KKInterpretation.{u, v, w} (K := K)) where
  cone_quotient_isIso : ∀ (I H Q : Algebra.{u})
    (θ : I →⋆ₙₐ[ℂ] H) (q : H →⋆ₙₐ[ℂ] Q) (e : ExactExtension θ q),
    CPCSection q → IsIso (J.map (A := cone θ) (B := suspension Q)
      (quotientSuspensionMap θ q e.zero))
  bott : ∀ B : Algebra.{u}, J.object (suspension (suspension B)) ≅ J.object B

namespace OriginalExtension
variable {B : Algebra.{u}} (d : OriginalExtension B)

/-- The coefficient algebra is the PREVIOUSLY CONSTRUCTED actual cone. -/
def coefficient : Algebra.{u} := cone d.inclusion

theorem ideal_nuclear (N : NuclearityInput.{u}) : Nuclear d.ideal :=
  N.matrix_sum d.ideal d.ideal_coordinates

theorem middle_nuclear (N : NuclearityInput.{u}) (hB : Nuclear B) : Nuclear d.middle :=
  N.extension _ _ _ d.inclusion d.quotient d.exact (d.ideal_nuclear N)
    (N.suspension B hB)

/-- Exactness for SH→Cone(theta)→I is proved for the actual maps. -/
theorem cone_exact : ExactExtension
    (I := suspension d.middle) (H := d.coefficient) (Q := d.ideal)
    (CoefficientModelConditional.inclusion d.inclusion) (projection d.inclusion) :=
  ⟨inclusion_injective d.inclusion, inclusion_range_eq_ideal d.inclusion,
    projection_surjective d.inclusion⟩

/-- Nuclearity is a double application of generic extension permanence,
not an assumed property of the new coefficient algebra. -/
theorem coefficient_nuclear (N : NuclearityInput.{u}) (hB : Nuclear B) :
    Nuclear d.coefficient :=
  N.extension _ _ _ _ _ d.cone_exact
    (N.suspension _ (d.middle_nuclear N hB)) (d.ideal_nuclear N)

theorem coefficient_rfd : UnitizationRFD.IsRFD d.coefficient :=
  CoefficientConeModel.rfd d.inclusion d.exact.injective d.middle_rfd

/-- Original semisplitting follows from the actual nuclear quotient. -/
def originalSection (N : NuclearityInput.{u}) (L : LiftingInput.{u})
    (hB : Nuclear B) : CPCSection d.quotient :=
  Classical.choice (L.lift _ _ d.quotient d.exact.surjective (N.suspension B hB))

/-- The map into SS(B), with literal pointwise quotient formula. -/
def comparison : d.coefficient →⋆ₙₐ[ℂ] suspension (suspension B) :=
  quotientSuspensionMap d.inclusion d.quotient d.exact.zero

@[simp] theorem comparison_apply (a : d.coefficient) (t : Interval) :
    (d.comparison a).val t = d.quotient (a.val.1 t) := rfl

theorem comparison_surjective (N : NuclearityInput.{u}) (L : LiftingInput.{u})
    (hB : Nuclear B) : Function.Surjective d.comparison :=
  quotientSuspensionMap_surjective_of_cpc d.inclusion d.quotient d.exact.zero
    (d.originalSection N L hB).sectionMap (d.originalSection N L hB).right_inverse
    (d.originalSection N L hB).contractive

variable (J : KKInterpretation.{u, v, w} (K := K)) (T : ConeBottInput J)

/-- The chosen invertible class is the class of the actual comparison
followed by Bott; its inverse is supplied by generic categorical isomorphism. -/
def equivalence (N : NuclearityInput.{u}) (L : LiftingInput.{u}) (hB : Nuclear B) :
    J.object d.coefficient ≅ J.object B := by
  letI : IsIso (J.map (A := d.coefficient) (B := suspension (suspension B))
    d.comparison) := T.cone_quotient_isIso _ _ _
    d.inclusion d.quotient d.exact (d.originalSection N L hB)
  exact (asIso (J.map (A := d.coefficient) (B := suspension (suspension B))
    d.comparison)) ≪≫ T.bott B

theorem equivalence_hom (N : NuclearityInput.{u}) (L : LiftingInput.{u})
    (hB : Nuclear B) :
    (d.equivalence J T N L hB).hom =
      J.map (A := d.coefficient) (B := suspension (suspension B)) d.comparison ≫
        (T.bott B).hom := rfl

theorem unitization_nuclear (N : NuclearityInput.{u}) (hB : Nuclear B) :
    Nuclear (unitization d.coefficient) := N.unitization _ (d.coefficient_nuclear N hB)

theorem unitization_target_nuclear (N : NuclearityInput.{u}) (hB : Nuclear B) :
    Target.HasCPApproximation (unitalUnitization d.coefficient) :=
  d.unitization_nuclear N hB

theorem unitization_rfd :
    ResidualRepresentations.IsRFD (Unitization ℂ d.coefficient) :=
  UnitizationRFD.unitization_rfd _ d.coefficient_rfd

theorem separating_tails :
    ∃ σ : ℕ → ResidualRepresentations.Representation (Unitization ℂ d.coefficient),
      ResidualRepresentations.SeparatingTails (Unitization ℂ d.coefficient) σ :=
  UnitizationRFD.exists_separating_tails _ d.coefficient_rfd

theorem unitization_stablyFinite : StableFiniteness.IsStablyFinite
    (Unitization ℂ d.coefficient) := ResidualRepresentations.stablyFinite d.unitization_rfd

end OriginalExtension

/-- DERIVED coefficient-model lemma, in every universe u. The only inputs
are universal established-theory interfaces; no coefficient model, new cone
equivalence, K-group vanishing or target/coefficient UCT is assumed. -/
theorem coefficient_model (N : NuclearityInput.{u}) (L : LiftingInput.{u})
    (D : DadarlatInput.{u}) (J : KKInterpretation.{u, v, w} (K := K))
    (T : ConeBottInput J) (B : Algebra.{u}) (hB : Nuclear B) :
    ∃ F : Algebra.{u}, Nuclear F ∧ UnitizationRFD.IsRFD F ∧
      Nonempty (J.object F ≅ J.object B) := by
  obtain ⟨d⟩ := D.original_extension B hB
  exact ⟨d.coefficient, d.coefficient_nuclear N hB, d.coefficient_rfd,
    ⟨d.equivalence J T N L hB⟩⟩

/-- The actual external-unitization inclusion. -/
def unitizationInclusion (A : Algebra.{u}) : A →⋆ₙₐ[ℂ] unitization A :=
  Unitization.inrNonUnitalStarAlgHom ℂ A

/-- The actual scalar quotient, even when A happened already to be unital. -/
def scalarQuotient (A : Algebra.{u}) : Unitization ℂ A →⋆ₐ[ℂ] ℂ :=
  UnitizationRFD.augmentation A

/-- The actual scalar section of the EXTERNAL unitization. -/
def scalarSection (A : Algebra.{u}) : ℂ →⋆ₐ[ℂ] Unitization ℂ A :=
  StarAlgHom.ofId ℂ (Unitization ℂ A)

@[simp] theorem scalarQuotient_section (A : Algebra.{u}) (z : ℂ) :
    scalarQuotient A (scalarSection A z) = z := rfl

theorem unitizationInclusion_injective (A : Algebra.{u}) :
    Function.Injective (unitizationInclusion A) := Unitization.inr_injective

/-- Literal equality with the closed two-sided ideal kernel. -/
theorem unitizationInclusion_range (A : Algebra.{u}) :
    Set.range (unitizationInclusion A) = (TwoSidedIdeal.ker (scalarQuotient A) :
      Set (Unitization ℂ A)) := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact (TwoSidedIdeal.mem_ker _).mpr rfl
  · intro ha
    have hz : a.fst = 0 := (TwoSidedIdeal.mem_ker _).mp ha
    exact ⟨a.snd, Unitization.ext hz.symm rfl⟩

theorem scalarQuotient_surjective (A : Algebra.{u}) :
    Function.Surjective (scalarQuotient A) :=
  fun z => ⟨scalarSection A z, rfl⟩

/-- Composing the two ACTUAL scalar maps gives an endomorphism in the same
universe as A. This avoids restricting the theorem to Type 0 merely to make
the scalar object an object of the chosen abstract category. Under the actual
KK interpretation its class is [epsilon];[eta], with that order. -/
def scalarRetraction (A : Algebra.{u}) : unitization A →⋆ₙₐ[ℂ] unitization A :=
  ((scalarSection A).comp (scalarQuotient A)).toNonUnitalStarAlgHom

@[simp] theorem scalarRetraction_apply (A : Algebra.{u}) (a : Unitization ℂ A) :
    scalarRetraction A a = scalarSection A (scalarQuotient A a) := rfl

theorem scalarRetraction_idempotent (A : Algebra.{u}) :
    (scalarRetraction A).comp (scalarRetraction A) = scalarRetraction A := by
  ext a
  exact congrArg (scalarSection A) (scalarQuotient_section A (scalarQuotient A a))

section SplitUnitization
variable [Preadditive K]

/-- EXTERNAL P4, split exactness, specialized UNIVERSALLY to the actual
external-unitization sequence whose kernel and splitting were proved above.
RS 1987 Theorem 1.11(1),(4), in the nuclear scope of that source. The second
formula is 1_E minus the class of the ACTUAL composite eta∘epsilon. Generic
split exactness, not an existence assertion about the coefficient model,
supplies r. Actual-KK interpretation and product order remain external. -/
structure SplitUnitizationInput (J : KKInterpretation.{u, v, w} (K := K)) : Prop where
  split : ∀ A : Algebra.{u}, Nuclear A →
    ∃ r : J.object (unitization A) ⟶ J.object A,
      J.map (unitizationInclusion A) ≫ r = 𝟙 (J.object A) ∧
      r ≫ J.map (unitizationInclusion A) =
        𝟙 (J.object (unitization A)) - J.map (scalarRetraction A)

variable (J : KKInterpretation.{u, v, w} (K := K)) (S : SplitUnitizationInput J)

/-- Choose the generic split-exact retraction for an actual nuclear algebra. -/
def unitizationRetraction (A : Algebra.{u}) (hA : Nuclear A) :
    J.object (unitization A) ⟶ J.object A := Classical.choose (S.split A hA)

theorem inclusion_retraction (A : Algebra.{u}) (hA : Nuclear A) :
    J.map (unitizationInclusion A) ≫ unitizationRetraction J S A hA =
      𝟙 (J.object A) := (Classical.choose_spec (S.split A hA)).1

theorem retraction_inclusion (A : Algebra.{u}) (hA : Nuclear A) :
    unitizationRetraction J S A hA ≫ J.map (unitizationInclusion A) =
      𝟙 (J.object (unitization A)) - J.map (scalarRetraction A) :=
  (Classical.choose_spec (S.split A hA)).2

/-- The actual coefficient inclusion supplies the checked abstract splitting
used by the idempotent-limit calculation in `ConditionalKK`. -/
def unitizationSplitting (A : Algebra.{u}) (hA : Nuclear A) :
    ConditionalKK.Splitting (J.object A) (J.object (unitization A)) where
  j := J.map (unitizationInclusion A)
  s := unitizationRetraction J S A hA
  retract := inclusion_retraction J S A hA

theorem unitizationSplitting_f (A : Algebra.{u}) (hA : Nuclear A) :
    (unitizationSplitting J S A hA).f =
      𝟙 (J.object (unitization A)) - J.map (scalarRetraction A) :=
  retraction_inclusion J S A hA

theorem reduced_idempotent (A : Algebra.{u}) :
    (𝟙 (J.object (unitization A)) - J.map (scalarRetraction A)) ≫
      (𝟙 (J.object (unitization A)) - J.map (scalarRetraction A)) =
        𝟙 (J.object (unitization A)) - J.map (scalarRetraction A) := by
  have hp : J.map (scalarRetraction A) ≫ J.map (scalarRetraction A) =
      J.map (scalarRetraction A) := by
    rw [← J.map_comp, scalarRetraction_idempotent]
  simp only [CategoryTheory.Preadditive.sub_comp, CategoryTheory.Preadditive.comp_sub,
    Category.id_comp, Category.comp_id, hp]
  abel

end SplitUnitization

end Suzuki.CoefficientModelFromExtension

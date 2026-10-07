import Suzuki.InitialGraphPresentation
import Suzuki.OrthogonalFiniteDiagrams
import Mathlib.Data.Matrix.Composition
import Mathlib.Algebra.Algebra.Pi

/-!
# A constructed recursive three-channel finite graph system

The vertex set is `Fin 2`; channels 0, 1, 2 have integer cokernel maps
+1, -1, 0 and zero kernel maps. Each presentation is an actual nonnegative
unimodular left change of the initial all-ones presentation. At each step the
noise channel has source sizes multiplied by the given positive integer q.
The common target dimensions are exactly `(T₊ + T₋ + q T₀)(k,l)`.

This is an internal construction using positive lifting, not an input asserting
existence of the recursive family. The finite maps are actual complex matrix
star homomorphisms with literal squares. No graph K-theory, tensor product,
KK interpretation, or analytic limit claim is made in this file.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Suzuki.RecursiveGraphSequence
open Matrix PositiveLifting FiniteDiagram MultiplicityEmbeddings OrthogonalFiniteDiagrams
open scoped CStarAlgebra ComplexOrder

abbrev Vertex := Fin 2
abbrev Channel := Fin 3
abbrev IntegerMatrix := Matrix Vertex Vertex ℤ
abbrev CommonMatrix := Matrix (Vertex ⊕ Vertex) (Vertex ⊕ Vertex) ℕ

/-- Channel order is positive, negative, noise. -/
def sign : Channel → ℤ := ![1,-1,0]
def scale (q : ℕ) : Channel → ℕ := ![1,1,q]

theorem scale_pos (q : ℕ) (hq : 0 < q) (c : Channel) : 0 < scale q c := by
  fin_cases c <;> simp [scale, hq]

/-- All data retained at a finite stage, including the actual presentation
change and strictly positive matrix-block dimensions. -/
structure Stage where
  U : IntegerMatrix
  unit : IsUnit U
  determinant : U.det = 1
  nonnegative : ∀ i j, 0 ≤ U i j
  positive : Positive (U * InitialGraphPresentation.B)
  k : Vertex → ℕ
  l : Vertex → ℕ
  k_pos : ∀ i, 0 < k i
  l_pos : ∀ i, 0 < l i

namespace Stage
abbrev B (P : Stage) : IntegerMatrix := P.U * InitialGraphPresentation.B
abbrev A (P : Stage) : Matrix Vertex Vertex ℕ := natMatrix (1 + P.B)
abbrev cokernel (P : Stage) : Cokernel P.B ≃ₗ[ℤ] ℤ :=
  InitialGraphPresentation.transportedCokernel P.U P.unit
abbrev kernel (P : Stage) : Kernel P.B ≃ₗ[ℤ] ℤ :=
  InitialGraphPresentation.transportedKernel P.U P.unit
abbrev scaledK (P : Stage) (q : ℕ) : Channel → Vertex → ℕ :=
  fun c i => scale q c * P.k i
abbrev scaledL (P : Stage) (q : ℕ) : Channel → Vertex → ℕ :=
  fun c i => scale q c * P.l i

def initial (k l : Vertex → ℕ) (hk : ∀ i, 0 < k i) (hl : ∀ i, 0 < l i) : Stage where
  U := 1
  unit := isUnit_one
  determinant := Matrix.det_one
  nonnegative := identity_nonnegative
  positive := by simpa using InitialGraphPresentation.positive
  k := k
  l := l
  k_pos := hk
  l_pos := hl

@[simp] theorem initial_B (k l : Vertex → ℕ) (hk : ∀ i, 0 < k i) (hl : ∀ i, 0 < l i) :
    (initial k l hk hl).B = InitialGraphPresentation.B := one_mul _

/-- The prescribed map goes to the fixed initial presentation, before the
simultaneous theorem makes the new target change of coordinates. -/
def prescribed (P : Stage) (c : Channel) :
    Cokernel P.B →ₗ[ℤ] Cokernel InitialGraphPresentation.B :=
  InitialGraphPresentation.cokernelEquiv.symm.toLinearMap.comp
    ((sign c • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).comp P.cokernel.toLinearMap)

@[simp] theorem prescribed_coordinate (P : Stage) (c : Channel) (x : Cokernel P.B) :
    InitialGraphPresentation.cokernelEquiv (P.prescribed c x) = sign c * P.cokernel x := by
  simp [prescribed]
end Stage

section CertifiedAggregation
variable {C n m : Type*} [Fintype C] [Fintype n] [Fintype m]
  [DecidableEq C] [DecidableEq n] [DecidableEq m]

/-- The specific factor-stack map, retaining its copy-and-reindex definition
instead of choosing an arbitrary map satisfying the same square. -/
def canonicalFactor (w : C → n → ℕ) (D : n → ℕ) (hD : total w = D)
    (H : Matrix m n ℕ) (d : C → m → ℕ) (hd : ∀ c, targetSize (w c) H = d c)
    (f : m → ℕ) (hf : targetSize D H = f) : Family d →⋆ₐ[ℂ] Blocks f := by
  subst D
  have hd' : (fun c => targetSize (w c) H) = d := funext hd
  subst d
  subst f
  exact factorStack w H

omit [DecidableEq n] [DecidableEq m] in
theorem canonicalFactor_isometry (w : C → n → ℕ) (D : n → ℕ) (hD : total w = D)
    (H : Matrix m n ℕ) (d : C → m → ℕ) (hd : ∀ c, targetSize (w c) H = d c)
    (f : m → ℕ) (hf : targetSize D H = f) :
    Isometry (canonicalFactor w D hD H d hd f hf) := by
  subst D
  have hd' : (fun c => targetSize (w c) H) = d := funext hd
  subst d
  subst f
  exact NonUnitalStarAlgHom.isometry _ (factorStack_injective w H)

omit [DecidableEq m] in
theorem canonicalFactor_square (w : C → n → ℕ) (D : n → ℕ) (hD : total w = D)
    (H : Matrix m n ℕ) (d : C → m → ℕ) (hd : ∀ c, targetSize (w c) H = d c)
    (f : m → ℕ) (hf : targetSize D H = f) (c : C) (a : Blocks (w c)) :
    channel (fun c => Blocks (d c)) (canonicalFactor w D hD H d hd f hf) c
      (intoDimensions (w c) H (d c) (hd c) a) =
    intoDimensions D H f hf (channel (fun c => Blocks (w c)) (stackInto w D hD) c a) := by
  subst D
  have hd' : (fun c => targetSize (w c) H) = d := funext hd
  subst d
  subst f
  exact channel_square w H c a

def canonicalFirst (k l : C → m → ℕ) :
    Family (fun c => k c + l c) →⋆ₐ[ℂ] Blocks (total k + total l) :=
  canonicalFactor (commonWeights k l) _ (total_commonWeights k l)
    firstMultiplicity _ (fun c => first_targetSize (k c) (l c)) _
    (first_targetSize (total k) (total l))

def canonicalSecond (k l : C → m → ℕ) (A : Matrix m m ℕ) :
    Family (fun c => k c + A *ᵥ l c) →⋆ₐ[ℂ] Blocks (total k + A *ᵥ total l) :=
  canonicalFactor (commonWeights k l) _ (total_commonWeights k l)
    (secondMultiplicity A) _ (fun c => second_targetSize A (k c) (l c)) _
    (second_targetSize A (total k) (total l))

/-- Canonical aggregation retains exact formulas for its actual maps. In
particular the factor maps are the given S/R-multiplicity Realizations followed
by the named block-stack embeddings. -/
def certifiedAggregate (A : Matrix n n ℕ) (A' : Matrix m m ℕ)
    (k l : C → n → ℕ) (T : C → Matrix (m ⊕ m) (n ⊕ n) ℕ)
    (S R : C → Matrix m n ℕ)
    (D : ∀ c, Realization A A' (T c) (S c) (R c) (k c) (l c)) : Aggregate A A' k l T := by
  let K := channelLeft k l T
  let L := channelRight k l T
  let F₀ := canonicalFirst K L
  let F₁ := canonicalSecond K L A'
  have hi₀ : Isometry F₀ := canonicalFactor_isometry _ _ _ _ _ _ _ _
  have hi₁ : Isometry F₁ := canonicalFactor_isometry _ _ _ _ _ _ _ _
  have hs₀ := fun c => canonicalFactor_square (commonWeights K L) _ (total_commonWeights K L)
    firstMultiplicity _ (fun c => first_targetSize (K c) (L c)) _
    (first_targetSize (total K) (total L)) c
  have hs₁ := fun c => canonicalFactor_square (commonWeights K L) _ (total_commonWeights K L)
    (secondMultiplicity A') _ (fun c => second_targetSize A' (K c) (L c)) _
    (second_targetSize A' (total K) (total L)) c
  let Q := commonAggregate K L
  let γ := fun c => (channel (fun c => Blocks (commonWeights K L c)) Q c).comp
    (commonMap (k c) (l c) (T c)).toNonUnitalStarAlgHom
  let β₀ := fun c => (channel (fun c => Blocks (K c + L c)) F₀ c).comp
    (D c).left.toNonUnitalStarAlgHom
  let β₁ := fun c => (channel (fun c => Blocks (K c + A' *ᵥ L c)) F₁ c).comp
    (D c).right.toNonUnitalStarAlgHom
  have hγ (c : C) : γ c 1 = channel (fun c => Blocks (commonWeights K L c)) Q c 1 := by
    change channel _ Q c (commonMap (k c) (l c) (T c) 1) = _
    rw [map_one]
  refine ⟨γ,β₀,β₁,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro c
    exact NonUnitalStarAlgHom.isometry _ ((channel_injective _ Q
      (stackInto_injective _ _ _) c).comp (D c).common_isometry.injective)
  · intro c
    exact NonUnitalStarAlgHom.isometry _ ((channel_injective _ F₀ hi₀.injective c).comp
      (D c).left_isometry.injective)
  · intro c
    exact NonUnitalStarAlgHom.isometry _ ((channel_injective _ F₁ hi₁.injective c).comp
      (D c).right_isometry.injective)
  · intro c; rw [hγ]; exact channel_unit_projection _ Q c
  · intro c d h; rw [hγ,hγ]; exact channel_orthogonal _ Q c d h
  · change ∑ c, γ c 1 = 1
    calc
      ∑ c, γ c 1 = ∑ c, channel (fun c => Blocks (commonWeights K L c)) Q c 1 :=
        Finset.sum_congr rfl (fun c _ => hγ c)
      _ = 1 := channel_unit_sum _ Q
  · intro c i hi
    rw [hγ]
    exact stackInto_channel_block_nonzero _ _ _ c i hi
  · intro c a
    change channel _ F₀ c ((D c).left (firstInclusion (k c) (l c) a)) = _
    have h := DFunLike.congr_fun (D c).first_square a
    change (D c).left (firstInclusion (k c) (l c) a) = _ at h
    rw [h]
    exact hs₀ c (commonMap (k c) (l c) (T c) a)
  · intro c a
    change channel _ F₁ c ((D c).right (secondInclusion A (k c) (l c) a)) = _
    have h := DFunLike.congr_fun (D c).second_square a
    change (D c).right (secondInclusion A (k c) (l c) a) = _ at h
    rw [h]
    exact hs₁ c (commonMap (k c) (l c) (T c) a)
end CertifiedAggregation

/-- One finite choice, whose existence will be proved. The retained `realization`
contains actual multiplicity-certified maps. The aggregate is constructed
canonically from these data below, with no external mathematical input. -/
structure Lift (P : Stage) (q : ℕ) where
  q_pos : 0 < q
  U : IntegerMatrix
  unit : IsUnit U
  determinant : U.det = 1
  nonnegative : ∀ i j, 0 ≤ U i j
  positive : Positive (U * InitialGraphPresentation.B)
  S : Channel → IntegerMatrix
  H : Channel → IntegerMatrix
  Z : Channel → IntegerMatrix
  chain : ∀ c, S c * P.B = (U * InitialGraphPresentation.B) * H c
  S_pos : ∀ c, Positive (S c)
  T_pos : ∀ c, Positive (MatrixDiagrams.diagram P.B (S c) (H c) (Z c))
  R_pos : ∀ c, Positive (S c + (U * InitialGraphPresentation.B) * Z c)
  cokernel_map : ∀ c x, quotient (U * InitialGraphPresentation.B) (S c *ᵥ x) =
    targetCokernelEquiv InitialGraphPresentation.B U unit (P.prescribed c (quotient P.B x))
  kernel_map : ∀ c (x : Kernel P.B), H c *ᵥ x.val = 0
  realization : ∀ c, Realization P.A (natMatrix (1 + U * InitialGraphPresentation.B))
    (natMatrix (MatrixDiagrams.diagram P.B (S c) (H c) (Z c)))
    (natMatrix (S c)) (natMatrix (S c + (U * InitialGraphPresentation.B) * Z c))
    (P.scaledK q c) (P.scaledL q c)

/-- Every stage and every positive noise dimension have an actual next lift.
The only choices here select witnesses to the already proved positive lifting
and concrete finite realization theorems. -/
theorem lift_exists (P : Stage) (q : ℕ) (hq : 0 < q) : Nonempty (Lift P q) := by
  obtain ⟨U,hU,hdet,hU0,hUB,_hker,S,H,Z,h⟩ :=
    simultaneous_positive_lifting P.B InitialGraphPresentation.B P.positive
      InitialGraphPresentation.positive P.prescribed (fun _ : Channel => 0)
  refine ⟨⟨hq,U,hU,hdet,hU0,hUB,S,H,Z,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · exact fun c => (h c).1
  · exact fun c => (h c).2.1
  · exact fun c => (h c).2.2.1
  · exact fun c => (h c).2.2.2.1
  · exact fun c => (h c).2.2.2.2.1
  · intro c x
    simpa using (h c).2.2.2.2.2 x
  · intro c
    exact Classical.choice (integer_realization P.B (U * InitialGraphPresentation.B)
      (S c) (H c) (Z c) P.positive hUB (h c).1 (h c).2.1 (h c).2.2.1
      (h c).2.2.2.1 (P.scaledK q c) (P.scaledL q c))

namespace Lift
variable {P : Stage} {q : ℕ} (D : Lift P q)
abbrev T : Channel → CommonMatrix :=
  fun c => natMatrix (MatrixDiagrams.diagram P.B (D.S c) (D.H c) (D.Z c))
abbrev K : Channel → Vertex → ℕ := channelLeft (P.scaledK q) (P.scaledL q) D.T
abbrev L : Channel → Vertex → ℕ := channelRight (P.scaledK q) (P.scaledL q) D.T

theorem natural_positive (c : Channel) : ∀ i j, 0 < D.T c i j :=
  natMatrix_positive _ (D.T_pos c)

theorem channel_dimensions_positive (c : Channel) :
    (∀ i, 0 < D.K c i) ∧ (∀ i, 0 < D.L c i) :=
  target_dimensions_positive (P.scaledK q c) (P.scaledL q c)
    (fun i => Nat.mul_pos (scale_pos q D.q_pos c) (P.k_pos i)) (D.T c) (D.natural_positive c)

def next : Stage where
  U := D.U
  unit := D.unit
  determinant := D.determinant
  nonnegative := D.nonnegative
  positive := D.positive
  k := total D.K
  l := total D.L
  k_pos := fun i => lt_of_lt_of_le ((D.channel_dimensions_positive 0).1 i)
    (Finset.single_le_sum (fun c _ => Nat.zero_le (D.K c i)) (Finset.mem_univ 0))
  l_pos := fun i => lt_of_lt_of_le ((D.channel_dimensions_positive 0).2 i)
    (Finset.single_le_sum (fun c _ => Nat.zero_le (D.L c i)) (Finset.mem_univ 0))

/-- The unsigned dimensions count the noise block q times. They do not use
the sign of the K0 channel, which belongs to the presentation coordinates. -/
def totalMultiplicity : CommonMatrix := D.T 0 + D.T 1 + q • D.T 2

theorem weighted_matrix :
    (∑ c, fun i j => scale q c * D.T c i j) = D.totalMultiplicity := by
  ext i j
  change (∑ c, scale q c * D.T c i j) = D.T 0 i j + D.T 1 i j + q * D.T 2 i j
  simp [scale, Fin.sum_univ_succ, add_assoc]

theorem dimensions : Sum.elim D.next.k D.next.l =
    targetSize (Sum.elim P.k P.l) D.totalMultiplicity := by
  change Sum.elim (total D.K) (total D.L) = _
  rw [weighted_common_dimensions P.k P.l D.T (scale q), D.weighted_matrix]

/-- Applying the displayed signed coordinate to the actual quotient square
recovers exactly +1, -1, or 0. -/
theorem signed_cokernel (c : Channel) (x : Vertex → ℤ) :
    D.next.cokernel (quotient D.next.B (D.S c *ᵥ x)) =
      sign c * P.cokernel (quotient P.B x) := by
  change InitialGraphPresentation.transportedCokernel D.U D.unit
    (quotient (D.U * InitialGraphPresentation.B) (D.S c *ᵥ x)) = _
  rw [D.cokernel_map]
  change InitialGraphPresentation.cokernelEquiv
    ((targetCokernelEquiv InitialGraphPresentation.B D.U D.unit).symm
      (targetCokernelEquiv InitialGraphPresentation.B D.U D.unit
        (P.prescribed c (quotient P.B x)))) = _
  rw [LinearEquiv.symm_apply_apply, Stage.prescribed_coordinate]

/-- The degree-one map on the actual kernel is zero in every channel. -/
def onKernel (_c : Channel) : Kernel P.B →ₗ[ℤ] Kernel D.next.B := 0

theorem onKernel_matrix (c : Channel) (x : Kernel P.B) :
    (D.onKernel c x).val = D.H c *ᵥ x.val := by
  rw [D.kernel_map]
  rfl

theorem zero_kernel_coordinate (c : Channel) (x : Kernel P.B) :
    D.next.kernel (D.onKernel c x) = 0 := map_zero _

/-- This is the canonical aggregate, assembled from the retained actual
multiplicity-certified Realizations. It is not a separately chosen aggregate. -/
def aggregate : Aggregate P.A D.next.A (P.scaledK q) (P.scaledL q) D.T :=
  certifiedAggregate P.A D.next.A (P.scaledK q) (P.scaledL q) D.T
    (fun c => natMatrix (D.S c)) (fun c => natMatrix (D.S c + D.next.B * D.Z c)) D.realization

/-- Exact common-map factorization preserves its T multiplicity witness. -/
theorem aggregate_common (c : Channel) : D.aggregate.common c =
    (channel (fun c => Blocks (commonWeights D.K D.L c)) (commonAggregate D.K D.L) c).comp
      (commonMap (P.scaledK q c) (P.scaledL q c) (D.T c)).toNonUnitalStarAlgHom := rfl

/-- Exact first-factor factorization preserves the S multiplicity witness. -/
theorem aggregate_left (c : Channel) : D.aggregate.left c =
    (channel (fun c => Blocks (D.K c + D.L c)) (canonicalFirst D.K D.L) c).comp
      (D.realization c).left.toNonUnitalStarAlgHom := rfl

/-- Exact second-factor factorization preserves the S+B'Z witness. -/
theorem aggregate_right (c : Channel) : D.aggregate.right c =
    (channel (fun c => Blocks (D.K c + D.next.A *ᵥ D.L c))
      (canonicalSecond D.K D.L D.next.A) c).comp
      (D.realization c).right.toNonUnitalStarAlgHom := rfl

/-- The concrete diagram can be used directly with the next stage dimensions. -/
abbrev diagram : Aggregate P.A D.next.A (P.scaledK q) (P.scaledL q) D.T := D.aggregate

theorem all_common_supports_nonzero : ∀ c i, D.diagram.common c 1 i ≠ 0 :=
  D.diagram.positive_common_blocks
    (fun c i => Nat.mul_pos (scale_pos q D.q_pos c) (P.k_pos i)) D.natural_positive
end Lift

/-- An actual unital map of finite triples, with both squares literally
commuting and all three connecting maps preserving the C*-norm. -/
structure FiniteBond (A A' : Matrix Vertex Vertex ℕ)
    (k l k' l' : Vertex → ℕ) where
  common : Blocks (Sum.elim k l) →⋆ₐ[ℂ] Blocks (Sum.elim k' l')
  left : Blocks (k+l) →⋆ₐ[ℂ] Blocks (k'+l')
  right : Blocks (k+A*ᵥl) →⋆ₐ[ℂ] Blocks (k'+A'*ᵥl')
  common_isometry : Isometry common
  left_isometry : Isometry left
  right_isometry : Isometry right
  first_square : left.comp (firstInclusion k l) = (firstInclusion k' l').comp common
  second_square : right.comp (secondInclusion A k l) = (secondInclusion A' k' l').comp common

abbrev Bond (P Q : Stage) := FiniteBond P.A Q.A P.k P.l Q.k Q.l

/-- One copy of each signed channel and q individually orthogonal copies of
the zero channel. This also constructs the unital aggregate on scalar stages. -/
abbrev ExpandedChannel (q : ℕ) := Unit ⊕ (Unit ⊕ Fin q)
def collapse {q : ℕ} : ExpandedChannel q → Channel
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

namespace Lift
variable {P : Stage} {q : ℕ} (D : Lift P q)

abbrev expandedT : ExpandedChannel q → CommonMatrix := fun c => D.T (collapse c)
abbrev expandedK : ExpandedChannel q → Vertex → ℕ :=
  channelLeft (fun _ => P.k) (fun _ => P.l) D.expandedT
abbrev expandedL : ExpandedChannel q → Vertex → ℕ :=
  channelRight (fun _ => P.k) (fun _ => P.l) D.expandedT

theorem expanded_multiplicity : (∑ c, D.expandedT c) = D.totalMultiplicity := by
  ext i j
  simp only [Matrix.sum_apply]
  change (∑ c : ExpandedChannel q, D.T (collapse c) i j) =
    D.T 0 i j + D.T 1 i j + q * D.T 2 i j
  simp [Fintype.sum_sum_type, collapse, add_assoc]

theorem expanded_dimensions :
    Sum.elim (total D.expandedK) (total D.expandedL) = Sum.elim D.next.k D.next.l := by
  rw [D.dimensions]
  have h := weighted_common_dimensions P.k P.l D.expandedT (fun _ => 1)
  simpa only [one_mul, D.expanded_multiplicity] using h

theorem expandedK_eq : total D.expandedK = D.next.k := by
  funext i
  exact congrFun D.expanded_dimensions (Sum.inl i)

theorem expandedL_eq : total D.expandedL = D.next.l := by
  funext i
  exact congrFun D.expanded_dimensions (Sum.inr i)

/-- Repeated zero channels are constructed by the same integer realization
lemma. No scalar-amplification isomorphism or graph theorem is assumed here. -/
def expandedAggregate : Aggregate P.A D.next.A (fun _ : ExpandedChannel q => P.k)
    (fun _ => P.l) D.expandedT :=
  Classical.choice (integer_aggregate P.B D.next.B P.positive D.next.positive
    (fun c => D.S (collapse c)) (fun c => D.H (collapse c)) (fun c => D.Z (collapse c))
    (fun c => D.chain (collapse c)) (fun c => D.S_pos (collapse c))
    (fun c => D.T_pos (collapse c)) (fun c => D.R_pos (collapse c))
    (fun _ => P.k) (fun _ => P.l))

/-- The scalar sum is an actual unital isometric map of triples into exactly
the next recursively specified dimensions. -/
theorem bond_exists : Nonempty (Bond P D.next) := by
  let E := D.expandedAggregate
  obtain ⟨hc,hl,hr⟩ := sum_isometries P.A D.next.A P.k P.l D.expandedT E
  have h : Nonempty (FiniteBond P.A D.next.A P.k P.l
      (total D.expandedK) (total D.expandedL)) :=
    ⟨⟨sumCommon P.A D.next.A P.k P.l D.expandedT E,
      sumLeft P.A D.next.A P.k P.l D.expandedT E,
      sumRight P.A D.next.A P.k P.l D.expandedT E,
      hc,hl,hr,
      sum_first_square P.A D.next.A P.k P.l D.expandedT E,
      sum_second_square P.A D.next.A P.k P.l D.expandedT E⟩⟩
  rw [D.expandedK_eq,D.expandedL_eq] at h
  exact h

def bond : Bond P D.next := Classical.choice D.bond_exists

/-- The actual quotient map, expressed through the fixed signed coordinates. -/
def onCokernel (c : Channel) : Cokernel P.B →ₗ[ℤ] Cokernel D.next.B :=
  D.next.cokernel.symm.toLinearMap.comp
    ((sign c • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).comp P.cokernel.toLinearMap)

theorem onCokernel_quotient (c : Channel) (x : Vertex → ℤ) :
    D.onCokernel c (quotient P.B x) = quotient D.next.B (D.S c *ᵥ x) := by
  apply D.next.cokernel.injective
  simpa [onCokernel] using (D.signed_cokernel c x).symm

end Lift

/-- Choice is used only after existence has been proved. -/
def chosenLift (P : Stage) (q : ℕ) (hq : 0 < q) : Lift P q :=
  Classical.choice (lift_exists P q hq)

/-- The stage sequence is defined recursively, for arbitrary prescribed
positive noise dimensions and arbitrary positive initial common weights. -/
def stages (q : ℕ → ℕ) (hq : ∀ h, 0 < q h)
    (k l : Vertex → ℕ) (hk : ∀ i, 0 < k i) (hl : ∀ i, 0 < l i) : ℕ → Stage
  | 0 => Stage.initial k l hk hl
  | h + 1 => (chosenLift (stages q hq k l hk hl h) (q h) (hq h)).next

/-- A resulting system includes the witnesses used at every recursive step;
its existence is not an assumption of the construction theorem. -/
structure System (q : ℕ → ℕ) (k l : Vertex → ℕ) where
  stage : ℕ → Stage
  initial_B : (stage 0).B = InitialGraphPresentation.B
  initial_k : (stage 0).k = k
  initial_l : (stage 0).l = l
  step : ∀ h, Lift (stage h) (q h)
  successor : ∀ h, (step h).next = stage (h+1)

/-- Constructive existence modulo ordinary classical witness choice; no
published input and no recursive-family assumption occurs in its type. -/
def construct (q : ℕ → ℕ) (hq : ∀ h, 0 < q h)
    (k l : Vertex → ℕ) (hk : ∀ i, 0 < k i) (hl : ∀ i, 0 < l i) : System q k l where
  stage := stages q hq k l hk hl
  initial_B := Stage.initial_B k l hk hl
  initial_k := rfl
  initial_l := rfl
  step := fun h => chosenLift (stages q hq k l hk hl h) (q h) (hq h)
  successor := fun _ => rfl

theorem recursive_sequence_exists (q : ℕ → ℕ) (hq : ∀ h, 0 < q h)
    (k l : Vertex → ℕ) (hk : ∀ i, 0 < k i) (hl : ∀ i, 0 < l i) : Nonempty (System q k l) :=
  ⟨construct q hq k l hk hl⟩

namespace System
variable {q : ℕ → ℕ} {k l : Vertex → ℕ} (R : System q k l)

/-- Actual unital scalar triple maps between consecutive stages. -/
def bond (h : ℕ) : Bond (R.stage h) (R.stage (h+1)) :=
  R.successor h ▸ (R.step h).bond

/-- All presentation matrices remain strictly positive, on the same two
vertices, and have actual kernel and cokernel isomorphic to ℤ. -/
theorem presentations (h : ℕ) : Positive (R.stage h).B ∧
    Nonempty (Cokernel (R.stage h).B ≃ₗ[ℤ] ℤ) ∧
    Nonempty (Kernel (R.stage h).B ≃ₗ[ℤ] ℤ) :=
  ⟨(R.stage h).positive, ⟨(R.stage h).cokernel⟩, ⟨(R.stage h).kernel⟩⟩

theorem dimensions (h : ℕ) :
    Sum.elim (R.stage (h+1)).k (R.stage (h+1)).l =
      targetSize (Sum.elim (R.stage h).k (R.stage h).l) (R.step h).totalMultiplicity := by
  simpa only [R.successor h] using (R.step h).dimensions

theorem signed_cokernel (h : ℕ) (c : Channel) (x : Vertex → ℤ) :
    (R.stage (h+1)).cokernel
      (quotient (R.stage (h+1)).B ((R.step h).S c *ᵥ x)) =
        sign c * (R.stage h).cokernel (quotient (R.stage h).B x) := by
  have he := congrArg (fun Q : Stage =>
    Q.cokernel (quotient Q.B ((R.step h).S c *ᵥ x))) (R.successor h)
  rw [← he]
  exact (R.step h).signed_cokernel c x

theorem zero_kernel_matrix (h : ℕ) (c : Channel) (x : Kernel (R.stage h).B) :
    (R.step h).H c *ᵥ x.val = 0 := (R.step h).kernel_map c x

end System

/-- A nonunital scalar map of triples, retaining literal squares and
injectivity before summing the mutually orthogonal channels. -/
structure ScalarBond (A A' : Matrix Vertex Vertex ℕ)
    (k l k' l' : Vertex → ℕ) where
  common : Blocks (Sum.elim k l) →⋆ₙₐ[ℂ] Blocks (Sum.elim k' l')
  left : Blocks (k+l) →⋆ₙₐ[ℂ] Blocks (k'+l')
  right : Blocks (k+A*ᵥl) →⋆ₙₐ[ℂ] Blocks (k'+A'*ᵥl')
  common_isometry : Isometry common
  left_isometry : Isometry left
  right_isometry : Isometry right
  first_square : ∀ a, left (firstInclusion k l a) = firstInclusion k' l' (common a)
  second_square : ∀ a, right (secondInclusion A k l a) = secondInclusion A' k' l' (common a)

namespace ScalarBond
variable {A A' : Matrix Vertex Vertex ℕ} {k l k₀ l₀ k' l' : Vertex → ℕ}

def castSource (D : ScalarBond A A' k₀ l₀ k' l') (hk : k₀ = k) (hl : l₀ = l) :
    ScalarBond A A' k l k' l' := hk ▸ hl ▸ D

theorem castSource_common_one (D : ScalarBond A A' k₀ l₀ k' l') (hk : k₀ = k) (hl : l₀ = l) :
    (D.castSource hk hl).common 1 = D.common 1 := by subst k; subst l; rfl

theorem castSource_left_one (D : ScalarBond A A' k₀ l₀ k' l') (hk : k₀ = k) (hl : l₀ = l) :
    (D.castSource hk hl).left 1 = D.left 1 := by subst k; subst l; rfl

theorem castSource_right_one (D : ScalarBond A A' k₀ l₀ k' l') (hk : k₀ = k) (hl : l₀ = l) :
    (D.castSource hk hl).right 1 = D.right 1 := by subst k; subst l; rfl
end ScalarBond

namespace Lift
variable {P : Stage} {q : ℕ} (D : Lift P q)

def rawChannel (c : Channel) : ScalarBond P.A D.next.A
    (P.scaledK q c) (P.scaledL q c) D.next.k D.next.l :=
  ⟨D.diagram.common c,D.diagram.left c,D.diagram.right c,
    D.diagram.common_isometry c,D.diagram.left_isometry c,D.diagram.right_isometry c,
    D.diagram.first_square c,D.diagram.second_square c⟩

def scalarChannel (c : Channel) (hc : scale q c = 1) :
    ScalarBond P.A D.next.A P.k P.l D.next.k D.next.l :=
  (D.rawChannel c).castSource
    (by funext i; simp only [Stage.scaledK,hc,one_mul])
    (by funext i; simp only [Stage.scaledL,hc,one_mul])

theorem scalarChannel_common_one (c : Channel) (hc : scale q c = 1) :
    (D.scalarChannel c hc).common 1 = D.diagram.common c 1 :=
  ScalarBond.castSource_common_one _ _ _

theorem scalarChannel_left_one (c : Channel) (hc : scale q c = 1) :
    (D.scalarChannel c hc).left 1 = D.diagram.left c 1 :=
  ScalarBond.castSource_left_one _ _ _

theorem scalarChannel_right_one (c : Channel) (hc : scale q c = 1) :
    (D.scalarChannel c hc).right 1 = D.diagram.right c 1 :=
  ScalarBond.castSource_right_one _ _ _

def positiveChannel : ScalarBond P.A D.next.A P.k P.l D.next.k D.next.l :=
  D.scalarChannel 0 rfl

def negativeChannel : ScalarBond P.A D.next.A P.k P.l D.next.k D.next.l :=
  D.scalarChannel 1 rfl
end Lift

section Amplification

variable {s : Type*}
variable {I : Type*} [Fintype I] [DecidableEq I]

def amplifyInto (w D : s → ℕ) (E : ∀ i, (I × Fin (w i)) ≃ Fin (D i)) :
    CStarMatrix I I (Blocks w) ≃⋆ₐ[ℂ] Blocks D :=
  { (Matrix.piAlgEquiv ℂ (n := I) (β := fun i => Matrix (Fin (w i)) (Fin (w i)) ℂ)).trans
      (AlgEquiv.piCongrRight fun i =>
        (Matrix.compAlgEquiv I (Fin (w i)) ℂ ℂ).trans
          (Matrix.reindexAlgEquiv ℂ ℂ (E i))) with
    map_star' := by intro a; funext i; ext r t; rfl
    map_smul' := by intro z a; funext i; ext r t; rfl }

theorem amplifyInto_pullback (w D : s → ℕ) (E : ∀ i, (I × Fin (w i)) ≃ Fin (D i))
    (a : CStarMatrix I I (Blocks w)) (i : s) (r t : I) (u v : Fin (w i)) :
    amplifyInto w D E a i (E i (r,u)) (E i (t,v)) = a r t i u v := by
  change a ((E i).symm (E i (r,u))).1 ((E i).symm (E i (t,v))).1 i
    ((E i).symm (E i (r,u))).2 ((E i).symm (E i (t,v))).2 = _
  simp


variable {t : Type*} [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]

def productSigma (w : s → ℕ) (H : Matrix t s ℕ) (v : t) :
    (I × (Σ c : Copies H v, Fin (w c.1))) ≃ (Σ c : Copies H v, I × Fin (w c.1)) where
  toFun x := ⟨x.2.1,x.1,x.2.2⟩
  invFun x := (x.2.1,⟨x.1,x.2.2⟩)
  left_inv := by rintro ⟨r,c,i⟩; rfl
  right_inv := by rintro ⟨c,r,i⟩; rfl

def amplifyFactorEquiv (w D : s → ℕ) (E : ∀ i, (I × Fin (w i)) ≃ Fin (D i))
    (H : Matrix t s ℕ) (v : t) :
    (I × Fin (targetSize w H v)) ≃ Fin (targetSize D H v) :=
  (Equiv.prodCongr (Equiv.refl I) (slotEquiv w H v).symm).trans
    ((productSigma w H v).trans
      ((Equiv.sigmaCongrRight (fun c : Copies H v => E c.1)).trans (slotEquiv D H v)))

omit [Fintype I] [DecidableEq I] [Fintype t] [DecidableEq s] [DecidableEq t] in
theorem amplifyFactorEquiv_apply (w D : s → ℕ)
    (E : ∀ i, (I × Fin (w i)) ≃ Fin (D i)) (H : Matrix t s ℕ)
    (v : t) (r : I) (c : Copies H v) (i : Fin (w c.1)) :
    amplifyFactorEquiv w D E H v (r,slotEquiv w H v ⟨c,i⟩) =
      slotEquiv D H v ⟨c,E c.1 (r,i)⟩ := by simp [amplifyFactorEquiv,productSigma]

omit [Fintype t] [DecidableEq t] in
/-- The same common flattening, together with the forced factor reindexing,
commutes literally with every natural-multiplicity inclusion. -/
theorem amplification_square (w D : s → ℕ)
    (E : ∀ i, (I × Fin (w i)) ≃ Fin (D i)) (H : Matrix t s ℕ)
    (a : CStarMatrix I I (Blocks w)) :
    amplifyInto (targetSize w H) (targetSize D H) (amplifyFactorEquiv w D E H)
      (CStarMatrix.mapₙₐ (multiplicityHom w H).toNonUnitalStarAlgHom a) =
        multiplicityHom D H (amplifyInto w D E a) := by
  funext v
  apply CStarMatrix.ext
  intro x y
  obtain ⟨⟨r,u⟩,rfl⟩ := (amplifyFactorEquiv w D E H v).surjective x
  obtain ⟨⟨z,b⟩,rfl⟩ := (amplifyFactorEquiv w D E H v).surjective y
  rw [amplifyInto_pullback]
  obtain ⟨⟨c,i⟩,rfl⟩ := (slotEquiv w H v).surjective u
  obtain ⟨⟨d,j⟩,rfl⟩ := (slotEquiv w H v).surjective b
  change multiplicityHom w H (a r z) v _ _ = _
  rw [amplifyFactorEquiv_apply,amplifyFactorEquiv_apply,
    multiplicityHom_pullback,multiplicityHom_pullback]
  by_cases hcd : c = d
  · subst d
    rw [copyHom_same,copyHom_same]
    exact (amplifyInto_pullback w D E a c.1 r z i j).symm
  · rw [copyHom_different _ _ _ hcd,copyHom_different _ _ _ hcd]

omit [Fintype t] [DecidableEq t] in
/-- Both dimension equalities are implemented by actual coordinate transport. -/
theorem amplification_intoDimensions (w D : s → ℕ)
    (E : ∀ i, (I × Fin (w i)) ≃ Fin (D i)) (H : Matrix t s ℕ)
    (f g : t → ℕ) (hf : targetSize w H = f) (hg : targetSize D H = g) :
    ∃ F : CStarMatrix I I (Blocks f) ≃⋆ₐ[ℂ] Blocks g,
      ∀ a, F (CStarMatrix.mapₙₐ (intoDimensions w H f hf).toNonUnitalStarAlgHom a) =
        intoDimensions D H g hg (amplifyInto w D E a) := by
  subst f
  subst g
  exact ⟨amplifyInto _ _ (amplifyFactorEquiv w D E H), amplification_square w D E H⟩

/-- A matrix amplification of the whole scalar triple, using one common
flattening and the two explicitly compatible factor rearrangements. -/
structure TripleAmplification (P : Stage) (q : ℕ) (J : Type*) [Fintype J] [DecidableEq J] where
  common : CStarMatrix J J (Blocks (Sum.elim P.k P.l)) ≃⋆ₐ[ℂ]
    Blocks (Sum.elim (fun i => q * P.k i) (fun i => q * P.l i))
  left : CStarMatrix J J (Blocks (P.k + P.l)) ≃⋆ₐ[ℂ]
    Blocks ((fun i => q * P.k i) + (fun i => q * P.l i))
  right : CStarMatrix J J (Blocks (P.k + P.A *ᵥ P.l)) ≃⋆ₐ[ℂ]
    Blocks ((fun i => q * P.k i) + P.A *ᵥ (fun i => q * P.l i))
  first_square : ∀ a, left (CStarMatrix.mapₙₐ (firstInclusion P.k P.l).toNonUnitalStarAlgHom a) =
    firstInclusion (fun i => q * P.k i) (fun i => q * P.l i) (common a)
  second_square : ∀ a, right (CStarMatrix.mapₙₐ (secondInclusion P.A P.k P.l).toNonUnitalStarAlgHom a) =
    secondInclusion P.A (fun i => q * P.k i) (fun i => q * P.l i) (common a)

def scaleIndex {q : ℕ} (eI : I ≃ Fin q) (w : s → ℕ) (i : s) :
    (I × Fin (w i)) ≃ Fin (q * w i) :=
  (Equiv.prodCongr eI (Equiv.refl _)).trans finProdFinEquiv

def commonScaleIndex (P : Stage) {q : ℕ} (eI : I ≃ Fin q) (i : Vertex ⊕ Vertex) :
    (I × Fin (Sum.elim P.k P.l i)) ≃
      Fin (Sum.elim (fun i => q * P.k i) (fun i => q * P.l i) i) := by
  cases i with
  | inl i => exact scaleIndex eI P.k i
  | inr i => exact scaleIndex eI P.l i

/-- This finite matrix algebra fact is proved internally for any finite index
set equivalent to Fin q, including a universe-lifted Fin q. -/
theorem triple_amplification_exists (P : Stage) {q : ℕ} (eI : I ≃ Fin q) :
    Nonempty (TripleAmplification P q I) := by
  let w := Sum.elim P.k P.l
  let D := Sum.elim (fun i => q * P.k i) (fun i => q * P.l i)
  let E := commonScaleIndex P eI
  obtain ⟨F₀,h₀⟩ := amplification_intoDimensions w D E firstMultiplicity
    (P.k+P.l) ((fun i => q*P.k i)+(fun i => q*P.l i))
    (first_targetSize P.k P.l) (first_targetSize _ _)
  obtain ⟨F₁,h₁⟩ := amplification_intoDimensions w D E (secondMultiplicity P.A)
    (P.k+P.A*ᵥP.l) ((fun i => q*P.k i)+P.A*ᵥ(fun i => q*P.l i))
    (second_targetSize P.A P.k P.l) (second_targetSize P.A _ _)
  exact ⟨⟨amplifyInto w D E,F₀,F₁,h₀,h₁⟩⟩

def tripleAmplification (P : Stage) {q : ℕ} (eI : I ≃ Fin q) : TripleAmplification P q I :=
  Classical.choice (triple_amplification_exists P eI)

local instance blocksOrder {V : Type*} [Fintype V] (w : V → ℕ) : PartialOrder (Blocks w) :=
  CStarAlgebra.spectralOrder _

local instance blocksStarOrderedRing {V : Type*} [Fintype V] (w : V → ℕ) :
    StarOrderedRing (Blocks w) := CStarAlgebra.spectralOrderedRing _

namespace Lift
variable {P : Stage} {q : ℕ} (D : Lift P q) (eI : I ≃ Fin q)

def noiseCommon : CStarMatrix I I (Blocks (Sum.elim P.k P.l)) →⋆ₙₐ[ℂ]
    Blocks (Sum.elim D.next.k D.next.l) :=
  (D.diagram.common 2).comp (tripleAmplification P eI).common.toStarAlgHom.toNonUnitalStarAlgHom

def noiseLeft : CStarMatrix I I (Blocks (P.k+P.l)) →⋆ₙₐ[ℂ]
    Blocks (D.next.k+D.next.l) :=
  (D.diagram.left 2).comp (tripleAmplification P eI).left.toStarAlgHom.toNonUnitalStarAlgHom

def noiseRight : CStarMatrix I I (Blocks (P.k+P.A*ᵥP.l)) →⋆ₙₐ[ℂ]
    Blocks (D.next.k+D.next.A*ᵥD.next.l) :=
  (D.diagram.right 2).comp (tripleAmplification P eI).right.toStarAlgHom.toNonUnitalStarAlgHom

theorem noise_first_square (a : CStarMatrix I I (Blocks (Sum.elim P.k P.l))) :
    D.noiseLeft eI (CStarMatrix.mapₙₐ (firstInclusion P.k P.l).toNonUnitalStarAlgHom a) =
      firstInclusion D.next.k D.next.l (D.noiseCommon eI a) := by
  change D.diagram.left 2 ((tripleAmplification P eI).left _) = _
  rw [(tripleAmplification P eI).first_square]
  exact D.diagram.first_square 2 ((tripleAmplification P eI).common a)

theorem noise_second_square (a : CStarMatrix I I (Blocks (Sum.elim P.k P.l))) :
    D.noiseRight eI (CStarMatrix.mapₙₐ (secondInclusion P.A P.k P.l).toNonUnitalStarAlgHom a) =
      secondInclusion D.next.A D.next.k D.next.l (D.noiseCommon eI a) := by
  change D.diagram.right 2 ((tripleAmplification P eI).right _) = _
  rw [(tripleAmplification P eI).second_square]
  exact D.diagram.second_square 2 ((tripleAmplification P eI).common a)

theorem noiseCommon_one : D.noiseCommon eI 1 = D.diagram.common 2 1 := by
  change D.diagram.common 2 ((tripleAmplification P eI).common 1) = _
  rw [map_one]

theorem noiseLeft_one : D.noiseLeft eI 1 = D.diagram.left 2 1 := by
  change D.diagram.left 2 ((tripleAmplification P eI).left 1) = _
  rw [map_one]

theorem noiseRight_one : D.noiseRight eI 1 = D.diagram.right 2 1 := by
  change D.diagram.right 2 ((tripleAmplification P eI).right 1) = _
  rw [map_one]

theorem noise_isometries : Isometry (D.noiseCommon eI) ∧ Isometry (D.noiseLeft eI) ∧
    Isometry (D.noiseRight eI) :=
  ⟨NonUnitalStarAlgHom.isometry _ ((D.diagram.common_isometry 2).injective.comp
      (tripleAmplification P eI).common.injective),
    NonUnitalStarAlgHom.isometry _ ((D.diagram.left_isometry 2).injective.comp
      (tripleAmplification P eI).left.injective),
    NonUnitalStarAlgHom.isometry _ ((D.diagram.right_isometry 2).injective.comp
      (tripleAmplification P eI).right.injective)⟩

/-- All three common-channel units are precisely the original orthogonal
aggregate supports, including the full matrix unit of the amplified noise. -/
theorem common_channel_units :
    D.positiveChannel.common 1 + D.negativeChannel.common 1 + D.noiseCommon eI 1 = 1 := by
  rw [noiseCommon_one]
  change (D.scalarChannel 0 rfl).common 1 + (D.scalarChannel 1 rfl).common 1 + _ = _
  rw [scalarChannel_common_one,scalarChannel_common_one]
  simpa [Fin.sum_univ_succ,add_assoc] using D.diagram.common_unit_sum

theorem common_channel_orthogonal :
    D.positiveChannel.common 1 * D.negativeChannel.common 1 = 0 ∧
    D.positiveChannel.common 1 * D.noiseCommon eI 1 = 0 ∧
    D.negativeChannel.common 1 * D.noiseCommon eI 1 = 0 := by
  unfold positiveChannel negativeChannel
  rw [scalarChannel_common_one,scalarChannel_common_one,noiseCommon_one]
  exact ⟨D.diagram.common_orthogonal 0 1 (by decide),
    D.diagram.common_orthogonal 0 2 (by decide),D.diagram.common_orthogonal 1 2 (by decide)⟩

theorem left_channel_units :
    D.positiveChannel.left 1 + D.negativeChannel.left 1 + D.noiseLeft eI 1 = 1 := by
  rw [noiseLeft_one]
  change (D.scalarChannel 0 rfl).left 1 + (D.scalarChannel 1 rfl).left 1 + _ = _
  rw [scalarChannel_left_one,scalarChannel_left_one]
  simpa [Fin.sum_univ_succ,add_assoc] using D.diagram.left_unit_sum

theorem right_channel_units :
    D.positiveChannel.right 1 + D.negativeChannel.right 1 + D.noiseRight eI 1 = 1 := by
  rw [noiseRight_one]
  change (D.scalarChannel 0 rfl).right 1 + (D.scalarChannel 1 rfl).right 1 + _ = _
  rw [scalarChannel_right_one,scalarChannel_right_one]
  simpa [Fin.sum_univ_succ,add_assoc] using D.diagram.right_unit_sum

def commonSupports : Channel → Blocks (Sum.elim D.next.k D.next.l) :=
  ![D.positiveChannel.common 1,D.negativeChannel.common 1,D.noiseCommon eI 1]

def leftSupports : Channel → Blocks (D.next.k+D.next.l) :=
  ![D.positiveChannel.left 1,D.negativeChannel.left 1,D.noiseLeft eI 1]

def rightSupports : Channel → Blocks (D.next.k+D.next.A*ᵥD.next.l) :=
  ![D.positiveChannel.right 1,D.negativeChannel.right 1,D.noiseRight eI 1]

theorem commonSupports_eq (c : Channel) : D.commonSupports eI c = D.diagram.common c 1 := by
  fin_cases c <;> simp [commonSupports,positiveChannel,negativeChannel,scalarChannel_common_one,noiseCommon_one]

theorem leftSupports_eq (c : Channel) : D.leftSupports eI c = D.diagram.left c 1 := by
  fin_cases c <;> simp [leftSupports,positiveChannel,negativeChannel,scalarChannel_left_one,noiseLeft_one]

theorem rightSupports_eq (c : Channel) : D.rightSupports eI c = D.diagram.right c 1 := by
  fin_cases c <;> simp [rightSupports,positiveChannel,negativeChannel,scalarChannel_right_one,noiseRight_one]

/-- The retyped +,- and full matrix-noise channels preserve all three
orthogonal support families, in both orders of every distinct pair. -/
theorem channel_supports_orthogonal (c d : Channel) (hcd : c ≠ d) :
    D.commonSupports eI c * D.commonSupports eI d = 0 ∧
    D.leftSupports eI c * D.leftSupports eI d = 0 ∧
    D.rightSupports eI c * D.rightSupports eI d = 0 := by
  rw [commonSupports_eq,commonSupports_eq,leftSupports_eq,leftSupports_eq,
    rightSupports_eq,rightSupports_eq]
  exact ⟨D.diagram.common_orthogonal c d hcd,D.diagram.left_orthogonal c d hcd,
    D.diagram.right_orthogonal c d hcd⟩

end Lift


end Amplification

end Suzuki.RecursiveGraphSequence

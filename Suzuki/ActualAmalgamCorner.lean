import Suzuki.ActualFiniteCoefficientLimits
import Suzuki.GraphCoefficientLimit
import Suzuki.FiniteCornerAmalgam
import Suzuki.CornerPureInfiniteness

/-! Actual completed finite constituents, their literal induced full amalgam,
and the common projection corner. All new diagram and fullness conclusions
are proved from the constructed recursive scalar maps. -/
noncomputable section
namespace Suzuki.ActualAmalgamCorner
open TensorCoefficientChannels ActualGraphCoefficientSystem RecursiveGraphSequence
open MultiplicityEmbeddings TensorEvaluationPaths SequentialCStarLimit
open ActualFiniteCoefficientLimits
open scoped CStarAlgebra ComplexOrder
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 2000000

variable (T : Spatial.{u}) (H : GraphCoefficientLimit.GraphInput.{u})
  (P : GraphCoefficientLimit.SupportInput T)
  (F : CoefficientModelFromExtension.Algebra.{u}) (R : CoefficientSchedule.Schedule F) (n : ℕ)

abbrev finiteChannels (c : Constituent) :=
  ActualFiniteCoefficientLimits.coefficientChannels T c (R.recursive n)
    (CoefficientSchedule.E F) (CoefficientSchedule.quotient F)
    (CoefficientSchedule.sectionMap F) R.sigma

abbrev finiteSystem (c : Constituent) := (finiteChannels T F R n c).system
abbrev productSystem := (GraphCoefficientLimit.coefficientChannels T H P F R n).system

instance finiteStepFact (c : Constituent) :
    Fact (∀ h, Function.Injective ((finiteSystem T F R n c).step h)) :=
  TensorEvaluationPaths.stepFact T (fun h => scalarStage c ((R.recursive n).stage h))
    (CoefficientSchedule.E F) R.dimension (scalarChannels c (R.recursive n))
    (CoefficientSchedule.quotient F) (CoefficientSchedule.sectionMap F) R.sigma

abbrev finiteLimitAlgebra (c : Constituent) : Target.UnitalAlgebra.{u} :=
  ActualFiniteCoefficientLimits.limitAlgebra T c (R.recursive n)
    (CoefficientSchedule.E F) (CoefficientSchedule.quotient F)
    (CoefficientSchedule.sectionMap F) R.sigma

private def scalarCommonLeft (Q : Stage) : commonStage.{u} Q →⋆ₐ[ℂ] leftStage.{u} Q :=
  UniverseLift.map (firstInclusion Q.k Q.l)
private def scalarCommonRight (Q : Stage) : commonStage.{u} Q →⋆ₐ[ℂ] rightStage.{u} Q :=
  UniverseLift.map (secondInclusion Q.A Q.k Q.l)
private def scalarLeftProduct (Q : Stage) : leftStage.{u} Q →⋆ₐ[ℂ] graphStage.{u} Q :=
  graphFirst Q.A Q.k Q.l
private def scalarRightProduct (Q : Stage) : rightStage.{u} Q →⋆ₐ[ℂ] graphStage.{u} Q :=
  graphSecond Q.A Q.k Q.l Q.k_pos (stage_noSinks Q)

private theorem transport_square {A B : Stage → Algebra.{u}} {X Q Q' : Stage}
    {q : ℕ} (e : Q = Q') (G : ScalarChannels (A X) (A Q) q)
    (K : ScalarChannels (B X) (B Q) q) (i : ∀ Q, A Q →⋆ₐ[ℂ] B Q)
    {E : Algebra.{u}} (ε : E →⋆ₐ[ℂ] ℂ) (η : ℂ →⋆ₐ[ℂ] E)
    (σ : E →⋆ₐ[ℂ] matrixAlgebra.{u} q)
    (h : (K.phi T ε η σ).comp (T.unitalMap (i X) (StarAlgHom.id ℂ E)) =
      (T.unitalMap (i Q) (StarAlgHom.id ℂ E)).comp (G.phi T ε η σ)) :
    ((e ▸ K).phi T ε η σ).comp (T.unitalMap (i X) (StarAlgHom.id ℂ E)) =
      (T.unitalMap (i Q') (StarAlgHom.id ℂ E)).comp ((e ▸ G).phi T ε η σ) := by
  cases e
  exact h

private theorem commonLeft_naturality (h : ℕ) :
    ((finiteSystem T F R n .left).step h).comp
      (T.unitalMap (scalarCommonLeft ((R.recursive n).stage h)) (StarAlgHom.id ℂ (CoefficientSchedule.E F))) =
    (T.unitalMap (scalarCommonLeft ((R.recursive n).stage (h+1))) (StarAlgHom.id ℂ (CoefficientSchedule.E F))).comp
      ((finiteSystem T F R n .common).step h) := by
  rw [TensorEvaluationPaths.step_eq_phi, TensorEvaluationPaths.step_eq_phi]
  exact transport_square T ((R.recursive n).successor h) _ _ scalarCommonLeft
    _ _ _ (common_left_phi_square ((R.recursive n).step h) T _ _ _)

private theorem commonRight_naturality (h : ℕ) :
    ((finiteSystem T F R n .right).step h).comp
      (T.unitalMap (scalarCommonRight ((R.recursive n).stage h)) (StarAlgHom.id ℂ (CoefficientSchedule.E F))) =
    (T.unitalMap (scalarCommonRight ((R.recursive n).stage (h+1))) (StarAlgHom.id ℂ (CoefficientSchedule.E F))).comp
      ((finiteSystem T F R n .common).step h) := by
  rw [TensorEvaluationPaths.step_eq_phi, TensorEvaluationPaths.step_eq_phi]
  exact transport_square T ((R.recursive n).successor h) _ _ scalarCommonRight
    _ _ _ (common_right_phi_square ((R.recursive n).step h) T _ _ _)

private theorem localProduct_square {Q : Stage} {q : ℕ} (D : Lift Q q)
    (Mq : MaximalOn T (matrixAlgebra q)) (ME : MaximalOn T (CoefficientSchedule.E F))
    (hQ : Target.IsSimple ⟨graphStage.{u} Q, inferInstance⟩)
    [Nontrivial (graphProduct.{u} D.next.A D.next.k D.next.l)]
    (σ : CoefficientSchedule.E F →⋆ₐ[ℂ] matrixAlgebra.{u} q) :
    ((graphScalarChannels T D (stage_noSinks Q) (stage_noSinks D.next) Mq hQ).phi T
      (CoefficientSchedule.quotient F) (CoefficientSchedule.sectionMap F) σ).comp
      (T.unitalMap (scalarLeftProduct Q) (StarAlgHom.id ℂ (CoefficientSchedule.E F))) =
    (T.unitalMap (scalarLeftProduct D.next) (StarAlgHom.id ℂ (CoefficientSchedule.E F))).comp
      ((leftScalarChannels D).phi T (CoefficientSchedule.quotient F) (CoefficientSchedule.sectionMap F) σ) ∧
    ((graphScalarChannels T D (stage_noSinks Q) (stage_noSinks D.next) Mq hQ).phi T
      (CoefficientSchedule.quotient F) (CoefficientSchedule.sectionMap F) σ).comp
      (T.unitalMap (scalarRightProduct Q) (StarAlgHom.id ℂ (CoefficientSchedule.E F))) =
    (T.unitalMap (scalarRightProduct D.next) (StarAlgHom.id ℂ (CoefficientSchedule.E F))).comp
      ((rightScalarChannels D).phi T (CoefficientSchedule.quotient F) (CoefficientSchedule.sectionMap F) σ) := by
  obtain ⟨hf, he⟩ := actual_phi_is_full_product_map T D (stage_noSinks Q) (stage_noSinks D.next)
    Mq ME hQ (CoefficientSchedule.quotient F) (CoefficientSchedule.sectionMap F) σ
  rw [← he]
  exact ⟨(tensor_isFullAmalgam T ME (standardGraph_isFullAmalgam Q.A Q.k Q.l
    Q.k_pos Q.l_pos (stage_noSinks Q))).lift_left _ _ hf,
    (tensor_isFullAmalgam T ME (standardGraph_isFullAmalgam Q.A Q.k Q.l
    Q.k_pos Q.l_pos (stage_noSinks Q))).lift_right _ _ hf⟩

private theorem product_naturality (ME : MaximalOn T (CoefficientSchedule.E F)) (h : ℕ) :
    ((productSystem T H P F R n).step h).comp
      (T.unitalMap (scalarLeftProduct ((R.recursive n).stage h)) (StarAlgHom.id ℂ (CoefficientSchedule.E F))) =
    (T.unitalMap (scalarLeftProduct ((R.recursive n).stage (h+1))) (StarAlgHom.id ℂ (CoefficientSchedule.E F))).comp
      ((finiteSystem T F R n .left).step h) ∧
    ((productSystem T H P F R n).step h).comp
      (T.unitalMap (scalarRightProduct ((R.recursive n).stage h)) (StarAlgHom.id ℂ (CoefficientSchedule.E F))) =
    (T.unitalMap (scalarRightProduct ((R.recursive n).stage (h+1))) (StarAlgHom.id ℂ (CoefficientSchedule.E F))).comp
      ((finiteSystem T F R n .right).step h) := by
  let S := R.recursive n
  have hn : (S.step h).next = S.stage (h+1) := S.successor h
  have hnext : Nontrivial (graphStage.{u} (S.step h).next) := by
    rw [hn]
    exact (GraphCoefficientLimit.stage_kirchberg H (S.stage (h+1))).2.2.1.1
  let : Nontrivial (graphProduct.{u} (S.step h).next.A (S.step h).next.k (S.step h).next.l) := hnext
  have hs := localProduct_square T F (S.step h)
    (P.matrix_maximal (R.dimension h) (R.dimension_pos h)) ME
    (GraphCoefficientLimit.stage_kirchberg H (S.stage h)).2.2.1 (R.sigma h)
  constructor
  · rw [TensorEvaluationPaths.step_eq_phi, TensorEvaluationPaths.step_eq_phi]
    exact transport_square T hn _ _ scalarLeftProduct _ _ _ hs.1
  · rw [TensorEvaluationPaths.step_eq_phi, TensorEvaluationPaths.step_eq_phi]
    exact transport_square T hn _ _ scalarRightProduct _ _ _ hs.2

def commonLeftFamily : (finiteSystem T F R n .common).Hom (finiteSystem T F R n .left) where
  app h := T.unitalMap (scalarCommonLeft ((R.recursive n).stage h)) (StarAlgHom.id ℂ (CoefficientSchedule.E F))
  naturality := commonLeft_naturality T F R n

def commonRightFamily : (finiteSystem T F R n .common).Hom (finiteSystem T F R n .right) where
  app h := T.unitalMap (scalarCommonRight ((R.recursive n).stage h)) (StarAlgHom.id ℂ (CoefficientSchedule.E F))
  naturality := commonRight_naturality T F R n

def leftProductFamily (ME : MaximalOn T (CoefficientSchedule.E F)) :
    (finiteSystem T F R n .left).Hom (productSystem T H P F R n) where
  app h := T.unitalMap (scalarLeftProduct ((R.recursive n).stage h)) (StarAlgHom.id ℂ (CoefficientSchedule.E F))
  naturality h := (product_naturality T H P F R n ME h).1

def rightProductFamily (ME : MaximalOn T (CoefficientSchedule.E F)) :
    (finiteSystem T F R n .right).Hom (productSystem T H P F R n) where
  app h := T.unitalMap (scalarRightProduct ((R.recursive n).stage h)) (StarAlgHom.id ℂ (CoefficientSchedule.E F))
  naturality h := (product_naturality T H P F R n ME h).2

def commonLeft : finiteLimitAlgebra T F R n .common →⋆ₐ[ℂ] finiteLimitAlgebra T F R n .left :=
  SequentialCStarLimit.map _ _ (commonLeftFamily T F R n)
def commonRight : finiteLimitAlgebra T F R n .common →⋆ₐ[ℂ] finiteLimitAlgebra T F R n .right :=
  SequentialCStarLimit.map _ _ (commonRightFamily T F R n)
def leftProduct (ME : MaximalOn T (CoefficientSchedule.E F)) :
    finiteLimitAlgebra T F R n .left →⋆ₐ[ℂ] GraphCoefficientLimit.limitAlgebra T H P F R n :=
  SequentialCStarLimit.map _ _ (leftProductFamily T H P F R n ME)
def rightProduct (ME : MaximalOn T (CoefficientSchedule.E F)) :
    finiteLimitAlgebra T F R n .right →⋆ₐ[ℂ] GraphCoefficientLimit.limitAlgebra T H P F R n :=
  SequentialCStarLimit.map _ _ (rightProductFamily T H P F R n ME)

/-- The exact completed graph coefficient system is the full amalgam of the
three completed finite systems. The four colimit properties are proved. -/
theorem limit_fullAmalgam (ME : MaximalOn T (CoefficientSchedule.E F)) :
    CStarAmalgam.IsFullAmalgam (commonLeft T F R n) (commonRight T F R n)
      (leftProduct T H P F R n ME) (rightProduct T H P F R n ME) := by
  apply SequentialCStarLimit.isFullAmalgam
  intro h
  exact tensor_isFullAmalgam T ME (standardGraph_isFullAmalgam
    ((R.recursive n).stage h).A ((R.recursive n).stage h).k ((R.recursive n).stage h).l
    ((R.recursive n).stage h).k_pos ((R.recursive n).stage h).l_pos
    (stage_noSinks ((R.recursive n).stage h)))

include P in
/-- All finite constituent properties are derived for the actual schedule. -/
theorem finiteConstituent (N : FiniteNuclearInput.{u})
    (J : JointFaithfulnessInput T)
    (hE : Target.HasCPApproximation (CoefficientModelFromExtension.unitalUnitization F))
    (c : Constituent) : Target.IsFiniteConstituent (finiteLimitAlgebra T F R n c) := by
  let : Nontrivial (CoefficientSchedule.E F) := inferInstanceAs (Nontrivial (Unitization ℂ F))
  let : TopologicalSpace.SeparableSpace (CoefficientSchedule.E F) :=
    inferInstanceAs (TopologicalSpace.SeparableSpace (Unitization ℂ F))
  exact ActualFiniteCoefficientLimits.limit_finiteConstituent T c (R.recursive n)
    (CoefficientSchedule.E F) (CoefficientSchedule.quotient F) (CoefficientSchedule.sectionMap F)
    R.sigma P N J R.sigma_tails hE


variable (N : FiniteNuclearInput.{u}) (J : JointFaithfulnessInput T)
  (hE : Target.HasCPApproximation (CoefficientModelFromExtension.unitalUnitization F))
  (ME : MaximalOn T (CoefficientSchedule.E F))

include P N J hE in
theorem commonLeft_injective : Function.Injective (commonLeft T F R n) := by
  let : Nontrivial (finiteLimitAlgebra T F R n .left) :=
    (finiteConstituent T P F R n N J hE .left).2.2.1.1
  apply injective_of_simple (finiteConstituent T P F R n N J hE .common).2.2.1
    (commonLeft T F R n).toNonUnitalStarAlgHom
  exact map_one (commonLeft T F R n) ▸ one_ne_zero

include P N J hE in
theorem commonRight_injective : Function.Injective (commonRight T F R n) := by
  let : Nontrivial (finiteLimitAlgebra T F R n .right) :=
    (finiteConstituent T P F R n N J hE .right).2.2.1.1
  apply injective_of_simple (finiteConstituent T P F R n N J hE .common).2.2.1
    (commonRight T F R n).toNonUnitalStarAlgHom
  exact map_one (commonRight T F R n) ▸ one_ne_zero

/-- The specified common-stage projection is transported by the actual
stage inclusion; no independently supplied limit projection is used. -/
def commonProjection (p : (finiteSystem T F R n .common).obj 0) :
    finiteLimitAlgebra T F R n .common := stage (finiteSystem T F R n .common) 0 p

def productProjection (p : (finiteSystem T F R n .common).obj 0) :
    GraphCoefficientLimit.limitAlgebra T H P F R n :=
  leftProduct T H P F R n ME (commonLeft T F R n (commonProjection T F R n p))

/-- The product projection is literally the initial common image followed
by the product-stage inclusion. This pins the map used by K0/Morita data. -/
theorem productProjection_stage (p : (finiteSystem T F R n .common).obj 0) :
    productProjection T H P F R n ME p =
      stage (productSystem T H P F R n) 0
        ((leftProductFamily T H P F R n ME).app 0
          ((commonLeftFamily T F R n).app 0 p)) := by
  exact (congrArg (leftProduct T H P F R n ME)
    (SequentialCStarLimit.map_stage _ _ (commonLeftFamily T F R n) 0 p)).trans
      (SequentialCStarLimit.map_stage _ _ (leftProductFamily T H P F R n ME) 0
        ((commonLeftFamily T F R n).app 0 p))

theorem commonProjection_projection {p : (finiteSystem T F R n .common).obj 0}
    (hp : IsStarProjection p) : IsStarProjection (commonProjection T F R n p) :=
  hp.map (stage (finiteSystem T F R n .common) 0)

theorem commonProjection_nonzero {p : (finiteSystem T F R n .common).obj 0}
    (hp : p ≠ 0) : commonProjection T F R n p ≠ 0 := by
  intro h
  exact hp (stage_injective (finiteSystem T F R n .common) 0
    (h.trans (map_zero _).symm))

theorem productProjection_projection {p : (finiteSystem T F R n .common).obj 0}
    (hp : IsStarProjection p) : IsStarProjection (productProjection T H P F R n ME p) :=
  ((commonProjection_projection T F R n hp).map (commonLeft T F R n)).map
    (leftProduct T H P F R n ME)

def cornerAlgebra {p : (finiteSystem T F R n .common).obj 0} (hp : IsStarProjection p) :
    Target.UnitalAlgebra.{u} :=
  ⟨CommonCorner.Corner (productProjection_projection T H P F R n ME hp), inferInstance⟩

include N J hE in
/-- Exact finite-amalgam presentation of the actual product projection corner. -/
theorem corner_hasFiniteAmalgam {p : (finiteSystem T F R n .common).obj 0}
    (hp : IsStarProjection p) (hne : p ≠ 0) :
    Target.HasFiniteAmalgam (cornerAlgebra T H P F R n ME hp) := by
  exact FiniteCornerAmalgam.hasFiniteAmalgam
    (finiteLimitAlgebra T F R n .common) (finiteLimitAlgebra T F R n .left)
    (finiteLimitAlgebra T F R n .right) (GraphCoefficientLimit.limitAlgebra T H P F R n)
    (finiteConstituent T P F R n N J hE .common)
    (finiteConstituent T P F R n N J hE .left)
    (finiteConstituent T P F R n N J hE .right)
    (commonLeft T F R n) (commonRight T F R n)
    (leftProduct T H P F R n ME) (rightProduct T H P F R n ME)
    (commonLeft_injective T P F R n N J hE)
    (commonRight_injective T P F R n N J hE)
    (limit_fullAmalgam T H P F R n ME)
    (commonProjection_projection T F R n hp) (commonProjection_nonzero T F R n hne)

include N J hE in
/-- Nonzeroness is derived from the simplicity of the actual finite left
constituent and the actual Kirchberg product limit. -/
theorem productProjection_nonzero (I : EvaluationLimitPureInfiniteness.ComparisonInput.{u})
    {p : (finiteSystem T F R n .common).obj 0} (hne : p ≠ 0) :
    productProjection T H P F R n ME p ≠ 0 := by
  let : Nontrivial (GraphCoefficientLimit.limitAlgebra T H P F R n) :=
    (GraphCoefficientLimit.limit_kirchberg T H P F R n I J hE).2.2.1.1
  have hi : Function.Injective (leftProduct T H P F R n ME) := by
    apply injective_of_simple (finiteConstituent T P F R n N J hE .left).2.2.1
      (leftProduct T H P F R n ME).toNonUnitalStarAlgHom
    exact map_one (leftProduct T H P F R n ME) ▸ one_ne_zero
  intro hz
  have hz' := hi (hz.trans (map_zero _).symm)
  have hz'' := commonLeft_injective T P F R n N J hE (hz'.trans (map_zero _).symm)
  exact commonProjection_nonzero T F R n hne hz''

include N J hE in
/-- The actual common projection corner is a Kirchberg algebra with a full
finite-constituent amalgam presentation. -/
theorem corner_properties (I : EvaluationLimitPureInfiniteness.ComparisonInput.{u})
    {p : (finiteSystem T F R n .common).obj 0} (hp : IsStarProjection p) (hne : p ≠ 0) :
    Target.IsKirchberg (cornerAlgebra T H P F R n ME hp) ∧
    Target.HasFiniteAmalgam (cornerAlgebra T H P F R n ME hp) :=
  ⟨CornerPureInfiniteness.isKirchberg (GraphCoefficientLimit.limitAlgebra T H P F R n)
    (GraphCoefficientLimit.limit_kirchberg T H P F R n I J hE)
    (productProjection_projection T H P F R n ME hp)
    (productProjection_nonzero T H P F R n N J hE ME I hne),
    corner_hasFiniteAmalgam T H P F R n N J hE ME hp hne⟩

end Suzuki.ActualAmalgamCorner

import ArchonPhysics.RandomMassTransferProjectiveStrongIrreducibility
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Continuous two-point projective transfer dynamics

Mathlib has an algebraic projectivization and a set-theoretic identification
of the real projective line with `OnePoint ℝ`, but currently supplies neither
a Furstenberg positivity theorem nor the missing topological
projectivization action needed to invoke one.  This file constructs the next
honest analytic input directly: the continuous normalized transfer action on
the compact unit-sphere double cover of the real projective line, together
with the equal-weight two-atom Markov operator on probability measures.

The operator is proved continuous for weak convergence, and its probability
measure state space is compact.  A stationary probability is therefore
reduced to the fixed-point theorem for this continuous affine operator.
Mathlib currently has no Schauder/Krylov--Bogolyubov theorem supplying that
fixed point (and `ProbabilityMeasure.lean` explicitly lists its convex-space
structure as a TODO), so no stationary measure or positive Lyapunov exponent
is asserted here.
-/

open scoped LinearAlgebra.Projectivization Matrix NNReal Topology

namespace ArchonPhysics.RandomMassTwoPointProjectiveMarkov

open ArchonPhysics
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.RandomMassTransferProjectiveStrongIrreducibility
open ArchonPhysics.RandomMassTransferGroupNoncompactness
open ArchonPhysics.RandomMassTwoStepAnnealedTransferGrowth
open MeasureTheory Set

noncomputable section

abbrev TransferVector := Fin 2 → Real

/-- The compact oriented double cover of the real projective line. -/
abbrev OrientedProjectiveDirection :=
  Metric.sphere (0 : TransferVector) 1

/-- A unit direction is nonzero. -/
theorem orientedProjectiveDirection_ne_zero
    (direction : OrientedProjectiveDirection) :
    (direction : TransferVector) ≠ 0 := by
  simpa using Metric.ne_of_mem_sphere direction.property one_ne_zero

/-- An invertible transfer matrix does not annihilate a unit direction. -/
theorem oneStepTransferState_direction_ne_zero
    (lambda mass : Real) (direction : OrientedProjectiveDirection) :
    oneStepTransferState lambda mass (direction : TransferVector) ≠ 0 := by
  rw [← andersonTransferSL_smul]
  exact (smul_ne_zero_iff_ne _).2
    (orientedProjectiveDirection_ne_zero direction)

/-- Normalize one transfer step back to the unit sphere. -/
def normalizedTransferDirection
    (lambda mass : Real) (direction : OrientedProjectiveDirection) :
    OrientedProjectiveDirection :=
  ⟨NormedSpace.normalize
      (oneStepTransferState lambda mass (direction : TransferVector)), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact NormedSpace.norm_normalize
      (oneStepTransferState_direction_ne_zero lambda mass direction)⟩

/-- A transfer step depends continuously on its input vector. -/
theorem continuous_oneStepTransferState (lambda mass : Real) :
    Continuous (oneStepTransferState lambda mass) := by
  unfold oneStepTransferState
  exact continuous_const.matrix_mulVec continuous_id

/-- The normalized transfer action on oriented projective directions is
continuous. -/
theorem continuous_normalizedTransferDirection (lambda mass : Real) :
    Continuous (normalizedTransferDirection lambda mass) := by
  have hstep : Continuous (fun direction : OrientedProjectiveDirection =>
      oneStepTransferState lambda mass
        (direction : TransferVector)) :=
    (continuous_oneStepTransferState lambda mass).comp continuous_subtype_val
  have hnormalize : Continuous (fun direction : OrientedProjectiveDirection =>
      NormedSpace.normalize
        (oneStepTransferState lambda mass
          (direction : TransferVector))) := by
    rw [continuous_iff_continuousAt]
    intro direction
    have hstep_at : ContinuousAt
        (fun direction : OrientedProjectiveDirection =>
          oneStepTransferState lambda mass
            (direction : TransferVector)) direction :=
      hstep.continuousAt
    have hnorm_ne :
        ‖oneStepTransferState lambda mass
          (direction : TransferVector)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr
        (oneStepTransferState_direction_ne_zero lambda mass direction)
    change Filter.Tendsto
      (fun d : OrientedProjectiveDirection =>
        ‖oneStepTransferState lambda mass (d : TransferVector)‖⁻¹ •
          oneStepTransferState lambda mass (d : TransferVector))
      (𝓝 direction)
      (𝓝 (‖oneStepTransferState lambda mass
        (direction : TransferVector)‖⁻¹ •
          oneStepTransferState lambda mass (direction : TransferVector)))
    simpa only [Pi.inv_apply] using
      Filter.Tendsto.smul (hstep_at.norm.inv₀ hnorm_ne) hstep_at
  exact hnormalize.subtype_mk _

/-- Forget the orientation and map a unit direction to Mathlib's algebraic
real projective line. -/
def orientedDirectionProjectivePoint
    (direction : OrientedProjectiveDirection) : RealProjectiveLine :=
  Projectivization.mk Real (direction : TransferVector)
    (orientedProjectiveDirection_ne_zero direction)

/-- The continuous normalized action is a lift of the algebraic projective
transfer action. -/
theorem normalizedTransferDirection_projectivePoint
    (lambda mass : Real) (direction : OrientedProjectiveDirection) :
    orientedDirectionProjectivePoint
        (normalizedTransferDirection lambda mass direction) =
      andersonTransferSL lambda mass •
        orientedDirectionProjectivePoint direction := by
  unfold orientedDirectionProjectivePoint
  rw [Projectivization.smul_mk]
  rw [Projectivization.mk_eq_mk_iff' Real]
  refine ⟨‖oneStepTransferState lambda mass
    (direction : TransferVector)‖⁻¹, ?_⟩
  rfl

/-! ## Equal-weight averages of probability measures -/

/-- The equal-weight average of two probability measures. -/
def probabilityAverage
    {X : Type*} [MeasurableSpace X]
    (left right : ProbabilityMeasure X) : ProbabilityMeasure X :=
  ⟨(2 : NNReal)⁻¹ • (left : Measure X) +
      (2 : NNReal)⁻¹ • (right : Measure X), by
    constructor
    simp
    simpa only [ENNReal.coe_inv_two] using ENNReal.inv_two_add_inv_two⟩

@[simp]
theorem probabilityAverage_toFiniteMeasure
    {X : Type*} [MeasurableSpace X]
    (left right : ProbabilityMeasure X) :
    (probabilityAverage left right).toFiniteMeasure =
      (2 : NNReal)⁻¹ • left.toFiniteMeasure +
        (2 : NNReal)⁻¹ • right.toFiniteMeasure := by
  apply FiniteMeasure.toMeasure_injective
  rfl

/-- Equal-weight averaging is continuous for weak convergence. -/
theorem continuous_probabilityAverage
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] :
    Continuous (fun pair : ProbabilityMeasure X × ProbabilityMeasure X =>
      probabilityAverage pair.1 pair.2) := by
  rw [(ProbabilityMeasure.toFiniteMeasure_isEmbedding X).continuous_iff]
  change Continuous (fun pair : ProbabilityMeasure X × ProbabilityMeasure X =>
    (2 : NNReal)⁻¹ • pair.1.toFiniteMeasure +
      (2 : NNReal)⁻¹ • pair.2.toFiniteMeasure)
  fun_prop

/-! ## The two-point transfer Markov operator -/

/-- Push a direction law forward by one normalized transfer step. -/
def transferDirectionPushforward
    (lambda mass : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection) :
    ProbabilityMeasure OrientedProjectiveDirection :=
  law.map (continuous_normalizedTransferDirection lambda mass).measurable.aemeasurable

/-- Pushforward by one transfer action is continuous for weak convergence. -/
theorem continuous_transferDirectionPushforward (lambda mass : Real) :
    Continuous (transferDirectionPushforward lambda mass) :=
  ProbabilityMeasure.continuous_map
    (continuous_normalizedTransferDirection lambda mass)

/-- The probability-law Markov operator for the equal-weight two-atom mass
law on `mass0` and `mass1`. -/
def twoPointProjectiveMarkovOperator
    (lambda mass0 mass1 : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection) :
    ProbabilityMeasure OrientedProjectiveDirection :=
  probabilityAverage
    (transferDirectionPushforward lambda mass0 law)
    (transferDirectionPushforward lambda mass1 law)

/-- The two-point projective Markov operator is continuous in the weak
topology on probability measures. -/
theorem continuous_twoPointProjectiveMarkovOperator
    (lambda mass0 mass1 : Real) :
    Continuous (twoPointProjectiveMarkovOperator lambda mass0 mass1) := by
  exact continuous_probabilityAverage.comp
    ((continuous_transferDirectionPushforward lambda mass0).prodMk
      (continuous_transferDirectionPushforward lambda mass1))

/-- The dual Feller operator on continuous real observables. -/
def twoPointProjectiveFellerOperator
    (lambda mass0 mass1 : Real)
    (observable : C(OrientedProjectiveDirection, Real)) :
    C(OrientedProjectiveDirection, Real) :=
  ⟨fun direction =>
      (observable (normalizedTransferDirection lambda mass0 direction) +
        observable (normalizedTransferDirection lambda mass1 direction)) / 2,
    ((observable.continuous.comp
        (continuous_normalizedTransferDirection lambda mass0)).add
      (observable.continuous.comp
        (continuous_normalizedTransferDirection lambda mass1))).div_const 2⟩

@[simp]
theorem twoPointProjectiveFellerOperator_apply
    (lambda mass0 mass1 : Real)
    (observable : C(OrientedProjectiveDirection, Real))
    (direction : OrientedProjectiveDirection) :
    twoPointProjectiveFellerOperator lambda mass0 mass1 observable direction =
      (observable (normalizedTransferDirection lambda mass0 direction) +
        observable (normalizedTransferDirection lambda mass1 direction)) / 2 :=
  rfl

/-- The Feller operator preserves the constant-one observable. -/
theorem twoPointProjectiveFellerOperator_one
    (lambda mass0 mass1 : Real) :
    twoPointProjectiveFellerOperator lambda mass0 mass1 1 = 1 := by
  ext direction
  simp

/-- The Feller operator preserves pointwise nonnegativity. -/
theorem twoPointProjectiveFellerOperator_nonnegative
    (lambda mass0 mass1 : Real)
    (observable : C(OrientedProjectiveDirection, Real))
    (hobservable : ∀ direction, 0 ≤ observable direction) :
    ∀ direction,
      0 ≤ twoPointProjectiveFellerOperator
        lambda mass0 mass1 observable direction := by
  intro direction
  simp only [twoPointProjectiveFellerOperator_apply]
  exact div_nonneg
    (add_nonneg (hobservable _) (hobservable _)) (by norm_num)

/-- The weak probability-measure space on the compact direction sphere is
itself compact. -/
theorem isCompact_probabilityMeasure_orientedProjectiveDirection :
    IsCompact (Set.univ :
      Set (ProbabilityMeasure OrientedProjectiveDirection)) :=
  isCompact_univ

/-- A reusable certificate collecting exactly the algebraic and topological
inputs established for the equal-weight two-point transfer dynamics.  It does
not contain a stationary law or a Lyapunov-exponent conclusion. -/
structure TwoPointProjectivePrerequisiteCertificate
    (lambda mass0 mass1 : Real) : Prop where
  relativeTransferIdentity :
    andersonTransferSL lambda mass0 *
        (andersonTransferSL lambda mass1)⁻¹ =
      upperUnipotentShearSL (lambda * (mass1 - mass0))
  relativePowersUnbounded :
    ∀ bound : Real, ∃ n : Nat, bound <
      |((andersonTransferMatrix lambda mass0 *
        andersonTransferMatrixInverse lambda mass1) ^ n) 0 1|
  projectivelyStronglyIrreducible :
    IsProjectivelyStronglyIrreducible lambda mass0 mass1
  action0Continuous :
    Continuous (normalizedTransferDirection lambda mass0)
  action1Continuous :
    Continuous (normalizedTransferDirection lambda mass1)
  markovContinuous :
    Continuous (twoPointProjectiveMarkovOperator lambda mass0 mass1)
  fellerPreservesOne :
    twoPointProjectiveFellerOperator lambda mass0 mass1 1 = 1
  fellerPreservesNonnegative :
    ∀ observable : C(OrientedProjectiveDirection, Real),
      (∀ direction, 0 ≤ observable direction) →
      ∀ direction, 0 ≤ twoPointProjectiveFellerOperator
        lambda mass0 mass1 observable direction
  lawSpaceCompact :
    IsCompact (Set.univ :
      Set (ProbabilityMeasure OrientedProjectiveDirection))

/-- Positive parameter and distinct masses produce the complete algebraic plus
Feller/compactness prerequisite certificate available in the current library. -/
theorem twoPointProjectivePrerequisiteCertificate_of_distinct
    {lambda mass0 mass1 : Real} (hlambda : 0 < lambda)
    (hmass : mass0 ≠ mass1) :
    TwoPointProjectivePrerequisiteCertificate lambda mass0 mass1 where
  relativeTransferIdentity :=
    andersonTransferSL_mul_inv_eq_upperUnipotentShearSL
      lambda mass0 mass1
  relativePowersUnbounded :=
    relativeTransfer_powers_unbounded_entry hlambda hmass
  projectivelyStronglyIrreducible :=
    twoMass_isProjectivelyStronglyIrreducible (ne_of_gt hlambda) hmass
  action0Continuous :=
    continuous_normalizedTransferDirection lambda mass0
  action1Continuous :=
    continuous_normalizedTransferDirection lambda mass1
  markovContinuous :=
    continuous_twoPointProjectiveMarkovOperator lambda mass0 mass1
  fellerPreservesOne :=
    twoPointProjectiveFellerOperator_one lambda mass0 mass1
  fellerPreservesNonnegative :=
    twoPointProjectiveFellerOperator_nonnegative lambda mass0 mass1
  lawSpaceCompact :=
    isCompact_probabilityMeasure_orientedProjectiveDirection

/-- The exact remaining stationary-measure target: a fixed point of the
continuous affine two-point Markov operator. -/
def IsTwoPointProjectiveStationary
    (lambda mass0 mass1 : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection) : Prop :=
  twoPointProjectiveMarkovOperator lambda mass0 mass1 law = law

end

end ArchonPhysics.RandomMassTwoPointProjectiveMarkov

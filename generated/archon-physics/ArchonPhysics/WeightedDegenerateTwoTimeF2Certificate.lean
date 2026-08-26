import ArchonPhysics.TwoTimeConditionalThermalizationCertificate
import ArchonPhysics.TwoTimeFiniteThreeWaveKineticFamily
import ArchonPhysics.WeightedDegenerateTwoTimeKineticWindow

/-!
# Release F2 certificate from weighted degenerate relaxation

The release theorem only needs a robust lower/upper kinetic window.  This
module packages such a window without retaining the stronger assertion that
the complete real-time distance converges to zero.  A weighted decay
majorant at integer times is enough to construct the certificate.
-/

namespace ArchonPhysics.WeightedDegenerateTwoTimeF2Certificate

open ArchonPhysics
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.TwoTimeConditionalThermalizationCertificate
open ArchonPhysics.TwoTimeConditionalThermalizationCertificate.ConditionalThermalizationCertificate
open ArchonPhysics.TwoTimeKineticHittingBounds
open ArchonPhysics.WeightedDegenerateRelaxation
open MeasureTheory

noncomputable section

variable {Mode Triad Alpha : Type}
variable [Fintype Mode] [DecidableEq Mode] [Fintype Triad] [Nonempty Mode]
variable [MeasurableSpace Alpha]

/-- Concrete analytic inputs for a release-level kinetic window.  The decay
rate may approach zero; only almost-everywhere positivity is required. -/
structure WeightedReleaseContracts
    (model : FiniteCollisionModel Mode Triad)
    (trajectory : Real -> (Mode -> Real))
    (mu delta : Real) (decayMeasure : Measure Alpha)
    (rate error : Alpha -> Real) : Prop where
  mu_nonnegative : 0 <= mu
  mu_less_one : mu < 1
  threshold_positive : 0 < delta
  threshold_below_initial :
    delta < kineticEquipartitionProfile model.collisionData trajectory mu 0
  distance_continuousAt_zero : ContinuousAt
    (kineticEquipartitionProfile model.collisionData trajectory mu) 0
  rate_measurable : Measurable rate
  error_integrable : Integrable error decayMeasure
  rate_nonnegative : ∀ᵐ x ∂decayMeasure, 0 <= rate x
  rate_positive : ∀ᵐ x ∂decayMeasure, 0 < rate x
  distance_le_weightedDecay : forall n : Nat,
    kineticEquipartitionProfile model.collisionData trajectory mu (n : Real) <=
      weightedDecayIntegral decayMeasure rate error n

/-- Weighted release contracts produce the robust window required by the
two-sided release law. -/
theorem WeightedReleaseContracts.exists_robustKineticHittingWindow
    {model : FiniteCollisionModel Mode Triad}
    {trajectory : Real -> (Mode -> Real)} {mu delta : Real}
    {decayMeasure : Measure Alpha} {rate error : Alpha -> Real}
    (contracts : WeightedReleaseContracts model trajectory mu delta
      decayMeasure rate error) :
    exists lower upper : Real,
      RobustKineticHittingWindow
        (kineticEquipartitionProfile model.collisionData trajectory mu)
        delta lower upper := by
  exact
    ArchonPhysics.WeightedDegenerateTwoTimeKineticWindow.exists_robustKineticHittingWindow
      (kineticEquipartitionProfile model.collisionData trajectory mu)
      delta decayMeasure rate error contracts.threshold_positive
      contracts.threshold_below_initial contracts.distance_continuousAt_zero
      contracts.rate_measurable contracts.error_integrable
      contracts.rate_nonnegative contracts.rate_positive
      contracts.distance_le_weightedDecay

/-- Minimal release-level F2 data: a constructed global flow and one robust
window.  No unique threshold time or full real-time relaxation field is
stored. -/
structure RobustTwoTimeF2Certificate
    (model : FiniteCollisionModel Mode Triad)
    (actionZero : Mode -> Real) (mu delta : Real) where
  unitFlow : GlobalForwardCertificate model 1 actionZero
  initialEnergy_positive :
    0 < totalKineticEnergy model.frequency actionZero
  mu_nonnegative : 0 <= mu
  mu_less_one : mu < 1
  threshold_positive : 0 < delta
  lower : Real
  upper : Real
  robust_window : RobustKineticHittingWindow
    (kineticEquipartitionProfile model.collisionData unitFlow.trajectory mu)
    delta lower upper

/-- A weighted decay witness for a constructed unit-coupling flow yields the
minimal release-level F2 certificate. -/
theorem WeightedReleaseContracts.toRobustTwoTimeF2Certificate
    {model : FiniteCollisionModel Mode Triad}
    {actionZero : Mode -> Real} {mu delta : Real}
    (flow : GlobalForwardCertificate model 1 actionZero)
    (hinitialEnergy : 0 < totalKineticEnergy model.frequency actionZero)
    {decayMeasure : Measure Alpha} {rate error : Alpha -> Real}
    (contracts : WeightedReleaseContracts model flow.trajectory mu delta
      decayMeasure rate error) :
    Nonempty (RobustTwoTimeF2Certificate model actionZero mu delta) := by
  obtain ⟨lower, upper, window⟩ :=
    contracts.exists_robustKineticHittingWindow
  exact ⟨{
    unitFlow := flow
    initialEnergy_positive := hinitialEnergy
    mu_nonnegative := contracts.mu_nonnegative
    mu_less_one := contracts.mu_less_one
    threshold_positive := contracts.threshold_positive
    lower := lower
    upper := upper
    robust_window := window }⟩

/-- Construct a global forward flow and its minimal F2 certificate whenever
every such constructed flow has the stated weighted decay witness. -/
theorem exists_robustTwoTimeF2Certificate
    (model : FiniteCollisionModel Mode Triad)
    (actionZero : Mode -> Real)
    (hactionZero : forall i, 0 <= actionZero i)
    (hinitialEnergy : 0 < totalKineticEnergy model.frequency actionZero)
    (mu delta : Real)
    (decayMeasure : Measure Alpha) (rate error : Alpha -> Real)
    (hcontracts : forall flow : GlobalForwardCertificate model 1 actionZero,
      WeightedReleaseContracts model flow.trajectory mu delta
        decayMeasure rate error) :
    exists _certificate : RobustTwoTimeF2Certificate
      model actionZero mu delta, True := by
  obtain ⟨flow, _⟩ := exists_globalForwardCertificate
    model 1 actionZero hactionZero
  obtain ⟨certificate⟩ :=
    (hcontracts flow).toRobustTwoTimeF2Certificate flow hinitialEnergy
  exact ⟨certificate, trivial⟩

/-- The minimal F2 certificate composes directly with the microscopic
local-uniform F3 certificate. -/
theorem RobustTwoTimeF2Certificate.toHighProbabilityG2Bounds
    {model : FiniteCollisionModel Mode Triad}
    {actionZero : Mode -> Real} {mu delta : Real}
    (kinetic : RobustTwoTimeF2Certificate model actionZero mu delta)
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (equilibrationTime : Nat -> Real -> Omega -> ENNReal)
    (sizeCutoff : Real -> Nat)
    (microscopic : ConditionalThermalizationCertificate probability
      equilibrationTime sizeCutoff
      (kineticEquipartitionProfile model.collisionData
        kinetic.unitFlow.trajectory mu) delta) :
    HighProbabilityG2Bounds probability equilibrationTime
      sizeCutoff kinetic.lower kinetic.upper := by
  exact
    toHighProbabilityG2Bounds_of_twoTimeWindow
      probability equilibrationTime sizeCutoff
      (kineticEquipartitionProfile model.collisionData
        kinetic.unitFlow.trajectory mu)
      delta kinetic.lower kinetic.upper microscopic kinetic.robust_window

/-- Exact kinetic rescaling transports the minimal robust window to the
physical `g^-2` time window. -/
theorem RobustTwoTimeF2Certificate.physicalHittingTime_bounds
    {model : FiniteCollisionModel Mode Triad}
    {actionZero : Mode -> Real} {mu delta : Real}
    (certificate : RobustTwoTimeF2Certificate model actionZero mu delta)
    (g : Real) (hg : g ≠ 0) :
    (Real.toNNReal (certificate.lower / g ^ 2) : ENNReal) <=
        distanceThresholdHittingTime
          (kineticEquipartitionProfile model.collisionData
            (certificate.unitFlow.rescale g).trajectory mu) delta /\
      distanceThresholdHittingTime
          (kineticEquipartitionProfile model.collisionData
            (certificate.unitFlow.rescale g).trajectory mu) delta <=
        (Real.toNNReal (certificate.upper / g ^ 2) : ENNReal) := by
  have hgsq : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have hlowerPhysical : 0 < certificate.lower / g ^ 2 :=
    div_pos certificate.robust_window.lower_pos hgsq
  have hupperPositive : 0 < certificate.upper :=
    certificate.robust_window.lower_pos.trans_le
      certificate.robust_window.lower_le_upper
  have hupperPhysical : 0 < certificate.upper / g ^ 2 :=
    div_pos hupperPositive hgsq
  have hrescale (T : Real) (hT : 0 < T) :
      kineticEquipartitionProfile model.collisionData
          (certificate.unitFlow.rescale g).trajectory mu T =
        kineticEquipartitionProfile model.collisionData
          certificate.unitFlow.trajectory mu (g ^ 2 * T) := by
    exact certificate.unitFlow.kineticEquipartitionDistance_rescale
      g hg mu T certificate.mu_nonnegative certificate.mu_less_one hT
  obtain ⟨beforeMargin, hbeforeMargin, hbefore⟩ :=
    certificate.robust_window.beforeMargin
  obtain ⟨afterMargin, hafterMargin, hafter⟩ :=
    certificate.robust_window.afterMargin
  constructor
  · apply coe_toNNReal_le_distanceThresholdHittingTime_of_no_hit_before
      hlowerPhysical.le
    intro t ht htLower
    have hscaledPos : 0 < g ^ 2 * t := mul_pos hgsq ht
    have hscaledLe : g ^ 2 * t <= certificate.lower := by
      calc
        g ^ 2 * t <= g ^ 2 * (certificate.lower / g ^ 2) :=
          mul_le_mul_of_nonneg_left htLower hgsq.le
        _ = certificate.lower := by
          field_simp [hg]
    have hunit := hbefore (g ^ 2 * t) hscaledPos hscaledLe
    rw [hrescale t ht]
    linarith
  · apply distanceThresholdHittingTime_le_of_hit hupperPhysical
    have hscaledUpper :
        g ^ 2 * (certificate.upper / g ^ 2) = certificate.upper := by
      field_simp [hg]
    rw [hrescale (certificate.upper / g ^ 2) hupperPhysical,
      hscaledUpper]
    linarith

end

end ArchonPhysics.WeightedDegenerateTwoTimeF2Certificate

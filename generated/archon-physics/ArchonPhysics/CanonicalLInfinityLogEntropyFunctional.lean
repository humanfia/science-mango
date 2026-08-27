import ArchonPhysics.CanonicalLInfinityCompactEntropyRelaxation

/-!
# Canonical logarithmic entropy on positive L-infinity states

The positive-floor representative is pointwise bounded above and below by
strictly positive constants.  Its logarithm is therefore integrable against
the finite three-leg reference measure.  Compactness of a state set supplies
a common `L-infinity` radius, hence an automatic upper bound for the genuine
logarithmic entropy along every trajectory in that set.

This removes the external entropy-ceiling premise from compact relaxation.
The derivative identity along a selected kinetic trajectory remains an
explicit dynamical obligation.
-/

namespace ArchonPhysics.CanonicalLInfinityLogEntropyFunctional

open Filter MeasureTheory Metric Set
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.CanonicalLInfinityCompactEntropyRelaxation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Logarithmic entropy of the canonical representative repaired by a
strictly positive floor. -/
def canonicalLogEntropy
    (collision : ResonantThreeWaveMeasure Mode) (floor : Real)
    (action : CanonicalLInfinity collision) : Real :=
  ∫ mode, Real.log
    (positiveFloorRepresentative collision floor action mode)
      ∂collisionReferenceMeasure collision

/-- The logarithm of a positive-floor representative is integrable. -/
theorem integrable_log_positiveFloorRepresentative
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision) :
    Integrable
      (fun mode => Real.log
        (positiveFloorRepresentative collision floor action mode))
      (collisionReferenceMeasure collision) := by
  let representative :=
    positiveFloorRepresentative collision floor action
  let radius := max floor ‖action‖
  let bound := max |Real.log floor| |Real.log radius|
  have hradius : 0 < radius := hfloor.trans_le (le_max_left _ _)
  have hmeasurable : Measurable (fun mode => Real.log (representative mode)) :=
    (measurable_positiveFloorRepresentative collision floor action).log
  apply Integrable.of_bound hmeasurable.aestronglyMeasurable bound
  filter_upwards with mode
  have hrepresentativeFloor : floor ≤ representative mode :=
    floor_le_positiveFloorRepresentative collision floor action mode
  have hrepresentativePos : 0 < representative mode :=
    hfloor.trans_le hrepresentativeFloor
  have hrepresentativeRadius : representative mode ≤ radius := by
    have hnorm := norm_positiveFloorRepresentative_le
      collision hfloor.le action mode
    simpa only [representative, radius, Real.norm_eq_abs,
      abs_of_pos hrepresentativePos] using hnorm
  have hlogFloor : Real.log floor ≤ Real.log (representative mode) :=
    Real.log_le_log hfloor hrepresentativeFloor
  have hlogRadius : Real.log (representative mode) ≤ Real.log radius :=
    Real.log_le_log hrepresentativePos hrepresentativeRadius
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact (neg_le_neg (le_max_left |Real.log floor| |Real.log radius|)).trans
      ((neg_abs_le (Real.log floor)).trans hlogFloor)
  · exact hlogRadius.trans
      ((le_abs_self (Real.log radius)).trans
        (le_max_right |Real.log floor| |Real.log radius|))

/-- The true canonical log entropy is bounded above by the reference mass
times the logarithm of the common pointwise radius. -/
theorem canonicalLogEntropy_le
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision) :
    canonicalLogEntropy collision floor action ≤
      (collisionReferenceMeasure collision).real univ *
        Real.log (max floor ‖action‖) := by
  let representative :=
    positiveFloorRepresentative collision floor action
  let radius := max floor ‖action‖
  have hradius : 0 < radius := hfloor.trans_le (le_max_left _ _)
  have hintegrable :=
    integrable_log_positiveFloorRepresentative collision hfloor action
  have hconstant : Integrable (fun _ : Mode => Real.log radius)
      (collisionReferenceMeasure collision) := integrable_const _
  unfold canonicalLogEntropy
  calc
    (∫ mode, Real.log (representative mode)
        ∂collisionReferenceMeasure collision) ≤
        ∫ _mode : Mode, Real.log radius
          ∂collisionReferenceMeasure collision := by
      apply integral_mono hintegrable hconstant
      intro mode
      have hfloorMode : floor ≤ representative mode :=
        floor_le_positiveFloorRepresentative collision floor action mode
      have hpositiveMode : 0 < representative mode :=
        hfloor.trans_le hfloorMode
      apply Real.log_le_log hpositiveMode
      have hnorm := norm_positiveFloorRepresentative_le
        collision hfloor.le action mode
      simpa only [representative, radius, Real.norm_eq_abs,
        abs_of_pos hpositiveMode] using hnorm
    _ = (collisionReferenceMeasure collision).real univ *
        Real.log radius := by
      rw [integral_const]
      rfl

/-- A common `L-infinity` radius gives a common entropy ceiling. -/
theorem canonicalLogEntropy_le_of_norm_le
    (collision : ResonantThreeWaveMeasure Mode)
    {floor radius : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision) (haction : ‖action‖ ≤ radius) :
    canonicalLogEntropy collision floor action ≤
      (collisionReferenceMeasure collision).real univ *
        Real.log (max floor radius) := by
  refine (canonicalLogEntropy_le collision hfloor action).trans ?_
  apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
  apply Real.log_le_log
  · exact hfloor.trans_le (le_max_left _ _)
  · exact max_le_max_left floor haction

/-- Every compact canonical state set carries an automatically generated
uniform logarithmic-entropy ceiling. -/
theorem exists_canonicalLogEntropy_ceiling_on_compact
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (states : Set (CanonicalLInfinity collision)) (hstates : IsCompact states) :
    ∃ entropyCeiling : Real, ∀ action, action ∈ states →
      canonicalLogEntropy collision floor action ≤ entropyCeiling := by
  obtain ⟨radius, hstatesRadius⟩ :=
    hstates.isBounded.subset_closedBall
      (0 : CanonicalLInfinity collision)
  let nonnegativeRadius := max 0 radius
  refine ⟨(collisionReferenceMeasure collision).real univ *
      Real.log (max floor nonnegativeRadius), ?_⟩
  intro action haction
  apply canonicalLogEntropy_le_of_norm_le collision hfloor action
  have hclosed : action ∈ closedBall
      (0 : CanonicalLInfinity collision) radius := hstatesRadius haction
  have hnorm : ‖action‖ ≤ radius := by
    simpa only [mem_closedBall, dist_zero_right] using hclosed
  exact hnorm.trans (le_max_right 0 radius)

/-- Compact canonical entropy relaxation with its entropy and ceiling fixed by
the genuine logarithmic functional. -/
theorem tendsto_deficit_zero_of_compact_canonicalLogEntropy
    (collision : ResonantThreeWaveMeasure Mode)
    (hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision)
    {floor : Real} (hfloor : 0 < floor)
    (states : Set (CanonicalLInfinity collision)) (hstates : IsCompact states)
    (trajectory : Real -> CanonicalLInfinity collision)
    (deficit : CanonicalLInfinity collision -> Real)
    (htrajectory : forall t, 0 <= t -> trajectory t ∈ states)
    (hdeficitContinuous : ContinuousOn deficit states)
    (hactionFloor : forall action, action ∈ states ->
      AELowerBound collision floor action)
    (hdeficitEquilibrium : forall action, action ∈ states ->
      (exists scale : Real,
        ∀ᵐ mode ∂collisionReferenceMeasure collision,
          (action mode)⁻¹ = scale * collision.frequency mode) ->
      deficit action = 0)
    (hdeficitNonnegative : forall t, 0 <= t ->
      0 <= deficit (trajectory t))
    (hdeficitAntitone :
      AntitoneOn (fun t => deficit (trajectory t)) (Ici 0))
    (hentropyDeriv : forall t, 0 <= t ->
      HasDerivAt (fun s =>
        canonicalLogEntropy collision floor (trajectory s))
        (canonicalLogEntropyProduction collision floor (trajectory t)) t) :
    Tendsto (fun t => deficit (trajectory t)) atTop (nhds 0) := by
  obtain ⟨entropyCeiling, hentropyUpper⟩ :=
    exists_canonicalLogEntropy_ceiling_on_compact
      collision hfloor states hstates
  exact tendsto_deficit_zero_of_compact_canonicalEntropy
    collision hrigid hfloor states hstates trajectory deficit
      (fun t => canonicalLogEntropy collision floor (trajectory t))
      entropyCeiling htrajectory hdeficitContinuous hactionFloor
      hdeficitEquilibrium hdeficitNonnegative hdeficitAntitone
      hentropyDeriv (fun t ht => hentropyUpper (trajectory t) (htrajectory t ht))

end

end ArchonPhysics.CanonicalLInfinityLogEntropyFunctional

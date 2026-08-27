import ArchonPhysics.CompactDissipationThresholdRelaxation
import ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity
import ArchonPhysics.ResonantThreeWaveKineticLInfinityEntropyStationarity

/-!
# Compact-orbit entropy relaxation for canonical L-infinity kinetics

This module specializes compact-state threshold relaxation to the genuine
Radon--Nikodym three-wave collision map.  The continuum H-theorem supplies
nonnegativity of the dissipation, while bounded-measurable frequency-balance
rigidity classifies every zero-dissipation state.  Thus threshold coercivity
is derived rather than supplied as a separate analytic contract.
-/

namespace ArchonPhysics.CanonicalLInfinityCompactEntropyRelaxation

open Filter MeasureTheory Set
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity
open ArchonPhysics.CompactDissipationThresholdRelaxation
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticLInfinityEntropyStationarity
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The quotient-level logarithmic entropy production is nonnegative for
every positive repair floor, independently of a spectral gap. -/
theorem canonicalLogEntropyProduction_nonnegative
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision) :
    0 <= canonicalLogEntropyProduction collision floor action := by
  unfold canonicalLogEntropyProduction
  exact continuumLogEntropyProduction_nonneg collision fun mode =>
    hfloor.trans_le
      (floor_le_positiveFloorRepresentative collision floor action mode)

/-- On a compact positive state set, continuum balance rigidity turns the
H-theorem equality case into a positive entropy-production minimum on every
positive level of any continuous equilibrium deficit. -/
theorem exists_pos_canonicalEntropyProduction_lower_bound_on_compact_level
    (collision : ResonantThreeWaveMeasure Mode)
    (hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision)
    {floor : Real} (hfloor : 0 < floor)
    (states : Set (CanonicalLInfinity collision)) (hstates : IsCompact states)
    (deficit : CanonicalLInfinity collision -> Real)
    (hdeficitContinuous : ContinuousOn deficit states)
    (hactionFloor : forall action, action ∈ states ->
      AELowerBound collision floor action)
    (hdeficitEquilibrium : forall action, action ∈ states ->
      (exists scale : Real,
        ∀ᵐ mode ∂collisionReferenceMeasure collision,
          (action mode)⁻¹ = scale * collision.frequency mode) ->
      deficit action = 0)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists kappa : Real, 0 < kappa /\
      forall action, action ∈ states -> epsilon <= deficit action ->
        kappa <= canonicalLogEntropyProduction collision floor action := by
  apply exists_pos_dissipation_lower_bound_on_compact_level
    states hstates deficit
      (canonicalLogEntropyProduction collision floor)
      hdeficitContinuous
        (continuousOn_canonicalLogEntropyProduction collision hfloor states)
  · intro action _haction
    exact canonicalLogEntropyProduction_nonnegative
      collision hfloor action
  · intro action haction hzero
    obtain ⟨_hstationary, scale, hscale⟩ :=
      stationary_and_inverseAction_ae_proportional_of_canonicalEntropy_eq_zero
        collision hrigid hfloor action (hactionFloor action haction) hzero
    exact hdeficitEquilibrium action haction ⟨scale, hscale⟩
  · exact hepsilon

/-- A compact positive kinetic orbit relaxes for every continuous deficit
which vanishes on the rigid Rayleigh--Jeans equality class.  The conclusion
uses no assumed threshold coercivity and no uniform collision spectral gap. -/
theorem tendsto_deficit_zero_of_compact_canonicalEntropy
    (collision : ResonantThreeWaveMeasure Mode)
    (hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision)
    {floor : Real} (hfloor : 0 < floor)
    (states : Set (CanonicalLInfinity collision)) (hstates : IsCompact states)
    (trajectory : Real -> CanonicalLInfinity collision)
    (deficit : CanonicalLInfinity collision -> Real)
    (entropy : Real -> Real) (entropyCeiling : Real)
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
      HasDerivAt entropy
        (canonicalLogEntropyProduction collision floor (trajectory t)) t)
    (hentropyUpper : forall t, 0 <= t ->
      entropy t <= entropyCeiling) :
    Tendsto (fun t => deficit (trajectory t)) atTop (nhds 0) := by
  apply tendsto_deficit_zero_of_compact_state_dissipation
    states hstates trajectory deficit
      (canonicalLogEntropyProduction collision floor)
      entropy entropyCeiling htrajectory hdeficitContinuous
      (continuousOn_canonicalLogEntropyProduction collision hfloor states)
  · intro action _haction
    exact canonicalLogEntropyProduction_nonnegative
      collision hfloor action
  · intro action haction hzero
    obtain ⟨_hstationary, scale, hscale⟩ :=
      stationary_and_inverseAction_ae_proportional_of_canonicalEntropy_eq_zero
        collision hrigid hfloor action (hactionFloor action haction) hzero
    exact hdeficitEquilibrium action haction ⟨scale, hscale⟩
  · exact hdeficitNonnegative
  · exact hdeficitAntitone
  · exact hentropyDeriv
  · exact hentropyUpper

end

end ArchonPhysics.CanonicalLInfinityCompactEntropyRelaxation

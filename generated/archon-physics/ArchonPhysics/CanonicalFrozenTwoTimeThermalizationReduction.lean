import ArchonPhysics.AETwoTimeProbabilisticHittingTransfer
import ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction

/-!
# Canonical frozen two-time thermalization reduction

The release-level inverse-square law needs only a robust lower/upper kinetic
window.  Combining the canonical local-uniform approximation package with the
almost-everywhere hitting-time identification transfers such a window directly
to the frozen random-mass microscopic model.  No unique crossing time or strict
monotonicity is assumed.
-/

namespace ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction

open ArchonPhysics
open ArchonPhysics.AETwoTimeProbabilisticHittingTransfer
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.TwoTimeKineticHittingBounds
open Filter MeasureTheory Set Topology

noncomputable section

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

/-- A canonical microscopic kinetic-window approximation and a robust
two-time kinetic window imply the high-probability `g⁻²` law for the actual
frozen late-window hitting time. -/
theorem KineticWindowApproximation.toHighProbabilityG2Bounds_of_twoTimeWindow
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} (hmu0 : 0 ≤ mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8)
    {sizeCutoff : Real → Nat} {kineticDistance : Real → Real}
    (certificate : KineticWindowApproximation kappa beta hbeta mu delta
      sizeCutoff kineticDistance)
    {lower upper : Real}
    (window : RobustKineticHittingWindow
      kineticDistance delta lower upper) :
    HighProbabilityG2Bounds
      canonicalIIDMassPhaseEnsemble.probability
      (measurableClosedEquilibrationTime
        kappa beta hbeta mu delta)
      sizeCutoff lower upper := by
  refine ⟨window.lower_pos, window.lower_le_upper, ?_, ?_⟩
  · intro n g
    exact measurable_measurableClosedEquilibrationTime
      kappa beta hbeta mu delta n g
  · intro jointLimit
    have hwindow : Tendsto
        (fun j => canonicalIIDMassPhaseEnsemble.probability
          ((fun omega => scaledEquilibrationTime
            (measurableClosedEquilibrationTime
              kappa beta hbeta mu delta)
            (jointLimit.systemSize j) (jointLimit.coupling j) omega) ⁻¹'
              Icc (Real.toNNReal lower : ENNReal)
                (Real.toNNReal upper : ENNReal)))
        atTop (nhds 1) := by
      apply
        random_local_uniform_error_implies_ae_identified_twoTime_window
          canonicalIIDMassPhaseEnsemble.probability
          (fun j omega => scaledDistance kappa beta hbeta mu
            (jointLimit.systemSize j) (jointLimit.coupling j) omega)
          (fun j omega => certificate.localUniformError upper
            (jointLimit.systemSize j) (jointLimit.coupling j) omega)
          (fun j omega => scaledEquilibrationTime
            (measurableClosedEquilibrationTime
              kappa beta hbeta mu delta)
            (jointLimit.systemSize j) (jointLimit.coupling j) omega)
          delta lower upper window
      · exact certificate.localUniformError_convergesInProbability
          jointLimit upper
          (window.lower_pos.trans_le window.lower_le_upper)
      · intro eta heta j omega hsmall
        exact certificate.localUniformError_controls
          jointLimit upper eta
          (window.lower_pos.trans_le window.lower_le_upper)
          heta j omega hsmall
      · intro j
        exact scaled_measurableClosedEquilibrationTime_eq_hittingTime_ae
          kappa beta hbeta mu delta hmu0 hmu1 hdelta
          (jointLimit.systemSize j) (jointLimit.coupling j)
          (ne_of_gt (jointLimit.coupling_pos j))
    simpa only [scalingWindowEvent, ENNReal.ofReal] using hwindow

end

end ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction

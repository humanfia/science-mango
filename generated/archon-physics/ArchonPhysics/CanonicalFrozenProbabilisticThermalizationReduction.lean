import ArchonPhysics.AEIdentifiedHittingTimeTransfer
import ArchonPhysics.CanonicalFrozenClosedHittingRescaling

/-!
# Canonical frozen probabilistic thermalization reduction

For the frozen quarter-profile random-mass lattice, finite-model
measurability, the true closed-threshold semantics, and exact kinetic-time
rescaling are already kernel-checked.  This module packages only the genuinely
dynamical input still needed by the probability transfer: a local-uniform
microscopic-to-kinetic error gauge along every admissible joint limit.

Once that gauge vanishes in probability and controls the canonical scaled
distance, any robust crossing of the supplied kinetic distance yields the
full `g² T_eq` convergence law and its high-probability two-sided bounds.
-/

namespace ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.ThermalizationTransfer

noncomputable section

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

/-- The sole microscopic convergence package remaining after the canonical
finite-model and hitting-time fields have been discharged. -/
structure KineticWindowApproximation
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (sizeCutoff : Real → Nat)
    (kineticDistance : Real → Real) where
  /-- A measurable finite-model bound for local-uniform distance error. -/
  localUniformError :
    Real → Nat → Real → RandomEnsemble.SampleSpace → ENNReal
  localUniformError_measurable :
    ∀ s : AdmissibleJointLimit sizeCutoff, ∀ T j,
      Measurable
        (localUniformError T (s.systemSize j) (s.coupling j))
  /-- The bound vanishes in probability on every positive compact window. -/
  localUniformError_zero_law :
    ∀ s : AdmissibleJointLimit sizeCutoff, ∀ T, 0 < T →
      ∀ U : Set ENNReal, MeasurableSet U → U ∈ nhds 0 →
        Tendsto
          (fun j => canonicalIIDMassPhaseEnsemble.probability
            ((localUniformError T
              (s.systemSize j) (s.coupling j)) ⁻¹' U))
          atTop (nhds 1)
  /-- Small error controls the actual frozen distance at physical time
  `tau / g²`, uniformly on the requested kinetic window. -/
  localUniformError_controls :
    ∀ s : AdmissibleJointLimit sizeCutoff,
      ∀ T eta, 0 < T → 0 < eta → ∀ j omega,
        localUniformError T (s.systemSize j) (s.coupling j) omega <
            ENNReal.ofReal eta →
          UniformlyCloseOnNonnegativeWindow
            (scaledDistance kappa beta hbeta mu
              (s.systemSize j) (s.coupling j) omega)
            kineticDistance T eta

/-- The error package supplies the generic neighbourhood definition of
convergence in probability to zero. -/
theorem KineticWindowApproximation.localUniformError_convergesInProbability
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real → Nat}
    {kineticDistance : Real → Real}
    (certificate : KineticWindowApproximation kappa beta hbeta mu delta
      sizeCutoff kineticDistance)
    (s : AdmissibleJointLimit sizeCutoff) (T : Real) (hT : 0 < T) :
    ConvergesInProbabilityTo
      canonicalIIDMassPhaseEnsemble.probability
      (fun j omega => certificate.localUniformError T
        (s.systemSize j) (s.coupling j) omega) 0 := by
  constructor
  · intro j
    exact certificate.localUniformError_measurable s T j
  · exact certificate.localUniformError_zero_law s T hT

/-- For the exact frozen model, local-uniform kinetic-window convergence and
a robust kinetic crossing imply convergence in probability of `g² T_eq`.
No additional measurability, spectral simplicity, or hitting-time
identification premise remains. -/
theorem KineticWindowApproximation.toG2TeqConvergesInProbability
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} (hmu0 : 0 ≤ mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8)
    {sizeCutoff : Real → Nat} {kineticDistance : Real → Real}
    (certificate : KineticWindowApproximation kappa beta hbeta mu delta
      sizeCutoff kineticDistance)
    {tauStar : Real}
    (hcross : RobustKineticFirstCrossing kineticDistance delta tauStar) :
    G2TeqConvergesInProbability
      canonicalIIDMassPhaseEnsemble.probability
      (measurableClosedEquilibrationTime
        kappa beta hbeta mu delta)
      sizeCutoff tauStar := by
  refine ⟨hcross.tauStar_pos, ?_, ?_⟩
  · intro n g
    exact measurable_measurableClosedEquilibrationTime
      kappa beta hbeta mu delta n g
  · intro s
    apply random_local_uniform_error_implies_ae_identified_hitting_time_convergence
      canonicalIIDMassPhaseEnsemble.probability
      (fun j omega => scaledDistance kappa beta hbeta mu
        (s.systemSize j) (s.coupling j) omega)
      (fun T j omega => certificate.localUniformError T
        (s.systemSize j) (s.coupling j) omega)
      (fun j omega => scaledEquilibrationTime
        (measurableClosedEquilibrationTime
          kappa beta hbeta mu delta)
        (s.systemSize j) (s.coupling j) omega)
      delta tauStar hcross
    · intro T hT
      exact certificate.localUniformError_convergesInProbability s T hT
    · intro T eta hT heta j omega hsmall
      exact certificate.localUniformError_controls
        s T eta hT heta j omega hsmall
    · intro j
      apply measurable_scaledEquilibrationTime
      exact measurable_measurableClosedEquilibrationTime
        kappa beta hbeta mu delta (s.systemSize j) (s.coupling j)
    · intro j
      exact scaled_measurableClosedEquilibrationTime_eq_hittingTime_ae
        kappa beta hbeta mu delta hmu0 hmu1 hdelta
        (s.systemSize j) (s.coupling j)
        (ne_of_gt (s.coupling_pos j))

/-- The high-probability inverse-square window is now an immediate corollary
of the same canonical reduction. -/
theorem KineticWindowApproximation.toHighProbabilityG2Bounds
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} (hmu0 : 0 ≤ mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8)
    {sizeCutoff : Real → Nat} {kineticDistance : Real → Real}
    (certificate : KineticWindowApproximation kappa beta hbeta mu delta
      sizeCutoff kineticDistance)
    {tauStar lower upper : Real}
    (hcross : RobustKineticFirstCrossing kineticDistance delta tauStar)
    (hlower0 : 0 < lower) (hlower : lower < tauStar)
    (hupper : tauStar < upper) :
    HighProbabilityG2Bounds
      canonicalIIDMassPhaseEnsemble.probability
      (measurableClosedEquilibrationTime
        kappa beta hbeta mu delta)
      sizeCutoff lower upper := by
  exact G2TeqConvergesInProbability.toHighProbabilityG2Bounds
    canonicalIIDMassPhaseEnsemble.probability
    (measurableClosedEquilibrationTime kappa beta hbeta mu delta)
    sizeCutoff tauStar lower upper
    (certificate.toG2TeqConvergesInProbability
      hmu0 hmu1 hdelta hcross)
    hlower0 hlower hupper

end

end ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction

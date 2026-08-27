import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
import ArchonPhysics.ActualSixSiteNearResonantJacobianCompleteWitness

/-!
# Polynomial avoidance for the six-site weighted near-resonance witness

A nonzero collision weight at one fixed path parameter does not, by
continuity alone, produce nonzero weights arbitrarily close to the clean
endpoint.  The missing algebraic input is a parameter-elimination
polynomial: vanishing of the on-shell dual-adjugate contraction must force
the path parameter to be a root of one fixed nonzero polynomial.

This module isolates that exact interface and proves the rest of the
argument.  In particular, a certificate whose polynomial is nonzero at
`t = 1 / 10` has only finitely many exceptional parameters.  Every
neighborhood of zero therefore contains a positive parameter which
simultaneously has small mismatch, simple spectrum, nonzero lifted
Jacobian, and strictly positive normalized collision weight.

The structure below is not an assumption hidden in the final statement:
constructing its value from the explicit quotient/resultant computation is
the remaining certificate obligation.
-/

open scoped BigOperators Matrix Polynomial

namespace ArchonPhysics.ActualSixSiteNearResonantCollisionPolynomialAvoidance

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor
open ArchonPhysics.ActualSixSiteNearResonantDisplayedDetWitness
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness
open ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
open ArchonPhysics.ActualSixSiteNearResonantProjectorBridge
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Set

noncomputable section

/-- A nonzero real polynomial can be avoided inside every nonempty positive
interval. -/
theorem exists_pos_lt_eval_ne_zero (P : Real[X]) (hP : P ≠ 0)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ t : Real, 0 < t ∧ t < delta ∧ P.eval t ≠ 0 := by
  have hroots : Set.Finite {t : Real | P.eval t = 0} := by
    simpa only [Polynomial.IsRoot] using
      (Polynomial.finite_setOfPred_isRoot hP)
  have hremaining :
      (Set.Ioo (0 : Real) delta \ {t : Real | P.eval t = 0}).Infinite :=
    (Set.Ioo_infinite hdelta).sdiff hroots
  obtain ⟨t, ht⟩ := hremaining.nonempty
  exact ⟨t, ht.1.1, ht.1.2, ht.2⟩

/-- Exact interface required from a generic quotient/resultant computation.

The specialization field makes the exceptional polynomial genuinely
nonzero.  The soundness field is the substantive elimination statement:
at supported, pole-free path points, an on-shell zero of the selected
dual-adjugate contraction forces a zero of the parameter polynomial. -/
structure ActualSixSiteCollisionEliminationCertificate where
  exceptionalPolynomial : Real[X]
  eval_oneTenth_ne_zero :
    exceptionalPolynomial.eval (1 / 10 : Real) ≠ 0
  contraction_zero_implies_eval_zero : ∀ {t : Real},
    nearResonantMassTriple t ∈ iidMassTripleSupport →
    1 - t ^ 2 ≠ 0 →
    harmonicDualOrderedAdjugateInteractionContraction
        (actualSixSiteThreeMassConfig (nearResonantMassTriple t))
        cleanSixSiteDecayModes = 0 →
    exceptionalPolynomial.eval t = 0

theorem ActualSixSiteCollisionEliminationCertificate.polynomial_ne_zero
    (certificate : ActualSixSiteCollisionEliminationCertificate) :
    certificate.exceptionalPolynomial ≠ 0 := by
  intro hzero
  apply certificate.eval_oneTenth_ne_zero
  rw [hzero]
  simp

/-- Pathwise version of the lifted-Jacobian bridge.  Keeping the path
parameter exposed lets polynomial avoidance choose a point satisfying the
collision and Jacobian nondegeneracy conditions simultaneously. -/
theorem actualSixSitePath_liftedJacobian_det_ne_zero
    {t : Real} (ht : 0 < t)
    (hinterior : nearResonantMassTriple t ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)))
    (hresidual : actualSixSiteNearResonantAdjugateResidualPath t ≠ 0)
    (hpole : 1 - t ^ 2 ≠ 0) :
    (actualThreeMassLiftedFrequencyJacobian frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
      actualFourSiteDecaySign cleanSixSiteDecayModes
      (nearResonantMassTriple t)).det ≠ 0 := by
  have hprod : (1 - t) * (1 + t) ≠ 0 := by
    rw [show (1 - t) * (1 + t) = 1 - t ^ 2 by ring]
    exact hpole
  have hminus : t - 1 ≠ 0 := by
    have hleft : 1 - t ≠ 0 := (mul_ne_zero_iff.mp hprod).1
    intro h
    apply hleft
    linarith
  have hplus : t + 1 ≠ 0 := by
    have hright : 1 + t ≠ 0 := (mul_ne_zero_iff.mp hprod).2
    intro h
    apply hright
    linarith
  have hdisplayed :
      (nearResonantAdjugateWeightMatrix t
        (actualSixSiteNearResonantSelectedEnergy t)).det ≠ 0 :=
    nearResonantAdjugateWeightMatrix_det_ne_zero_of_path
      (ne_of_gt ht) hsimple hresidual hpole
  have hdisplayedDual :
      (nearResonantAdjugateWeightMatrix t
        (actualSixSiteSelectedDualEnergy cleanSixSiteDecayModes
          (nearResonantMassTriple t))).det ≠ 0 := by
    rw [actualSixSiteSelectedDualEnergy_cleanDecay_eq]
    exact hdisplayed
  have hprojector :
      (actualThreeMassProjectorWeightMatrix frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        cleanSixSiteDecayModes (nearResonantMassTriple t)).det ≠ 0 :=
    actualSixSitePath_projectorMinor_ne_zero_of_nearResonantAdjugate
      cleanSixSiteDecayModes (interior_subset hinterior) hsimple
      hminus hplus hdisplayedDual
  have hsimplePhysical : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        (nearResonantMassTriple t)) := by
    simpa [actualSixSiteThreeMassHarmonic] using hsimple
  have hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        (nearResonantMassTriple t)) (cleanSixSiteDecayModes r) := by
    intro r
    simpa [actualSixSiteThreeMassHarmonic] using
      actualSixSiteDecayModes_energy_pos_of_simple
        (nearResonantMassTriple t) hsimple r
  exact
    (actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      frozenUnitMassSix (by decide) (by decide) (by decide)
      actualFourSiteDecaySign cleanSixSiteDecayModes hinterior
      hsimplePhysical hpositive).2 hprojector

/-- Once the generic elimination certificate is supplied, every positive
mismatch tolerance admits one positive path parameter satisfying all four
physical regularity conditions simultaneously. -/
theorem exists_actualSixSiteNearResonant_weightedJacobianWitness
    (certificate : ActualSixSiteCollisionEliminationCertificate)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ t : Real,
      0 < t ∧
      nearResonantMassTriple t ∈ interior iidMassTripleSupport ∧
      abs (actualSixSiteNearResonantMismatchPath t) < epsilon ∧
      SimpleOrderedSpectrum
        (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)) ∧
      (actualThreeMassLiftedFrequencyJacobian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        actualFourSiteDecaySign cleanSixSiteDecayModes
        (nearResonantMassTriple t)).det ≠ 0 ∧
      0 < harmonicOrderedNormalizedInteractionWeight
        (actualSixSiteThreeMassConfig (nearResonantMassTriple t))
        cleanSixSiteDecayModes := by
  have heventually : ∀ᶠ t in nhds (0 : Real),
      nearResonantMassTriple t ∈ interior iidMassTripleSupport ∧
      abs (actualSixSiteNearResonantMismatchPath t) < epsilon ∧
      actualSixSiteNearResonantAdjugateResidualPath t ≠ 0 ∧
      1 - t ^ 2 ≠ 0 := by
    filter_upwards [eventually_nearResonantMassTriple_mem_interior,
      eventually_actualSixSiteNearResonantMismatchPath_lt hepsilon,
      eventually_actualSixSiteNearResonantAdjugateResidualPath_ne_zero,
      eventually_nearResonantPath_avoids_poles] with t hinterior hmismatch
        hresidual hpole
    exact ⟨hinterior, hmismatch, hresidual, hpole⟩
  rcases Metric.mem_nhds_iff.mp heventually with
    ⟨delta, hdelta, hball⟩
  obtain ⟨t, htpos, htdelta, hpoly⟩ :=
    exists_pos_lt_eval_ne_zero certificate.exceptionalPolynomial
      certificate.polynomial_ne_zero hdelta
  have htball : t ∈ Metric.ball (0 : Real) delta := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact htdelta
  have hdata := hball htball
  have hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport :=
    interior_subset hdata.1
  have hsimple : SimpleOrderedSpectrum
      (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)) :=
    actualSixSiteNearResonant_simpleOrderedSpectrum
      (ne_of_gt htpos) hsupport hdata.2.2.2
  have hcontraction :
      harmonicDualOrderedAdjugateInteractionContraction
        (actualSixSiteThreeMassConfig (nearResonantMassTriple t))
        cleanSixSiteDecayModes ≠ 0 := by
    intro hzero
    apply hpoly
    exact certificate.contraction_zero_implies_eval_zero
      hsupport hdata.2.2.2 hzero
  have hsimpleHarmonic : SimpleOrderedSpectrum
      (harmonicHermitian
        (actualSixSiteThreeMassConfig (nearResonantMassTriple t))) := by
    simpa [actualSixSiteThreeMassHarmonic, actualSixSiteThreeMassConfig,
      threeMassHarmonicHermitian] using hsimple
  have hfrequency : ∀ r, 0 < orderedModeFrequency
      (harmonicHermitian
        (actualSixSiteThreeMassConfig (nearResonantMassTriple t)))
      (cleanSixSiteDecayModes r) := by
    intro r
    rw [orderedModeFrequency]
    exact Real.sqrt_pos.2 (by
      simpa [actualSixSiteThreeMassHarmonic, actualSixSiteThreeMassConfig,
        threeMassHarmonicHermitian] using
          actualSixSiteDecayModes_energy_pos_of_simple
            (nearResonantMassTriple t) hsimple r)
  have hweight : 0 < harmonicOrderedNormalizedInteractionWeight
      (actualSixSiteThreeMassConfig (nearResonantMassTriple t))
      cleanSixSiteDecayModes :=
    harmonicOrderedNormalizedInteractionWeight_pos_of_dualAdjugateContraction_ne_zero
      (actualSixSiteThreeMassConfig (nearResonantMassTriple t))
      hsimpleHarmonic cleanSixSiteDecayModes hfrequency hcontraction
  have hjacobian := actualSixSitePath_liftedJacobian_det_ne_zero
    htpos hdata.1 hsimple hdata.2.2.1 hdata.2.2.2
  exact ⟨t, htpos, hdata.1, hdata.2.1, hsimple, hjacobian, hweight⟩

end

end ArchonPhysics.ActualSixSiteNearResonantCollisionPolynomialAvoidance

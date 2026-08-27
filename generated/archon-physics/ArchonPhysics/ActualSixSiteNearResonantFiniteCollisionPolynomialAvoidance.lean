import ArchonPhysics.ActualSixSiteNearResonantCollisionPolynomialAvoidance
import ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge

/-!
# Finite-coordinate elimination interface for the six-site witness

This adapter states the remaining elimination obligation entirely in terms
of the literal `Fin 6` shifted-adjugate contraction and transports any such
certificate to the physical collision-weight avoidance theorem.
-/

open scoped Matrix Polynomial

namespace ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionPolynomialAvoidance

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantCollisionPolynomialAvoidance
open ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantProjectorBridge
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- The computational form of the generic elimination certificate. -/
structure ActualSixSiteFiniteCollisionEliminationCertificate where
  exceptionalPolynomial : Real[X]
  eval_oneTenth_ne_zero :
    exceptionalPolynomial.eval (1 / 10 : Real) ≠ 0
  finiteContraction_zero_implies_eval_zero : ∀ {t : Real},
    nearResonantMassTriple t ∈ iidMassTripleSupport →
    1 - t ^ 2 ≠ 0 →
    sixSiteNearResonantFiniteAdjugateInteractionContraction t
        (actualSixSiteSelectedDualEnergy cleanSixSiteDecayModes
          (nearResonantMassTriple t)) = 0 →
    exceptionalPolynomial.eval t = 0

/-- Transport a literal finite-coordinate certificate to the physical
dual-adjugate certificate consumed by polynomial avoidance. -/
def ActualSixSiteFiniteCollisionEliminationCertificate.toPhysical
    (certificate : ActualSixSiteFiniteCollisionEliminationCertificate) :
    ActualSixSiteCollisionEliminationCertificate where
  exceptionalPolynomial := certificate.exceptionalPolynomial
  eval_oneTenth_ne_zero := certificate.eval_oneTenth_ne_zero
  contraction_zero_implies_eval_zero := by
    intro t hsupport hpole hzero
    apply certificate.finiteContraction_zero_implies_eval_zero
      hsupport hpole
    rw [← harmonicDualOrderedAdjugateInteractionContraction_eq_finite
      hsupport]
    exact hzero

/-- A finite-coordinate elimination certificate closes the complete
arbitrarily-small weighted-Jacobian path witness. -/
theorem exists_actualSixSiteNearResonant_weightedJacobianWitness_of_finiteCertificate
    (certificate : ActualSixSiteFiniteCollisionEliminationCertificate)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ t : Real,
      0 < t ∧
      nearResonantMassTriple t ∈ interior iidMassTripleSupport ∧
      abs (ActualSixSiteNearResonantPathResidualWitness.actualSixSiteNearResonantMismatchPath t) <
        epsilon ∧
      OrderedSingleModeProjector.SimpleOrderedSpectrum
        (ActualSixSiteThreeMassSimpleSpectrum.actualSixSiteThreeMassHarmonic
          (nearResonantMassTriple t)) ∧
      (ActualThreeMassLiftedSpectralChart.actualThreeMassLiftedFrequencyJacobian
        ActualSixSiteCleanDecayResonancePatch.frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        ActualThreeMassLiftedJacobianPolynomial.actualFourSiteDecaySign
        cleanSixSiteDecayModes (nearResonantMassTriple t)).det ≠ 0 ∧
      0 < MeasurableOrderedModeCoupling.Harmonic.harmonicOrderedNormalizedInteractionWeight
        (ActualSixSiteThreeMassSimpleSpectrum.actualSixSiteThreeMassConfig
          (nearResonantMassTriple t)) cleanSixSiteDecayModes :=
  exists_actualSixSiteNearResonant_weightedJacobianWitness
    certificate.toPhysical hepsilon

end

end ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionPolynomialAvoidance

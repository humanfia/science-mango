import ArchonPhysics.ActualSixSiteNearResonantFixedScaledCollisionMatrixBridge
import ArchonPhysics.ActualSixSiteNearResonantIntegralDeterminantConclusion
import ArchonPhysics.ActualSixSiteNearResonantScaledCompanionActualSoundness

/-!
# Concrete finite collision-elimination certificate

The scaled companion determinant is specialized at `t = 1 / 10` and
identified with the rational residual multiplication matrix.  Its certified
nonsingularity supplies the nonzero field of the finite-coordinate
elimination certificate; actual-mode soundness supplies the other field.
-/

open scoped Matrix Polynomial

namespace ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionEliminationCertificate

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness
open ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionPolynomialAvoidance
open ArchonPhysics.ActualSixSiteNearResonantFixedScaledCollisionMatrixBridge
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanionActualSoundness
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanionElimination
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

set_option maxRecDepth 100000 in
/-- Nonsingularity of the rational residual multiplication operator survives
the coefficient embedding from `Rat` to `Real`. -/
theorem residualMultiplicationRat_map_real_det_ne_zero :
    ((Rat.castHom Real).mapMatrix
      ModularCertificate.residualMultiplicationRat).det ≠ 0 := by
  rw [← RingHom.map_det]
  intro hzero
  apply ModularCertificate.residualMultiplicationRat_det_ne_zero
  apply Rat.cast_injective (α := Real)
  simpa using hzero

/-- The scaled exceptional polynomial is nonzero at the fixed physical point
`t = 1 / 10`. -/
theorem scaledCollisionExceptionalPolynomial_eval_oneTenth_ne_zero :
    scaledCollisionExceptionalPolynomial.eval (1 / 10 : Real) ≠ 0 := by
  rw [evaluate_scaledCollisionExceptionalPolynomial,
    scaledCollisionMultiplicationMatrix_oneTenth_eq_residualMultiplication,
    Matrix.det_smul]
  exact mul_ne_zero (by positivity)
    residualMultiplicationRat_map_real_det_ne_zero

/-- The concrete finite-coordinate elimination certificate for the selected
six-site near-resonant path. -/
def actualSixSiteFiniteCollisionEliminationCertificate :
    ActualSixSiteFiniteCollisionEliminationCertificate where
  exceptionalPolynomial := scaledCollisionExceptionalPolynomial
  eval_oneTenth_ne_zero :=
    scaledCollisionExceptionalPolynomial_eval_oneTenth_ne_zero
  finiteContraction_zero_implies_eval_zero := by
    intro t hsupport hpole hzero
    exact actualSixSiteFiniteContraction_zero_implies_exceptional_eval_zero
      hsupport hpole hzero

/-- The concrete finite certificate closes the full arbitrarily-small
weighted-Jacobian witness. -/
theorem exists_actualSixSiteNearResonant_weightedJacobianWitness_of_finiteCertificate
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ t : Real,
      0 < t ∧
      nearResonantMassTriple t ∈ interior iidMassTripleSupport ∧
      abs (actualSixSiteNearResonantMismatchPath t) < epsilon ∧
      SimpleOrderedSpectrum
        (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)) ∧
      (ActualThreeMassLiftedSpectralChart.actualThreeMassLiftedFrequencyJacobian
        frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        ActualThreeMassLiftedJacobianPolynomial.actualFourSiteDecaySign
        cleanSixSiteDecayModes (nearResonantMassTriple t)).det ≠ 0 ∧
      0 < harmonicOrderedNormalizedInteractionWeight
        (actualSixSiteThreeMassConfig (nearResonantMassTriple t))
        cleanSixSiteDecayModes :=
  ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionPolynomialAvoidance.exists_actualSixSiteNearResonant_weightedJacobianWitness_of_finiteCertificate
    actualSixSiteFiniteCollisionEliminationCertificate hepsilon

end

end ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionEliminationCertificate

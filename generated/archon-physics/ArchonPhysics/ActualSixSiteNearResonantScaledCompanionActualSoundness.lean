import ArchonPhysics.ActualSixSiteNearResonantScaledCompanionEliminationSoundness
import ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionPolynomialAvoidance

/-!
# Soundness specialized to the actual selected six-site modes

The abstract quotient-norm soundness theorem assumes that the three energy
parameters lie on the path quintic.  Here that premise is discharged for the
actual ordered modes `[0,3,4]`, including the repeated-spectrum endpoint
`t = 0`.
-/

open scoped Matrix Polynomial

namespace ArchonPhysics.ActualSixSiteNearResonantScaledCompanionActualSoundness

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionPolynomialAvoidance
open ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness
open ArchonPhysics.ActualSixSiteNearResonantPathSeparable
open ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
open ArchonPhysics.ActualSixSiteNearResonantProjectorBridge
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanionElimination
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanionEliminationSoundness
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- Every selected dual energy is a root of the nonzero-mode quintic.  At
`t = 0` this follows from the explicit spectrum `[4,1,1]`; away from zero it
follows from the physical characteristic equation and positivity of modes
`[0,3,4]`. -/
theorem actualSixSiteSelectedDualEnergy_quintic_root
    {t : Real}
    (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0) (r : Fin 3) :
    (nearResonantPathQuintic (t ^ 2)).eval
        (actualSixSiteSelectedDualEnergy cleanSixSiteDecayModes
          (nearResonantMassTriple t) r) = 0 := by
  rw [actualSixSiteSelectedDualEnergy_cleanDecay_eq]
  by_cases ht : t = 0
  · subst t
    rw [actualSixSiteNearResonantSelectedEnergy_zero]
    fin_cases r <;> norm_num [nearResonantPathQuintic]
  · have hsimple := actualSixSiteNearResonant_simpleOrderedSpectrum
      ht hsupport hpole
    have hpositive :
        0 < actualSixSiteNearResonantSelectedEnergy t r := by
      simpa [actualSixSiteNearResonantSelectedEnergy] using
        actualSixSiteDecayModes_energy_pos_of_simple
          (nearResonantMassTriple t) hsimple r
    have hchar := charpoly_eval_orderedEigenvalue_eq_zero
      (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t))
      (cleanSixSiteDecayModes r)
    change (Matrix.charpoly
      (Matrix.of (actualSixSiteThreeMassHarmonic
        (nearResonantMassTriple t)).val)).eval
      (actualSixSiteNearResonantSelectedEnergy t r) = 0 at hchar
    rw [actualSixSiteNearResonant_charpoly_eval hsupport hpole] at hchar
    have hfactor :
        actualSixSiteNearResonantSelectedEnergy t r /
            (1 - t ^ 2) ≠ 0 :=
      div_ne_zero (ne_of_gt hpositive) hpole
    have hquintic := (mul_eq_zero.mp hchar).resolve_left hfactor
    simpa [actualSixSiteNearResonantSelectedEnergy,
      nearResonantPathQuintic, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow] using hquintic

/-- The quotient determinant supplies the soundness field of the concrete
finite collision-elimination certificate.  The only remaining field for the
full certificate is the separately computed nonvanishing at `t = 1/10`. -/
theorem actualSixSiteFiniteContraction_zero_implies_exceptional_eval_zero
    {t : Real}
    (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0)
    (hzero :
      sixSiteNearResonantFiniteAdjugateInteractionContraction t
        (actualSixSiteSelectedDualEnergy cleanSixSiteDecayModes
          (nearResonantMassTriple t)) = 0) :
    scaledCollisionExceptionalPolynomial.eval t = 0 := by
  apply finiteContraction_zero_implies_exceptional_eval_zero
    (actualSixSiteSelectedDualEnergy cleanSixSiteDecayModes
      (nearResonantMassTriple t))
  · exact actualSixSiteSelectedDualEnergy_quintic_root hsupport hpole
  · exact hpole
  · exact hzero

end


end ArchonPhysics.ActualSixSiteNearResonantScaledCompanionActualSoundness

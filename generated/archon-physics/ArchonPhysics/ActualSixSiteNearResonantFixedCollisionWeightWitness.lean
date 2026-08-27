import ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionEliminationCertificate

/-!
# Fixed rational six-site collision-weight witness

The modular determinant certificate is nonzero at the explicit path parameter
t = 1/10. Soundness therefore makes the physical dual-adjugate contraction
nonzero at that same point, which yields a strictly positive
frequency-normalized interaction weight.
-/

namespace ArchonPhysics.ActualSixSiteNearResonantFixedCollisionWeightWitness

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionEliminationCertificate
open ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
open ArchonPhysics.ActualSixSiteNearResonantProjectorBridge
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanionActualSoundness
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

theorem nearResonantMassTriple_oneTenth_mem_support :
    nearResonantMassTriple (1 / 10 : Real) ∈ iidMassTripleSupport := by
  norm_num [nearResonantMassTriple, iidMassTripleSupport,
    TwoParameterSpectralAveragingAtlas.iidMassPairSupport,
    massSupport, massLower, massUpper]

theorem finiteAdjugateInteractionContraction_oneTenth_ne_zero :
    sixSiteNearResonantFiniteAdjugateInteractionContraction (1 / 10)
      (actualSixSiteSelectedDualEnergy cleanSixSiteDecayModes
        (nearResonantMassTriple (1 / 10))) ≠ 0 := by
  intro hzero
  apply scaledCollisionExceptionalPolynomial_eval_oneTenth_ne_zero
  exact actualSixSiteFiniteContraction_zero_implies_exceptional_eval_zero
    nearResonantMassTriple_oneTenth_mem_support (by norm_num) hzero

theorem dualAdjugateInteractionContraction_oneTenth_ne_zero :
    harmonicDualOrderedAdjugateInteractionContraction
      (actualSixSiteThreeMassConfig (nearResonantMassTriple (1 / 10)))
      cleanSixSiteDecayModes ≠ 0 := by
  rw [harmonicDualOrderedAdjugateInteractionContraction_eq_finite
    nearResonantMassTriple_oneTenth_mem_support]
  exact finiteAdjugateInteractionContraction_oneTenth_ne_zero

/-- Strict positivity of the selected normalized collision weight at the
explicit rational path point t = 1/10. -/
theorem harmonicOrderedNormalizedInteractionWeight_oneTenth_pos :
    0 < harmonicOrderedNormalizedInteractionWeight
      (actualSixSiteThreeMassConfig (nearResonantMassTriple (1 / 10)))
      cleanSixSiteDecayModes := by
  have hpole : 1 - (1 / 10 : Real) ^ 2 ≠ 0 := by norm_num
  have hsimple :
      SimpleOrderedSpectrum
        (actualSixSiteThreeMassHarmonic
          (nearResonantMassTriple (1 / 10))) :=
    actualSixSiteNearResonant_simpleOrderedSpectrum
      (by norm_num) nearResonantMassTriple_oneTenth_mem_support hpole
  have hsimpleHarmonic :
      SimpleOrderedSpectrum
        (harmonicHermitian
          (actualSixSiteThreeMassConfig
            (nearResonantMassTriple (1 / 10)))) := by
    simpa [actualSixSiteThreeMassHarmonic, actualSixSiteThreeMassConfig,
      threeMassHarmonicHermitian] using hsimple
  have hfrequency : ∀ r, 0 < orderedModeFrequency
      (harmonicHermitian
        (actualSixSiteThreeMassConfig (nearResonantMassTriple (1 / 10))))
      (cleanSixSiteDecayModes r) := by
    intro r
    rw [orderedModeFrequency]
    exact Real.sqrt_pos.2 (by
      simpa [actualSixSiteThreeMassHarmonic, actualSixSiteThreeMassConfig,
        threeMassHarmonicHermitian] using
          actualSixSiteDecayModes_energy_pos_of_simple
            (nearResonantMassTriple (1 / 10)) hsimple r)
  exact
    harmonicOrderedNormalizedInteractionWeight_pos_of_dualAdjugateContraction_ne_zero
      (actualSixSiteThreeMassConfig (nearResonantMassTriple (1 / 10)))
      hsimpleHarmonic cleanSixSiteDecayModes hfrequency
      dualAdjugateInteractionContraction_oneTenth_ne_zero

end

end ArchonPhysics.ActualSixSiteNearResonantFixedCollisionWeightWitness

import ArchonPhysics.ActualSixSiteNearResonantDisplayedDetWitness
import ArchonPhysics.ActualSixSiteNearResonantProjectorBridge

/-!
# Complete six-site near-resonant lifted-Jacobian witness

The displayed adjugate determinant is transported to the actual ordered
projector minor and then through the exact Hellmann--Feynman factorization to
the lifted frequency Jacobian.  The resulting point lies in every positive
mismatch strip.
-/

namespace ArchonPhysics.ActualSixSiteNearResonantJacobianWitness

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor
open ArchonPhysics.ActualSixSiteNearResonantDisplayedDetWitness
open ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness
open ArchonPhysics.ActualSixSiteNearResonantProjectorBridge
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- The dual and physical selected energy triples agree along the genuine
raw-mass path. -/
theorem actualSixSiteSelectedDualEnergy_cleanDecay_eq
    (t : Real) :
    actualSixSiteSelectedDualEnergy cleanSixSiteDecayModes
        (nearResonantMassTriple t) =
      actualSixSiteNearResonantSelectedEnergy t := by
  funext r
  simpa [actualSixSiteSelectedDualEnergy,
    actualSixSiteNearResonantSelectedEnergy,
    actualSixSiteThreeMassHarmonic] using
    (orderedEigenvalue_actualThreeMass_eq_dual frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
      (nearResonantMassTriple t) (cleanSixSiteDecayModes r)).symm

/-- Every positive mismatch strip contains a physical interior triple with
simple spectrum and genuinely nonzero lifted frequency Jacobian. -/
theorem exists_actualSixSiteNearResonantJacobianWitness
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ triple : MassTriple,
      triple ∈ interior iidMassTripleSupport ∧
      SimpleOrderedSpectrum (actualSixSiteThreeMassHarmonic triple) ∧
      |(actualSixSiteLiftedFrequencyChart triple).2| < epsilon ∧
      (actualThreeMassLiftedFrequencyJacobian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        actualFourSiteDecaySign cleanSixSiteDecayModes triple).det ≠ 0 := by
  obtain ⟨t, ht, hinterior, hmismatch, hsimple, hdisplayed, hpole⟩ :=
    exists_actualSixSiteNearResonantDisplayedDetWitness hepsilon
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
  have hjacobian :=
    (actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      frozenUnitMassSix (by decide) (by decide) (by decide)
      actualFourSiteDecaySign cleanSixSiteDecayModes hinterior
      hsimplePhysical hpositive).2 hprojector
  refine ⟨nearResonantMassTriple t, hinterior, hsimple, ?_, hjacobian⟩
  simpa [actualSixSiteNearResonantMismatchPath] using hmismatch

end

end ArchonPhysics.ActualSixSiteNearResonantJacobianWitness

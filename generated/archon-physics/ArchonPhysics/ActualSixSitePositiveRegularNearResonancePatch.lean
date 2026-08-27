import ArchonPhysics.ActualSixSiteNearResonantJacobianCompleteWitness
import ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
import ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound

/-!
# A positive-probability regular near-resonance patch at six sites

The one-parameter six-site witness supplies, for every positive mismatch
width, one interior simple-spectrum point with nonzero genuine lifted
Jacobian.  Openness of the exact projector-regular source and of the physical
near-resonance strip upgrades that point to a nonempty open patch.  The iid
mass law dominates Lebesgue measure on the support cube, so the patch has
strictly positive probability.

This is a local positive-probability conclusion.  It does not assert that the
lifted Jacobian is nonzero almost everywhere on the full three-mass slice.
-/

open scoped Matrix

namespace ArchonPhysics.ActualSixSitePositiveRegularNearResonancePatch

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorMinorRegularity
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

/-- The exact six-site projector-regular source intersected with the physical
near-resonance strip. -/
def actualSixSitePositiveRegularNearResonancePatch
    (epsilon : Real) : Set MassTriple :=
  actualThreeMassProjectorRegularSource frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
      cleanSixSiteDecayModes ∩
    actualSixSiteNearResonancePatch epsilon

/-- The six-site regular near-resonance patch is open. -/
theorem isOpen_actualSixSitePositiveRegularNearResonancePatch
    (epsilon : Real) :
    IsOpen (actualSixSitePositiveRegularNearResonancePatch epsilon) := by
  exact
    (isOpen_actualThreeMassProjectorRegularSource frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
      cleanSixSiteDecayModes).inter
        (isOpen_actualSixSiteNearResonancePatch epsilon)

theorem measurableSet_actualSixSitePositiveRegularNearResonancePatch
    (epsilon : Real) :
    MeasurableSet (actualSixSitePositiveRegularNearResonancePatch epsilon) :=
  (isOpen_actualSixSitePositiveRegularNearResonancePatch epsilon).measurableSet

/-- Every point of the patch lies in the frozen iid support cube. -/
theorem actualSixSitePositiveRegularNearResonancePatch_subset_support
    (epsilon : Real) :
    actualSixSitePositiveRegularNearResonancePatch epsilon ⊆
      iidMassTripleSupport := by
  intro triple htriple
  exact actualSixSiteNearResonancePatch_subset_support epsilon htriple.2

/-- Every positive mismatch width contains a witness in the exact regular
near-resonance patch. -/
theorem actualSixSitePositiveRegularNearResonancePatch_nonempty
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    (actualSixSitePositiveRegularNearResonancePatch epsilon).Nonempty := by
  obtain ⟨triple, htriple, hsimple, hmismatch, hJacobian⟩ :=
    exists_actualSixSiteNearResonantJacobianWitness hepsilon
  have hpositive : ∀ r, 0 < orderedEigenvalue
      (actualSixSiteThreeMassHarmonic triple) (cleanSixSiteDecayModes r) :=
    actualSixSiteDecayModes_energy_pos_of_simple triple hsimple
  have hregular : triple ∈ actualThreeMassProjectorRegularSource
      frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
      cleanSixSiteDecayModes := by
    apply (mem_actualThreeMassProjectorRegularSource_iff_lifted
      frozenUnitMassSix (by decide) (by decide) (by decide)
      actualFourSiteDecaySign cleanSixSiteDecayModes triple).2
    exact ⟨htriple, by
      simpa [actualSixSiteThreeMassHarmonic] using hsimple, by
      simpa [actualSixSiteThreeMassHarmonic] using hpositive, hJacobian⟩
  refine ⟨triple, hregular, ?_⟩
  exact ⟨htriple, hmismatch⟩

/-- The regular near-resonance patch has strictly positive iid mass. -/
theorem iidMassTripleLaw_actualSixSitePositiveRegularNearResonancePatch_pos
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 < iidMassTripleLaw
      (actualSixSitePositiveRegularNearResonancePatch epsilon) := by
  have hopen :=
    isOpen_actualSixSitePositiveRegularNearResonancePatch epsilon
  have hvolume : 0 < (volume : Measure MassTriple)
      (actualSixSitePositiveRegularNearResonancePatch epsilon) :=
    hopen.measure_pos volume
      (actualSixSitePositiveRegularNearResonancePatch_nonempty hepsilon)
  have hdomination :=
    volume_restrict_iidMassTripleSupport_le_iidMassTripleLaw
      (actualSixSitePositiveRegularNearResonancePatch epsilon)
  have hrestrict :
      (volume : Measure MassTriple).restrict iidMassTripleSupport
          (actualSixSitePositiveRegularNearResonancePatch epsilon) =
        (volume : Measure MassTriple)
          (actualSixSitePositiveRegularNearResonancePatch epsilon) := by
    rw [Measure.restrict_apply hopen.measurableSet]
    congr 1
    exact inter_eq_left.mpr
      (actualSixSitePositiveRegularNearResonancePatch_subset_support epsilon)
  rw [hrestrict] at hdomination
  exact hvolume.trans_le hdomination

/-- Consumer-facing formulation: for every positive mismatch width there is
an open positive-probability patch on which the selected modes are simple and
positive, the true mismatch is inside the strip, and the genuine lifted
Jacobian is nonzero. -/
theorem exists_positive_iidMass_actualSixSite_liftedRegularNearResonancePatch
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set MassTriple,
      IsOpen patch ∧
      0 < iidMassTripleLaw patch ∧
      ∀ triple ∈ patch,
        triple ∈ interior iidMassTripleSupport ∧
        SimpleOrderedSpectrum (actualSixSiteThreeMassHarmonic triple) ∧
        (∀ r, 0 < orderedEigenvalue
          (actualSixSiteThreeMassHarmonic triple) (cleanSixSiteDecayModes r)) ∧
        |(actualSixSiteLiftedFrequencyChart triple).2| < epsilon ∧
        (actualThreeMassLiftedFrequencyJacobian frozenUnitMassSix
          (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
          actualFourSiteDecaySign cleanSixSiteDecayModes triple).det ≠ 0 := by
  refine ⟨actualSixSitePositiveRegularNearResonancePatch epsilon,
    isOpen_actualSixSitePositiveRegularNearResonancePatch epsilon,
    iidMassTripleLaw_actualSixSitePositiveRegularNearResonancePatch_pos hepsilon,
    ?_⟩
  intro triple hpatch
  have hlifted :=
    (mem_actualThreeMassProjectorRegularSource_iff_lifted
      frozenUnitMassSix (by decide) (by decide) (by decide)
      actualFourSiteDecaySign cleanSixSiteDecayModes triple).1 hpatch.1
  exact ⟨hlifted.1, by
    simpa [actualSixSiteThreeMassHarmonic] using hlifted.2.1, by
    simpa [actualSixSiteThreeMassHarmonic] using hlifted.2.2.1,
    hpatch.2.2, hlifted.2.2.2⟩

end

end ArchonPhysics.ActualSixSitePositiveRegularNearResonancePatch

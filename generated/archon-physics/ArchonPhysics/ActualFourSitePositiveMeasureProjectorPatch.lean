import ArchonPhysics.ActualFourSitePositiveProjectorWitness
import ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
import ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound

/-!
# A positive-probability actual four-site nondegenerate patch

The explicit rational four-site witness lies strictly inside the frozen iid
mass cube, has simple positive spectrum, and has nonzero actual projector
minor.  Continuity therefore makes the corresponding actual regular source
a nonempty open set.  Since the frozen iid mass law dominates Lebesgue
measure on its support cube, this source has strictly positive probability.

This is an unconditional theorem about the genuine random-mass harmonic
model.  It proves a positive-probability nondegenerate patch at volume four;
it does not assert resonance, infrared coverage, or uniformity in volume.
-/

namespace ArchonPhysics.ActualFourSitePositiveMeasureProjectorPatch

open ArchonPhysics
open ArchonPhysics.ActualFourSitePositiveProjectorWitness
open ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound
open ArchonPhysics.ActualThreeMassProjectorMinorRegularity
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter MeasureTheory Set

noncomputable section

/-- The genuine projector-regular source for the three positive modes of the
four-site frozen-unit random-mass family. -/
def actualFourSiteProjectorRegularPatch : Set MassTriple :=
  actualThreeMassProjectorRegularSource frozenUnitMassFour
    (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
    actualFourSitePositiveModes

/-- The explicit rational physical witness belongs to the actual regular
source, with no genericity or nondegeneracy premise. -/
theorem actualFourSiteWitnessTriple_mem_projectorRegularPatch :
    actualFourSiteWitnessTriple ∈ actualFourSiteProjectorRegularPatch := by
  refine ⟨actualFourSiteWitnessTriple_mem_interior, ?_, ?_, ?_⟩
  · simpa [actualFourSiteHarmonic] using actualFourSiteWitness_simple
  · simpa [actualFourSiteHarmonic] using
      actualFourSiteWitness_positiveModes_energy_pos
  · exact actualFourSiteWitness_projectorWeightMatrix_det_ne_zero

/-- The actual four-site nondegenerate source is open. -/
theorem isOpen_actualFourSiteProjectorRegularPatch :
    IsOpen actualFourSiteProjectorRegularPatch := by
  exact isOpen_actualThreeMassProjectorRegularSource frozenUnitMassFour
    (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
    actualFourSitePositiveModes

/-- The actual four-site nondegenerate source is measurable. -/
theorem measurableSet_actualFourSiteProjectorRegularPatch :
    MeasurableSet actualFourSiteProjectorRegularPatch :=
  isOpen_actualFourSiteProjectorRegularPatch.measurableSet

/-- Every point of the patch remains inside the frozen iid mass cube. -/
theorem actualFourSiteProjectorRegularPatch_subset_support :
    actualFourSiteProjectorRegularPatch ⊆ iidMassTripleSupport := by
  intro triple htriple
  exact interior_subset htriple.1

/-- The actual four-site projector-regular patch has strictly positive iid
mass.  This upgrades the pointwise witness to a positive-probability model
statement. -/
theorem iidMassTripleLaw_actualFourSiteProjectorRegularPatch_pos :
    0 < iidMassTripleLaw actualFourSiteProjectorRegularPatch := by
  have hvolume :
      0 < (volume : Measure MassTriple) actualFourSiteProjectorRegularPatch :=
    isOpen_actualFourSiteProjectorRegularPatch.measure_pos volume
      ⟨actualFourSiteWitnessTriple,
        actualFourSiteWitnessTriple_mem_projectorRegularPatch⟩
  have hdomination :=
    volume_restrict_iidMassTripleSupport_le_iidMassTripleLaw
      actualFourSiteProjectorRegularPatch
  have hrestrict :
      (volume : Measure MassTriple).restrict iidMassTripleSupport
          actualFourSiteProjectorRegularPatch =
        (volume : Measure MassTriple) actualFourSiteProjectorRegularPatch := by
    rw [Measure.restrict_apply measurableSet_actualFourSiteProjectorRegularPatch]
    congr 1
    exact inter_eq_left.mpr
      actualFourSiteProjectorRegularPatch_subset_support
  rw [hrestrict] at hdomination
  exact hvolume.trans_le hdomination

/-- On a positive-probability actual mass patch, all three selected modes are
positive and the genuine lifted child-child-mismatch Jacobian is nonzero. -/
theorem exists_positive_iidMass_actualFourSite_liftedRegularPatch :
    ∃ patch : Set MassTriple,
      IsOpen patch ∧
      0 < iidMassTripleLaw patch ∧
      ∀ triple ∈ patch,
        triple ∈ interior iidMassTripleSupport ∧
        SimpleOrderedSpectrum (actualFourSiteHarmonic triple) ∧
        (∀ r, 0 < orderedEigenvalue
          (actualFourSiteHarmonic triple) (actualFourSitePositiveModes r)) ∧
        (actualFourSiteLiftedFrequencyJacobian triple).det ≠ 0 := by
  refine ⟨actualFourSiteProjectorRegularPatch,
    isOpen_actualFourSiteProjectorRegularPatch,
    iidMassTripleLaw_actualFourSiteProjectorRegularPatch_pos, ?_⟩
  intro triple htriple
  have hlifted :=
    (mem_actualThreeMassProjectorRegularSource_iff_lifted
      frozenUnitMassFour (by decide) (by decide) (by decide)
      actualFourSiteDecaySign actualFourSitePositiveModes triple).1 htriple
  simpa [actualFourSiteHarmonic, actualFourSiteLiftedFrequencyJacobian] using
    hlifted

/-- A compact positive-probability subpatch carries a uniform strictly
positive lower bound for the genuine lifted Jacobian determinant.  Thus the
point witness supplies a quantitative finite-chart good region, rather than
only an isolated nonzero determinant. -/
theorem exists_compact_positive_iidMass_actualFourSite_liftedJacobianPatch :
    ∃ K : Set MassTriple, ∃ detLower : Real,
      IsCompact K ∧
      0 < iidMassTripleLaw K ∧
      K ⊆ actualFourSiteProjectorRegularPatch ∧
      0 < detLower ∧
      ∀ triple ∈ K,
        detLower ≤ |(actualFourSiteLiftedFrequencyJacobian triple).det| := by
  have hnhds : actualFourSiteProjectorRegularPatch ∈
      nhds actualFourSiteWitnessTriple :=
    isOpen_actualFourSiteProjectorRegularPatch.mem_nhds
      actualFourSiteWitnessTriple_mem_projectorRegularPatch
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let K : Set MassTriple :=
    Metric.closedBall actualFourSiteWitnessTriple (radius / 2)
  have hradiusHalf : 0 < radius / 2 := half_pos hradius
  have hKregular : K ⊆ actualFourSiteProjectorRegularPatch := by
    exact (Metric.closedBall_subset_ball (half_lt_self hradius)).trans hball
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hKmeasurable : MeasurableSet K := hKcompact.measurableSet
  have hKsupport : K ⊆ iidMassTripleSupport :=
    hKregular.trans actualFourSiteProjectorRegularPatch_subset_support
  have hvolumeK : 0 < (volume : Measure MassTriple) K := by
    exact (Metric.measure_ball_pos volume actualFourSiteWitnessTriple
      hradiusHalf).trans_le (measure_mono Metric.ball_subset_closedBall)
  have hdomination :=
    volume_restrict_iidMassTripleSupport_le_iidMassTripleLaw K
  have hrestrict :
      (volume : Measure MassTriple).restrict iidMassTripleSupport K =
        (volume : Measure MassTriple) K := by
    rw [Measure.restrict_apply hKmeasurable]
    congr 1
    exact inter_eq_left.mpr hKsupport
  rw [hrestrict] at hdomination
  have hmassK : 0 < iidMassTripleLaw K :=
    hvolumeK.trans_le hdomination
  obtain ⟨detLower, hdetLower, hdetBound⟩ :=
    exists_positive_actualThreeMassLiftedJacobian_detLower_on_compact
      frozenUnitMassFour (by decide) (by decide) (by decide)
      actualFourSiteDecaySign actualFourSitePositiveModes K hKcompact hKregular
  refine ⟨K, detLower, hKcompact, hmassK, hKregular, hdetLower, ?_⟩
  intro triple htriple
  simpa [actualFourSiteLiftedFrequencyJacobian] using
    hdetBound triple htriple

end

end ArchonPhysics.ActualFourSitePositiveMeasureProjectorPatch

import ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor
import ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum

/-!
# A small positive six-site path point with nonzero adjugate residual

The clean six-cycle is exactly resonant but spectrally degenerate.  Along the
reciprocal raw-mass path, every nonzero supported point has simple spectrum.
The symmetric adjugate residual equals two at the clean endpoint, so
continuity supplies arbitrarily small positive points where the mismatch is
small, the spectrum is simple, and the residual remains nonzero.
-/

namespace ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open Filter Set

noncomputable section

/-- The three selected squared frequencies, in decay-chart order, along the
near-resonant raw-mass path. -/
def actualSixSiteNearResonantSelectedEnergy (t : Real) : Fin 3 → Real :=
  fun r => orderedEigenvalue
    (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t))
    (cleanSixSiteDecayModes r)

theorem continuous_actualSixSiteNearResonantSelectedEnergy (r : Fin 3) :
    Continuous fun t : Real => actualSixSiteNearResonantSelectedEnergy t r := by
  exact (continuous_orderedEigenvalue (cleanSixSiteDecayModes r)).comp
    ((continuous_threeMassHarmonicHermitian frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)).comp
      continuous_nearResonantMassTriple)

/-- At the clean endpoint the selected squared energies are `4,1,1`. -/
theorem actualSixSiteNearResonantSelectedEnergy_zero :
    actualSixSiteNearResonantSelectedEnergy 0 = ![(4 : Real), 1, 1] := by
  have hclean :
      actualSixSiteThreeMassHarmonic unitMassTriple =
        cleanCycleHarmonicHermitian 6 := by
    simpa [actualSixSiteThreeMassHarmonic] using
      threeMassHarmonic_unitMassTriple_eq_clean
  funext r
  fin_cases r <;>
    simp only [actualSixSiteNearResonantSelectedEnergy,
      nearResonantMassTriple_zero, cleanSixSiteDecayModes, hclean]
  all_goals norm_num
  · have h := orderedEigenvalue_cleanCycleHarmonic_six (0 : Fin 6)
    norm_num [cleanSixSiteOrderedEnergy] at h
    exact h
  · have h := orderedEigenvalue_cleanCycleHarmonic_six (3 : Fin 6)
    norm_num [cleanSixSiteOrderedEnergy] at h
    exact h
  · have h := orderedEigenvalue_cleanCycleHarmonic_six (4 : Fin 6)
    norm_num [cleanSixSiteOrderedEnergy] at h
    exact h

/-- The exact symmetric determinant residual along the genuine selected
energy branches. -/
def actualSixSiteNearResonantAdjugateResidualPath (t : Real) : Real :=
  nearResonantAdjugateResidual t
    (actualSixSiteNearResonantSelectedEnergy t)

theorem continuous_actualSixSiteNearResonantAdjugateResidualPath :
    Continuous actualSixSiteNearResonantAdjugateResidualPath := by
  change Continuous (nearResonantAdjugateResidualPath
    (fun t => actualSixSiteNearResonantSelectedEnergy t 0)
    (fun t => actualSixSiteNearResonantSelectedEnergy t 1)
    (fun t => actualSixSiteNearResonantSelectedEnergy t 2))
  exact continuous_nearResonantAdjugateResidualPath
    (continuous_actualSixSiteNearResonantSelectedEnergy 0)
    (continuous_actualSixSiteNearResonantSelectedEnergy 1)
    (continuous_actualSixSiteNearResonantSelectedEnergy 2)

theorem actualSixSiteNearResonantAdjugateResidualPath_zero :
    actualSixSiteNearResonantAdjugateResidualPath 0 = 2 := by
  rw [actualSixSiteNearResonantAdjugateResidualPath,
    actualSixSiteNearResonantSelectedEnergy_zero,
    nearResonantAdjugateResidual_zero_clean]

/-- The physical frequency mismatch restricted to the scalar mass path. -/
def actualSixSiteNearResonantMismatchPath (t : Real) : Real :=
  (actualSixSiteLiftedFrequencyChart (nearResonantMassTriple t)).2

theorem continuous_actualSixSiteNearResonantMismatchPath :
    Continuous actualSixSiteNearResonantMismatchPath := by
  exact continuous_actualSixSiteDecayMismatch.comp
    continuous_nearResonantMassTriple

theorem actualSixSiteNearResonantMismatchPath_zero :
    actualSixSiteNearResonantMismatchPath 0 = 0 := by
  rw [actualSixSiteNearResonantMismatchPath, nearResonantMassTriple_zero,
    actualSixSiteLiftedFrequencyChart_unit_mismatch_eq_zero]

theorem eventually_nearResonantMassTriple_mem_interior :
    ∀ᶠ t in nhds (0 : Real),
      nearResonantMassTriple t ∈ interior iidMassTripleSupport := by
  exact (isOpen_interior.preimage continuous_nearResonantMassTriple).mem_nhds
    (by simpa using unitMassTriple_mem_interior)

theorem eventually_actualSixSiteNearResonantMismatchPath_lt
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ t in nhds (0 : Real),
      |actualSixSiteNearResonantMismatchPath t| < epsilon := by
  have hopen : IsOpen
      {t : Real | |actualSixSiteNearResonantMismatchPath t| < epsilon} :=
    isOpen_lt continuous_actualSixSiteNearResonantMismatchPath.abs continuous_const
  exact hopen.mem_nhds (by
    change |actualSixSiteNearResonantMismatchPath 0| < epsilon
    rw [actualSixSiteNearResonantMismatchPath_zero, abs_zero]
    exact hepsilon)

theorem eventually_actualSixSiteNearResonantAdjugateResidualPath_ne_zero :
    ∀ᶠ t in nhds (0 : Real),
      actualSixSiteNearResonantAdjugateResidualPath t ≠ 0 := by
  apply continuous_actualSixSiteNearResonantAdjugateResidualPath.continuousAt.eventually_ne
  rw [actualSixSiteNearResonantAdjugateResidualPath_zero]
  norm_num

theorem eventually_nearResonantPath_avoids_poles :
    ∀ᶠ t in nhds (0 : Real), 1 - t ^ 2 ≠ 0 := by
  have hcontinuous : Continuous fun t : Real => 1 - t ^ 2 := by fun_prop
  exact hcontinuous.continuousAt.eventually_ne (by norm_num)

/-- Every positive mismatch tolerance admits a positive path parameter with
interior masses, simple spectrum, nonzero residual, and no reciprocal pole. -/
theorem exists_actualSixSiteNearResonantPathResidualWitness
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ t : Real,
      0 < t ∧
      nearResonantMassTriple t ∈ interior iidMassTripleSupport ∧
      |actualSixSiteNearResonantMismatchPath t| < epsilon ∧
      SimpleOrderedSpectrum
        (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)) ∧
      actualSixSiteNearResonantAdjugateResidualPath t ≠ 0 ∧
      1 - t ^ 2 ≠ 0 := by
  have heventually : ∀ᶠ t in nhds (0 : Real),
      nearResonantMassTriple t ∈ interior iidMassTripleSupport ∧
      |actualSixSiteNearResonantMismatchPath t| < epsilon ∧
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
  have htpos : 0 < delta / 2 := half_pos hdelta
  have htball : delta / 2 ∈ Metric.ball (0 : Real) delta := by
    simp only [Metric.mem_ball, Real.dist_eq]
    rw [sub_zero, abs_of_pos htpos]
    linarith
  have hdata := hball htball
  have hsimple := actualSixSiteNearResonant_simpleOrderedSpectrum
    (ne_of_gt htpos) (interior_subset hdata.1) hdata.2.2.2
  exact ⟨delta / 2, htpos, hdata.1, hdata.2.1, hsimple,
    hdata.2.2.1, hdata.2.2.2⟩

end

end ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness

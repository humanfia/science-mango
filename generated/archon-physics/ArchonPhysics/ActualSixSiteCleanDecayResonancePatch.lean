import ArchonPhysics.ActualFourSiteDecayMismatchInfraredGap
import ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound

/-!
# A genuine six-site near-resonance patch

The clean periodic six-cycle has decreasing squared-frequency spectrum
`[4, 3, 3, 1, 1, 0]`.  Hence its top frequency and the two ordered modes at
indices three and four obey the exact decay relation `2 = 1 + 1`.

We realize this point inside the actual three-mass family by freezing a
six-site unit background and setting the three sampled masses to one.
Continuity of the true ordered-frequency chart then shows that every open
mismatch strip around zero contains a nonempty open subset of the physical
iid mass cube, and consequently has strictly positive iid mass.

The clean resonance point has spectral multiplicities.  This module does
not assert simple spectrum or a nonzero lifted Jacobian there; intersecting
the positive strip with a genuine regular source remains a separate task.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualSixSiteCleanDecayResonancePatch

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.CleanCycleAcousticCountEnvelope
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open MeasureTheory Set

noncomputable section

/-- Fourier-labelled clean six-cycle squared frequencies. -/
def cleanSixSiteFourierEnergy : Fin 6 → Real := ![0, 1, 3, 4, 3, 1]

theorem cleanSixSiteFourierEnergy_congr_val (k l : Fin 6)
    (hval : k.val = l.val) :
    cleanSixSiteFourierEnergy k = cleanSixSiteFourierEnergy l := by
  exact congrArg cleanSixSiteFourierEnergy (Fin.ext hval)

/-- Decreasing clean six-cycle squared-frequency list. -/
def cleanSixSiteOrderedEnergy : Fin 6 → Real := ![4, 3, 3, 1, 1, 0]

theorem cleanCycleModeEnergy_six_site_reindex (k : Fin 6) :
    cleanCycleModeEnergy 6 ((siteEquivFin 6).symm k) =
      cleanSixSiteFourierEnergy k := by
  fin_cases k
  · norm_num [cleanCycleModeEnergy, cleanSixSiteFourierEnergy,
      val_siteEquivFin_symm]
  · simp only [cleanCycleModeEnergy, val_siteEquivFin_symm]
    rw [cleanSixSiteFourierEnergy_congr_val _ (1 : Fin 6) (by rfl),
      show cleanSixSiteFourierEnergy (1 : Fin 6) = 1 by rfl]
    norm_num only [Nat.cast_ofNat]
    rw [show Real.pi * (1 : Real) / 6 = Real.pi / 6 by ring,
      Real.sin_pi_div_six]
    norm_num
  · simp only [cleanCycleModeEnergy, val_siteEquivFin_symm]
    rw [cleanSixSiteFourierEnergy_congr_val _ (2 : Fin 6) (by rfl),
      show cleanSixSiteFourierEnergy (2 : Fin 6) = 3 by rfl]
    norm_num only [Nat.cast_ofNat]
    rw [show Real.pi * (2 : Real) / 6 = Real.pi / 3 by ring,
      Real.sin_pi_div_three]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3)]
  · simp only [cleanCycleModeEnergy, val_siteEquivFin_symm]
    rw [cleanSixSiteFourierEnergy_congr_val _ (3 : Fin 6) (by rfl),
      show cleanSixSiteFourierEnergy (3 : Fin 6) = 4 by rfl]
    norm_num only [Nat.cast_ofNat]
    rw [show Real.pi * (3 : Real) / 6 = Real.pi / 2 by ring,
      Real.sin_pi_div_two]
    norm_num
  · simp only [cleanCycleModeEnergy, val_siteEquivFin_symm]
    rw [cleanSixSiteFourierEnergy_congr_val _ (4 : Fin 6) (by rfl),
      show cleanSixSiteFourierEnergy (4 : Fin 6) = 3 by rfl]
    norm_num only [Nat.cast_ofNat]
    rw [show Real.pi * (4 : Real) / 6 =
      Real.pi - Real.pi / 3 by ring]
    rw [Real.sin_pi_sub, Real.sin_pi_div_three]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3)]
  · simp only [cleanCycleModeEnergy, val_siteEquivFin_symm]
    rw [cleanSixSiteFourierEnergy_congr_val _ (5 : Fin 6) (by rfl),
      show cleanSixSiteFourierEnergy (5 : Fin 6) = 1 by rfl]
    norm_num only [Nat.cast_ofNat]
    rw [show Real.pi * (5 : Real) / 6 =
      Real.pi - Real.pi / 6 by ring]
    rw [Real.sin_pi_sub, Real.sin_pi_div_six]
    norm_num

theorem cleanSixSiteOrderedEnergy_antitone :
    Antitone cleanSixSiteOrderedEnergy := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [cleanSixSiteOrderedEnergy, Fin.le_iff_val_le_val] <;>
      norm_num

theorem cleanCycleHarmonicMatrix_six_charpoly :
    Matrix.charpoly (cleanCycleHarmonicMatrix 6) =
      ∏ k : Fin 6,
        (Polynomial.X - Polynomial.C (cleanSixSiteOrderedEnergy k)) := by
  rw [cleanCycle_charpoly_formula]
  have hreindex :
      (∏ j : Lattice.Site 6,
          (Polynomial.X - Polynomial.C (cleanCycleModeEnergy 6 j))) =
        ∏ k : Fin 6,
          (Polynomial.X - Polynomial.C
            (cleanCycleModeEnergy 6 ((siteEquivFin 6).symm k))) := by
    apply Fintype.prod_equiv (siteEquivFin 6)
    intro j
    simp
  rw [hreindex]
  simp_rw [cleanCycleModeEnergy_six_site_reindex]
  simp [Fin.prod_univ_succ, cleanSixSiteFourierEnergy,
    cleanSixSiteOrderedEnergy]
  ring

/-- Exact decreasing squared-frequency spectrum of the clean six-cycle. -/
theorem orderedEigenvalue_cleanCycleHarmonic_six (k : Fin 6) :
    orderedEigenvalue (cleanCycleHarmonicHermitian 6) k =
      cleanSixSiteOrderedEnergy k := by
  exact
    ActualFourSiteDecayMismatchInfraredGap.orderedEigenvalue_eq_of_charpoly_eq_prod
      (cleanCycleHarmonicHermitian 6) cleanSixSiteOrderedEnergy
      cleanSixSiteOrderedEnergy_antitone
      cleanCycleHarmonicMatrix_six_charpoly k

/-- Unit six-site background for the actual three-mass chart. -/
def frozenUnitMassSix : Lattice.PositiveMassConfig 6 where
  mass _ := 1
  mass_pos _ := by norm_num

/-- The central raw triple, strictly inside the frozen iid cube. -/
def unitMassTriple : MassTriple := (((1 : Real), (1 : Real)), (1 : Real))

theorem unitMassTriple_mem_interior :
    unitMassTriple ∈ interior iidMassTripleSupport := by
  rw [iidMassTripleSupport, interior_prod_eq]
  constructor
  · rw [TwoParameterSpectralAveragingAtlas.iidMassPairSupport,
      interior_prod_eq]
    constructor <;>
      norm_num [unitMassTriple, massSupport, massLower, massUpper]
  · norm_num [unitMassTriple, massSupport, massLower, massUpper]

theorem threeMassSiteConfig_unitMassTriple_eq_frozenUnitMassSix :
    threeMassSiteConfig frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        unitMassTriple =
      frozenUnitMassSix := by
  change Lattice.PositiveMassConfig.mk _ _ =
    Lattice.PositiveMassConfig.mk _ _
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext i
  split_ifs <;> norm_num [unitMassTriple, frozenUnitMassSix, clippedMass, massLower, massUpper]

theorem harmonicHermitian_frozenUnitMassSix_eq_clean :
    harmonicHermitian frozenUnitMassSix = cleanCycleHarmonicHermitian 6 := by
  apply Subtype.ext
  unfold harmonicHermitian cleanCycleHarmonicHermitian
    massWeightedHarmonicMatrix cleanCycleHarmonicMatrix
  congr 1
  ext i j
  simp [massWeightedDifferenceMatrix, frozenUnitMassSix]

theorem threeMassHarmonic_unitMassTriple_eq_clean :
    threeMassHarmonicHermitian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        unitMassTriple =
      cleanCycleHarmonicHermitian 6 := by
  unfold threeMassHarmonicHermitian
  rw [threeMassSiteConfig_unitMassTriple_eq_frozenUnitMassSix,
    harmonicHermitian_frozenUnitMassSix_eq_clean]

/-- Parent index zero and child indices three and four. -/
def cleanSixSiteDecayModes : Fin 3 →
    Fin (Fintype.card (Lattice.Site 6)) := ![0, 3, 4]

/-- The actual three-mass six-site lifted chart centered at the clean
resonance. -/
def actualSixSiteLiftedFrequencyChart : MassTriple → MassTriple :=
  actualThreeMassLiftedFrequencyChart frozenUnitMassSix
    (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
    ActualThreeMassLiftedJacobianPolynomial.actualFourSiteDecaySign
    cleanSixSiteDecayModes

/-- The clean six-site point is an exact physical decay resonance. -/
theorem actualSixSiteLiftedFrequencyChart_unit_mismatch_eq_zero :
    (actualSixSiteLiftedFrequencyChart unitMassTriple).2 = 0 := by
  have hzero : orderedEigenvalue (cleanCycleHarmonicHermitian 6)
      (cleanSixSiteDecayModes 0) = 4 := by
    rw [orderedEigenvalue_cleanCycleHarmonic_six (cleanSixSiteDecayModes 0)]
    change (4 : Real) = 4
    norm_num
  have hone : orderedEigenvalue (cleanCycleHarmonicHermitian 6)
      (cleanSixSiteDecayModes 1) = 1 := by
    rw [orderedEigenvalue_cleanCycleHarmonic_six (cleanSixSiteDecayModes 1)]
    change (1 : Real) = 1
    norm_num
  have htwo : orderedEigenvalue (cleanCycleHarmonicHermitian 6)
      (cleanSixSiteDecayModes 2) = 1 := by
    rw [orderedEigenvalue_cleanCycleHarmonic_six (cleanSixSiteDecayModes 2)]
    change (1 : Real) = 1
    norm_num
  unfold actualSixSiteLiftedFrequencyChart
    actualThreeMassLiftedFrequencyChart
  dsimp only
  rw [Fin.sum_univ_three]
  rw [threeMassHarmonic_unitMassTriple_eq_clean]
  simp only [orderedModeFrequency]
  rw [hzero, hone, htwo]
  have htwo_ne : (2 : Fin 3) ≠ 0 := by decide
  norm_num [ActualThreeMassLiftedJacobianPolynomial.actualFourSiteDecaySign,
    htwo_ne]

/-- The true six-site mismatch is continuous in the three sampled masses. -/
theorem continuous_actualSixSiteDecayMismatch :
    Continuous fun triple : MassTriple ↦
      (actualSixSiteLiftedFrequencyChart triple).2 := by
  exact
    (continuous_actualThreeMassLiftedFrequencyChart frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
      ActualThreeMassLiftedJacobianPolynomial.actualFourSiteDecaySign
      cleanSixSiteDecayModes).snd

/-- Open physical part of the mismatch strip of half-width `epsilon`. -/
def actualSixSiteNearResonancePatch (epsilon : Real) : Set MassTriple :=
  interior iidMassTripleSupport ∩
    {triple | |(actualSixSiteLiftedFrequencyChart triple).2| < epsilon}

theorem isOpen_actualSixSiteNearResonancePatch (epsilon : Real) :
    IsOpen (actualSixSiteNearResonancePatch epsilon) := by
  apply isOpen_interior.inter
  exact isOpen_lt continuous_actualSixSiteDecayMismatch.abs continuous_const

theorem unitMassTriple_mem_actualSixSiteNearResonancePatch
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    unitMassTriple ∈ actualSixSiteNearResonancePatch epsilon := by
  refine ⟨unitMassTriple_mem_interior, ?_⟩
  change |(actualSixSiteLiftedFrequencyChart unitMassTriple).2| < epsilon
  rw [actualSixSiteLiftedFrequencyChart_unit_mismatch_eq_zero, abs_zero]
  exact hepsilon

theorem actualSixSiteNearResonancePatch_subset_support (epsilon : Real) :
    actualSixSiteNearResonancePatch epsilon ⊆ iidMassTripleSupport := by
  intro triple htriple
  exact interior_subset htriple.1

/-- Every positive mismatch width has strictly positive probability in the
genuine iid three-mass six-site family. -/
theorem iidMassTripleLaw_actualSixSiteNearResonancePatch_pos
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 < iidMassTripleLaw (actualSixSiteNearResonancePatch epsilon) := by
  have hopen := isOpen_actualSixSiteNearResonancePatch epsilon
  have hnonempty :
      (actualSixSiteNearResonancePatch epsilon).Nonempty :=
    ⟨unitMassTriple,
      unitMassTriple_mem_actualSixSiteNearResonancePatch hepsilon⟩
  have hvolume :
      0 < (volume : Measure MassTriple)
        (actualSixSiteNearResonancePatch epsilon) :=
    hopen.measure_pos volume hnonempty
  have hdomination :=
    volume_restrict_iidMassTripleSupport_le_iidMassTripleLaw
      (actualSixSiteNearResonancePatch epsilon)
  have hrestrict :
      (volume : Measure MassTriple).restrict iidMassTripleSupport
          (actualSixSiteNearResonancePatch epsilon) =
        (volume : Measure MassTriple)
          (actualSixSiteNearResonancePatch epsilon) := by
    rw [Measure.restrict_apply hopen.measurableSet]
    congr 1
    exact inter_eq_left.mpr
      (actualSixSiteNearResonancePatch_subset_support epsilon)
  rw [hrestrict] at hdomination
  exact hvolume.trans_le hdomination

/-- Equivalently, the unrestricted open mismatch strip itself has positive
iid mass. -/
theorem iidMassTripleLaw_actualSixSite_abs_mismatch_lt_pos
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 < iidMassTripleLaw
      {triple : MassTriple |
        |(actualSixSiteLiftedFrequencyChart triple).2| < epsilon} := by
  exact (iidMassTripleLaw_actualSixSiteNearResonancePatch_pos hepsilon).trans_le
    (measure_mono inter_subset_right)

end

end ArchonPhysics.ActualSixSiteCleanDecayResonancePatch

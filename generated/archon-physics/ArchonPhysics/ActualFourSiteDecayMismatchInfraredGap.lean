import ArchonPhysics.ActualFourSitePositiveMeasureProjectorPatch
import ArchonPhysics.CleanCycleAcousticCountEnvelope
import ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

/-!
# A uniform decay-mismatch gap on the actual four-site iid support

The clean four-cycle has decreasing squared-frequency spectrum
`[4, 2, 2, 0]`.  The frozen mass bounds compare every actual ordered
eigenvalue with the corresponding clean eigenvalue.  Consequently the
largest actual frequency is strictly smaller than `9 / 4`, whereas the next
two are each strictly larger than `23 / 20`.  The physical decay mismatch is
therefore uniformly smaller than `-1 / 20` on the whole iid mass cube.

In particular, the positive-measure nondegenerate projector patch constructed
for the actual four-site model cannot meet exact or `1 / 20`-near resonance.
This is an unconditional finite-volume no-go result; it does not transfer a
four-site contribution to arbitrary periodic volume.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualFourSiteDecayMismatchInfraredGap

open ArchonPhysics
open ArchonPhysics.ActualFourSitePositiveMeasureProjectorPatch
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
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
open Set

noncomputable section

/-- A decreasing list of roots is the ordered Hermitian spectrum.  This
local lemma keeps the four-site audit independent of the zero-cut path
regression chain. -/
theorem orderedEigenvalue_eq_of_charpoly_eq_prod
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index)
    (energy : Fin (Fintype.card index) → Real)
    (henergy : Antitone energy)
    (hchar : Matrix.charpoly A.1 = ∏ k,
      (Polynomial.X - Polynomial.C (energy k))) :
    ∀ k, orderedEigenvalue A k = energy k := by
  have hroots : (Matrix.charpoly A.1).roots =
      Multiset.map energy Finset.univ.val := by
    rw [hchar, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort := A.2.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hsort
  have hsort' :
      (Multiset.map energy Finset.univ.val).sort (· ≥ ·) =
        List.ofFn (fun k => orderedEigenvalue A k) := by
    simpa [orderedEigenvalue, Function.comp_def] using hsort
  have henergySort :
      (Multiset.map energy Finset.univ.val).sort (· ≥ ·) =
        List.ofFn energy := by
    simp only [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact henergy.sortedGE_ofFn
  have hlist : List.ofFn (fun k => orderedEigenvalue A k) =
      List.ofFn energy := hsort'.symm.trans henergySort
  exact fun k => congrFun (List.ofFn_inj.mp hlist) k

/-- The Fourier-labelled clean four-cycle energies. -/
def cleanFourSiteFourierEnergy : Fin 4 → Real := ![0, 2, 4, 2]

/-- The decreasing clean four-cycle energy list. -/
def cleanFourSiteOrderedEnergy : Fin 4 → Real := ![4, 2, 2, 0]

theorem cleanCycleModeEnergy_four_site_reindex (k : Fin 4) :
    cleanCycleModeEnergy 4 ((siteEquivFin 4).symm k) =
      cleanFourSiteFourierEnergy k := by
  fin_cases k
  · norm_num [cleanCycleModeEnergy, cleanFourSiteFourierEnergy,
      val_siteEquivFin_symm]
  · simp only [cleanCycleModeEnergy, val_siteEquivFin_symm]
    norm_num [cleanFourSiteFourierEnergy]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  · change 4 * Real.sin (Real.pi * (2 : Real) / 4) ^ 2 = 4
    rw [show Real.pi * (2 : Real) / 4 = Real.pi / 2 by ring]
    norm_num [Real.sin_pi_div_two]
  · change 4 * Real.sin (Real.pi * (3 : Real) / 4) ^ 2 = 2
    rw [show Real.pi * (3 : Real) / 4 =
      Real.pi - Real.pi / 4 by ring]
    rw [Real.sin_pi_sub, Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]

theorem cleanFourSiteOrderedEnergy_antitone :
    Antitone cleanFourSiteOrderedEnergy := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [cleanFourSiteOrderedEnergy, Fin.le_iff_val_le_val] <;>
      norm_num

theorem cleanCycleHarmonicMatrix_four_charpoly :
    Matrix.charpoly (cleanCycleHarmonicMatrix 4) =
      ∏ k : Fin 4,
        (Polynomial.X - Polynomial.C (cleanFourSiteOrderedEnergy k)) := by
  rw [cleanCycle_charpoly_formula]
  have hreindex :
      (∏ j : Lattice.Site 4,
          (Polynomial.X - Polynomial.C (cleanCycleModeEnergy 4 j))) =
        ∏ k : Fin 4,
          (Polynomial.X - Polynomial.C
            (cleanCycleModeEnergy 4 ((siteEquivFin 4).symm k))) := by
    apply Fintype.prod_equiv (siteEquivFin 4)
    intro j
    simp
  rw [hreindex]
  simp_rw [cleanCycleModeEnergy_four_site_reindex]
  simp [Fin.prod_univ_succ, cleanFourSiteFourierEnergy,
    cleanFourSiteOrderedEnergy]
  ring

/-- The exact decreasing squared-frequency spectrum of the clean four-cycle. -/
theorem orderedEigenvalue_cleanCycleHarmonic_four (k : Fin 4) :
    orderedEigenvalue (cleanCycleHarmonicHermitian 4) k =
      cleanFourSiteOrderedEnergy k := by
  exact orderedEigenvalue_eq_of_charpoly_eq_prod
    (cleanCycleHarmonicHermitian 4) cleanFourSiteOrderedEnergy
    cleanFourSiteOrderedEnergy_antitone
    cleanCycleHarmonicMatrix_four_charpoly k

end

end ArchonPhysics.ActualFourSiteDecayMismatchInfraredGap

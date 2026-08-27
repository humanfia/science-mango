import ArchonPhysics.ActualFourSiteDecayMismatchInfraredGap
import ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
import ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
import ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound
import ArchonPhysics.CanonicalCollisionSoftLegBound
import ArchonPhysics.MassWeightedCycleBridge
import ArchonPhysics.RandomMassResultantBridge

/-!
# An exact child-repeated resonance on a six-site opposite-mass slice

We vary the masses at the opposite sites `0` and `3` of the unit six-cycle.
The first raw mass is fixed at `5 / 6`, while the second runs from `5 / 6`
to `7 / 6`.  Exact endpoint characteristic polynomials give opposite signs
for the mismatch between ordered frequencies `0` and `3`.  Global continuity
of ordered frequencies and the intermediate value theorem then produce an
interior exact resonance.

No simplicity or Jacobian statement is used here.  In particular, endpoint
multiplicities do not interfere with continuity of the ordered spectrum.
-/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance

open ArchonPhysics
open ArchonPhysics.ActualFourSiteDecayMismatchInfraredGap
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Polynomial Set

noncomputable section

/-- Reciprocal masses at opposite sites zero and three. -/
def oppositeSixSiteInverseWeights (x y : Real) : Fin 6 → Real :=
  ![x, 1, 1, y, 1, 1]

/-- The reindexed six-cycle Laplacian for opposite reciprocal masses. -/
def explicitSixSiteOppositeWeightLaplacian (x y : Real) :
    Matrix (Fin 6) (Fin 6) Real :=
  !![x + 1, -1, 0, 0, 0, -x;
     -1, 2, -1, 0, 0, 0;
     0, -1, 1 + y, -y, 0, 0;
     0, 0, -y, y + 1, -1, 0;
     0, 0, 0, -1, 2, -1;
     -x, 0, 0, 0, -1, x + 1]

theorem finWeightedCycleLaplacian_oppositeSixSiteInverseWeights
    (x y : Real) :
    finWeightedCycleLaplacian (oppositeSixSiteInverseWeights x y) =
      explicitSixSiteOppositeWeightLaplacian x y := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_succ]
  <;> norm_num +decide [oppositeSixSiteInverseWeights,
    explicitSixSiteOppositeWeightLaplacian, finCycleEdgeVector,
    SingleMassRankOnePerturbation.cycleMassPerturbationVector,
    differenceMatrix, siteEquivFin]
  all_goals simp
  all_goals ring

/-- Literal scalar shift used by the finite determinant computation. -/
def explicitSixSiteOppositeWeightShiftedMatrix
    (x y energy : Real) : Matrix (Fin 6) (Fin 6) Real :=
  !![energy - x - 1, 1, 0, 0, 0, x;
     1, energy - 2, 1, 0, 0, 0;
     0, 1, energy - y - 1, y, 0, 0;
     0, 0, y, energy - y - 1, 1, 0;
     0, 0, 0, 1, energy - 2, 1;
     x, 0, 0, 0, 1, energy - x - 1]

theorem scalar_sub_explicitSixSiteOppositeWeightLaplacian
    (x y energy : Real) :
    Matrix.scalar (Fin 6) energy -
        explicitSixSiteOppositeWeightLaplacian x y =
      explicitSixSiteOppositeWeightShiftedMatrix x y energy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [explicitSixSiteOppositeWeightLaplacian,
      explicitSixSiteOppositeWeightShiftedMatrix, Matrix.scalar_apply]
  all_goals ring

/-- The cubic factor carrying the three non-universal eigenvalues. -/
def oppositeSixSiteCubic (x y energy : Real) : Real :=
  energy ^ 3 - 2 * (x + y + 2) * energy ^ 2 +
    (4 * x * y + 6 * x + 6 * y + 3) * energy -
    (8 * x * y + 2 * x + 2 * y)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem explicitSixSiteOppositeWeightLaplacian_charpoly_eval
    (x y energy : Real) :
    (explicitSixSiteOppositeWeightLaplacian x y).charpoly.eval energy =
      energy * (energy - 1) * (energy - 3) *
        oppositeSixSiteCubic x y energy := by
  rw [Matrix.eval_charpoly,
    scalar_sub_explicitSixSiteOppositeWeightLaplacian]
  rw [det_fin_six_real]
  unfold detFinSixFormula
  simp only [Fin.sum_univ_succ]
  simp [explicitSixSiteOppositeWeightShiftedMatrix]
  unfold detFinFiveFormula
  simp only [Fin.sum_univ_succ]
  simp [Fin.succAbove]
  unfold detFinFourFormula
  simp [Fin.succAbove, oppositeSixSiteCubic]
  set_option maxRecDepth 100000 in
    ring

/-- Raw pair on the one-dimensional opposite-site slice. -/
def oppositeMassPair (s : Real) : Real × Real := ((5 : Real) / 6, s)

/-- Genuine positive-mass six-cycle on the opposite-site slice. -/
def oppositeSixSiteMassConfig (s : Real) : Lattice.PositiveMassConfig 6 :=
  twoSiteMassConfig frozenUnitMassSix
    (0 : Lattice.Site 6) (3 : Lattice.Site 6) (oppositeMassPair s)

/-- Genuine physical harmonic Hermitian matrix on the slice. -/
def oppositeSixSiteHarmonic (s : Real) : HermitianMatrix (Lattice.Site 6) :=
  twoSiteHarmonicHermitian frozenUnitMassSix
    (0 : Lattice.Site 6) (3 : Lattice.Site 6) (oppositeMassPair s)

theorem oppositeMassPair_mem_iidMassPairSupport
    {s : Real} (hs : s ∈ Set.Icc ((5 : Real) / 6) (7 / 6)) :
    oppositeMassPair s ∈ iidMassPairSupport := by
  rw [iidMassPairSupport]
  constructor
  · norm_num [oppositeMassPair, massSupport, massLower, massUpper]
  · norm_num [oppositeMassPair, massSupport, massLower, massUpper] at hs ⊢
    constructor <;> linarith

theorem inverseMassCoordinates_oppositeSixSiteMassConfig
    {s : Real} (hs : s ∈ Set.Icc ((5 : Real) / 6) (7 / 6)) :
    inverseMassCoordinates (oppositeSixSiteMassConfig s) =
      oppositeSixSiteInverseWeights ((6 : Real) / 5) s⁻¹ := by
  have hpair := oppositeMassPair_mem_iidMassPairSupport hs
  have hclip0 : clippedMass ((5 : Real) / 6) = 5 / 6 :=
    clippedMass_eq_self hpair.1
  have hclips : clippedMass s = s := clippedMass_eq_self hpair.2
  funext k
  fin_cases k <;>
    norm_num +decide [inverseMassCoordinates, oppositeSixSiteMassConfig,
      oppositeMassPair, oppositeSixSiteInverseWeights, siteEquivFin,
      twoSiteMassConfig, frozenUnitMassSix, hclip0, hclips]

/-- Characteristic polynomial of the genuine physical matrix on the slice. -/
theorem oppositeSixSiteHarmonic_charpoly_eval
    {s : Real} (hs : s ∈ Set.Icc ((5 : Real) / 6) (7 / 6))
    (energy : Real) :
    (Matrix.charpoly (Matrix.of (oppositeSixSiteHarmonic s).val)).eval energy =
      energy * (energy - 1) * (energy - 3) *
        oppositeSixSiteCubic ((6 : Real) / 5) s⁻¹ energy := by
  let m := oppositeSixSiteMassConfig s
  have hchar :
      (massWeightedHarmonicMatrix m).charpoly =
        (finWeightedCycleLaplacian (inverseMassCoordinates m)).charpoly := by
    calc
      (massWeightedHarmonicMatrix m).charpoly =
          (massWeightedDifferenceMatrix m *
            Matrix.transpose (massWeightedDifferenceMatrix m)).charpoly :=
        Matrix.charpoly_mul_comm
          (Matrix.transpose (massWeightedDifferenceMatrix m))
          (massWeightedDifferenceMatrix m)
      _ = (weightedCycleLaplacian (fun i => (m.mass i)⁻¹)).charpoly := by
        rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
      _ = (weightedCycleLaplacian
          (weightsOfCoordinates (inverseMassCoordinates m))).charpoly := by
        rw [weightsOfCoordinates_inverseMassCoordinates]
      _ = (finWeightedCycleLaplacian
          (inverseMassCoordinates m)).charpoly := by
        symm
        exact Matrix.charpoly_reindex _ _
  change (massWeightedHarmonicMatrix m).charpoly.eval energy = _
  rw [hchar, inverseMassCoordinates_oppositeSixSiteMassConfig hs,
    finWeightedCycleLaplacian_oppositeSixSiteInverseWeights]
  exact explicitSixSiteOppositeWeightLaplacian_charpoly_eval _ _ _

/-- Decreasing squared-frequency list at the left endpoint. -/
def leftOppositeOrderedEnergy : Fin 6 → Real :=
  ![((27 + Real.sqrt 249) / 10 : Real), 17 / 5, 3,
    (27 - Real.sqrt 249) / 10, 1, 0]

theorem sqrt249_sq : (Real.sqrt 249) ^ 2 = (249 : Real) := by
  exact Real.sq_sqrt (by norm_num)

theorem sqrt249_lower : (15 : Real) < Real.sqrt 249 := by
  have hs := Real.sqrt_nonneg (249 : Real)
  nlinarith [sqrt249_sq]

theorem sqrt249_upper : Real.sqrt 249 < (16 : Real) := by
  have hs := Real.sqrt_nonneg (249 : Real)
  nlinarith [sqrt249_sq]

theorem leftOppositeOrderedEnergy_antitone :
    Antitone leftOppositeOrderedEnergy := by
  intro i j hij
  have hlo := sqrt249_lower
  have hup := sqrt249_upper
  fin_cases i <;> fin_cases j <;>
    simp_all [leftOppositeOrderedEnergy, Fin.le_iff_val_le_val] <;> nlinarith

/-- Decreasing squared-frequency list at the right endpoint. -/
def rightOppositeOrderedEnergy : Fin 6 → Real :=
  ![((144 : Real) / 35), 3, 3, 1, 1, 0]

theorem rightOppositeOrderedEnergy_antitone :
    Antitone rightOppositeOrderedEnergy := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [rightOppositeOrderedEnergy, Fin.le_iff_val_le_val] <;> norm_num

set_option maxRecDepth 100000 in
theorem leftOppositeHarmonic_charpoly :
    Matrix.charpoly
        (Matrix.of (oppositeSixSiteHarmonic ((5 : Real) / 6)).val) =
      ∏ k : Fin 6,
        (Polynomial.X - Polynomial.C (leftOppositeOrderedEnergy k)) := by
  apply Polynomial.funext
  intro energy
  rw [oppositeSixSiteHarmonic_charpoly_eval
    (by norm_num : ((5 : Real) / 6) ∈ Set.Icc (5 / 6) (7 / 6))]
  simp [leftOppositeOrderedEnergy, Fin.prod_univ_succ,
    oppositeSixSiteCubic]
  ring_nf
  simp only [sqrt249_sq]
  ring

set_option maxRecDepth 100000 in
theorem rightOppositeHarmonic_charpoly :
    Matrix.charpoly
        (Matrix.of (oppositeSixSiteHarmonic ((7 : Real) / 6)).val) =
      ∏ k : Fin 6,
        (Polynomial.X - Polynomial.C (rightOppositeOrderedEnergy k)) := by
  apply Polynomial.funext
  intro energy
  rw [oppositeSixSiteHarmonic_charpoly_eval
    (by norm_num : ((7 : Real) / 6) ∈ Set.Icc (5 / 6) (7 / 6))]
  simp [rightOppositeOrderedEnergy, Fin.prod_univ_succ,
    oppositeSixSiteCubic]
  ring

theorem leftOppositeHarmonic_orderedEigenvalue (k : Fin 6) :
    orderedEigenvalue (oppositeSixSiteHarmonic ((5 : Real) / 6)) k =
      leftOppositeOrderedEnergy k := by
  exact orderedEigenvalue_eq_of_charpoly_eq_prod
    (oppositeSixSiteHarmonic ((5 : Real) / 6))
    leftOppositeOrderedEnergy leftOppositeOrderedEnergy_antitone
    leftOppositeHarmonic_charpoly k

theorem rightOppositeHarmonic_orderedEigenvalue (k : Fin 6) :
    orderedEigenvalue (oppositeSixSiteHarmonic ((7 : Real) / 6)) k =
      rightOppositeOrderedEnergy k := by
  exact orderedEigenvalue_eq_of_charpoly_eq_prod
    (oppositeSixSiteHarmonic ((7 : Real) / 6))
    rightOppositeOrderedEnergy rightOppositeOrderedEnergy_antitone
    rightOppositeHarmonic_charpoly k
theorem leftOpposite_parent_energy :
    orderedEigenvalue (oppositeSixSiteHarmonic ((5 : Real) / 6)) (0 : Fin 6) =
      (27 + Real.sqrt 249) / 10 := by
  simpa [leftOppositeOrderedEnergy] using
    leftOppositeHarmonic_orderedEigenvalue (0 : Fin 6)

theorem leftOpposite_child_energy :
    orderedEigenvalue (oppositeSixSiteHarmonic ((5 : Real) / 6)) (3 : Fin 6) =
      (27 - Real.sqrt 249) / 10 := by
  simpa [leftOppositeOrderedEnergy] using
    leftOppositeHarmonic_orderedEigenvalue (3 : Fin 6)

theorem rightOpposite_parent_energy :
    orderedEigenvalue (oppositeSixSiteHarmonic ((7 : Real) / 6)) (0 : Fin 6) =
      (144 : Real) / 35 := by
  simpa [rightOppositeOrderedEnergy] using
    rightOppositeHarmonic_orderedEigenvalue (0 : Fin 6)

theorem rightOpposite_child_energy :
    orderedEigenvalue (oppositeSixSiteHarmonic ((7 : Real) / 6)) (3 : Fin 6) = 1 := by
  simpa [rightOppositeOrderedEnergy] using
    rightOppositeHarmonic_orderedEigenvalue (3 : Fin 6)


/-- Child-repeated mismatch between parent mode zero and child mode three. -/
def oppositeChildRepeatedMismatch (s : Real) : Real :=
  childRepeatedDecayMismatch
    (actualTwoMassChildFrequencyChart frozenUnitMassSix
      (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3 (oppositeMassPair s))

theorem continuous_oppositeChildRepeatedMismatch :
    Continuous oppositeChildRepeatedMismatch := by
  unfold oppositeChildRepeatedMismatch childRepeatedDecayMismatch
    oppositeMassPair
  have hchart := continuous_actualTwoMassChildFrequencyChart frozenUnitMassSix
    (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3
  exact (continuous_fst.sub (continuous_const.mul continuous_snd)).comp
    (hchart.comp (continuous_const.prodMk continuous_id))

theorem oppositeChildRepeatedMismatch_left_neg :
    oppositeChildRepeatedMismatch ((5 : Real) / 6) < 0 := by
  have htop : 0 ≤ (27 + Real.sqrt 249) / 10 := by
    have hs := Real.sqrt_nonneg (249 : Real)
    positivity
  have hchild : 0 ≤ (27 - Real.sqrt 249) / 10 := by
    have hup := sqrt249_upper
    linarith
  have htopSq := Real.sq_sqrt htop
  have hchildSq := Real.sq_sqrt hchild
  have hsTop := Real.sqrt_nonneg ((27 + Real.sqrt 249) / 10)
  have hsChild := Real.sqrt_nonneg ((27 - Real.sqrt 249) / 10)
  rw [show oppositeChildRepeatedMismatch ((5 : Real) / 6) =
      Real.sqrt ((27 + Real.sqrt 249) / 10) -
        2 * Real.sqrt ((27 - Real.sqrt 249) / 10) by
    change
      Real.sqrt (orderedEigenvalue
          (oppositeSixSiteHarmonic ((5 : Real) / 6)) (0 : Fin 6)) -
        2 * Real.sqrt (orderedEigenvalue
          (oppositeSixSiteHarmonic ((5 : Real) / 6)) (3 : Fin 6)) = _
    rw [leftOpposite_parent_energy,
      leftOpposite_child_energy]]
  nlinarith [sqrt249_upper]

theorem oppositeChildRepeatedMismatch_right_pos :
    0 < oppositeChildRepeatedMismatch ((7 : Real) / 6) := by
  have hsqrt : (2 : Real) < Real.sqrt (144 / 35) := by
    apply (Real.lt_sqrt (by norm_num : (0 : Real) ≤ 2)).2
    norm_num
  rw [show oppositeChildRepeatedMismatch ((7 : Real) / 6) =
      Real.sqrt (144 / 35) - 2 by
    change
      Real.sqrt (orderedEigenvalue
          (oppositeSixSiteHarmonic ((7 : Real) / 6)) (0 : Fin 6)) -
        2 * Real.sqrt (orderedEigenvalue
          (oppositeSixSiteHarmonic ((7 : Real) / 6)) (3 : Fin 6)) = _
    rw [rightOpposite_parent_energy,
      rightOpposite_child_energy]
    norm_num]
  linarith

/-- There is an interior raw mass with exact parent-equals-twice-child
resonance. -/
theorem exists_interior_oppositeChildRepeated_exactResonance :
    ∃ s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6),
      oppositeChildRepeatedMismatch s = 0 := by
  have hzero : (0 : Real) ∈ Set.Ioo
      (oppositeChildRepeatedMismatch ((5 : Real) / 6))
      (oppositeChildRepeatedMismatch ((7 : Real) / 6)) :=
    ⟨oppositeChildRepeatedMismatch_left_neg,
      oppositeChildRepeatedMismatch_right_pos⟩
  have hzeroImage : (0 : Real) ∈ oppositeChildRepeatedMismatch ''
      Set.Ioo ((5 : Real) / 6) (7 / 6) :=
    intermediate_value_Ioo
      (by norm_num : ((5 : Real) / 6) ≤ 7 / 6)
      continuous_oppositeChildRepeatedMismatch.continuousOn hzero
  obtain ⟨s, hs, hres⟩ := hzeroImage
  exact ⟨s, hs, hres⟩

theorem opposite_parent_frequency_pos (s : Real) :
    0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 0 := by
  apply (orderedModeFrequency_pos_iff_ne_last_unconditional
    (oppositeSixSiteMassConfig s) 0).2
  decide

theorem opposite_child_frequency_pos (s : Real) :
    0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 3 := by
  apply (orderedModeFrequency_pos_iff_ne_last_unconditional
    (oppositeSixSiteMassConfig s) 3).2
  decide

/-- Exact interior resonance together with positivity of both participating
frequencies. -/
theorem exists_interior_positive_oppositeChildRepeated_exactResonance :
    ∃ s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6),
      oppositeChildRepeatedMismatch s = 0 ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 0 ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 3 := by
  obtain ⟨s, hs, hres⟩ :=
    exists_interior_oppositeChildRepeated_exactResonance
  exact ⟨s, hs, hres, opposite_parent_frequency_pos s,
    opposite_child_frequency_pos s⟩

end

end ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance

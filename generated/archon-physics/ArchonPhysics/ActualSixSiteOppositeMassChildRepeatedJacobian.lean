import ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedSimpleSpectrum
import ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial
import ArchonPhysics.HarmonicNormalizedEdgeFrame
import ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

/-!
# A true two-mass Jacobian at the opposite-site exact resonance

This file proves nondegeneracy of the genuine two-dimensional raw-mass
Fréchet derivative.  The proof does not differentiate an existential root
or the one-dimensional resonance slice.  Instead, two selected squared
frequencies are used to recover the elementary symmetric functions of the
two reciprocal masses from the exact characteristic cubic.  At resonance
the recovery determinant is uniformly nonzero.  Composing this recovery
map with the actual frequency chart identifies its derivative with an
explicit injective reciprocal-mass derivative, forcing the actual chart
Jacobian to be injective and hence to have nonzero determinant.
-/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedJacobian

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedSimpleSpectrum
open ArchonPhysics.ActualTwoMassRegularSpectralPatch
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open Filter Function Polynomial Set

noncomputable section

/-- The actual two-site physical mass family before restricting to the
one-dimensional resonance slice. -/
def oppositeTwoMassConfig (pair : Real × Real) :
    Lattice.PositiveMassConfig 6 :=
  twoSiteMassConfig frozenUnitMassSix
    (0 : Lattice.Site 6) (3 : Lattice.Site 6) pair

/-- The associated actual harmonic matrix. -/
def oppositeTwoMassHarmonic (pair : Real × Real) :
    HermitianMatrix (Lattice.Site 6) :=
  twoSiteHarmonicHermitian frozenUnitMassSix
    (0 : Lattice.Site 6) (3 : Lattice.Site 6) pair

@[simp] theorem oppositeTwoMassConfig_oppositeMassPair (s : Real) :
    oppositeTwoMassConfig (oppositeMassPair s) = oppositeSixSiteMassConfig s :=
  rfl

@[simp] theorem oppositeTwoMassHarmonic_oppositeMassPair (s : Real) :
    oppositeTwoMassHarmonic (oppositeMassPair s) = oppositeSixSiteHarmonic s :=
  rfl

/-- On the support square, the two varying reciprocal masses are exactly
the two non-unit weights in the explicit opposite-site Laplacian. -/
theorem inverseMassCoordinates_oppositeTwoMassConfig
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport) :
    inverseMassCoordinates (oppositeTwoMassConfig pair) =
      oppositeSixSiteInverseWeights pair.1⁻¹ pair.2⁻¹ := by
  have hclip₁ : clippedMass pair.1 = pair.1 := clippedMass_eq_self hpair.1
  have hclip₂ : clippedMass pair.2 = pair.2 := clippedMass_eq_self hpair.2
  funext k
  fin_cases k <;>
    norm_num +decide [inverseMassCoordinates, oppositeTwoMassConfig,
      oppositeSixSiteInverseWeights, siteEquivFin, twoSiteMassConfig,
      frozenUnitMassSix, hclip₁, hclip₂]

/-- Exact characteristic equation on the full two-dimensional support
square, rather than only on the one-dimensional resonance slice. -/
theorem oppositeTwoMassHarmonic_charpoly_eval
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (energy : Real) :
    (Matrix.charpoly (oppositeTwoMassHarmonic pair).1).eval energy =
      energy * (energy - 1) * (energy - 3) *
        oppositeSixSiteCubic pair.1⁻¹ pair.2⁻¹ energy := by
  let m := oppositeTwoMassConfig pair
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
      _ = (finWeightedCycleLaplacian (inverseMassCoordinates m)).charpoly := by
        symm
        exact Matrix.charpoly_reindex _ _
  change (massWeightedHarmonicMatrix m).charpoly.eval energy = _
  rw [hchar, inverseMassCoordinates_oppositeTwoMassConfig hpair,
    finWeightedCycleLaplacian_oppositeSixSiteInverseWeights]
  exact explicitSixSiteOppositeWeightLaplacian_charpoly_eval _ _ _

/-- Every mass in the clipped opposite-site family remains in the frozen
support interval. -/
theorem oppositeTwoMassConfig_mass_mem_support
    (pair : Real × Real) (i : Lattice.Site 6) :
    (oppositeTwoMassConfig pair).mass i ∈ massSupport := by
  by_cases hi₀ : i = (0 : Lattice.Site 6)
  · subst i
    simpa [oppositeTwoMassConfig, twoSiteMassConfig] using
      clippedMass_mem_support pair.1
  · by_cases hi₃ : i = (3 : Lattice.Site 6)
    · subst i
      simpa [oppositeTwoMassConfig, twoSiteMassConfig, hi₀] using
        clippedMass_mem_support pair.2
    · have hone : (1 : Real) ∈ massSupport := by
        norm_num [massSupport, massLower, massUpper]
      simpa [oppositeTwoMassConfig, twoSiteMassConfig, hi₀, hi₃,
        frozenUnitMassSix] using hone

/-- Uniform clean-spectrum comparison for the selected child energy. -/
theorem oppositeTwoMass_child_energy_bounds (pair : Real × Real) :
    (5 / 6 : Real) ≤ orderedEigenvalue (oppositeTwoMassHarmonic pair) 3 ∧
      orderedEigenvalue (oppositeTwoMassHarmonic pair) 3 ≤ (5 / 4 : Real) := by
  have hcompare := orderedEigenvalue_harmonic_compare_clean
    (oppositeTwoMassConfig pair) massLower massUpper massLower_pos
    (massLower_pos.trans_le massLower_le_massUpper)
    (fun i => (oppositeTwoMassConfig_mass_mem_support pair i).1)
    (fun i => (oppositeTwoMassConfig_mass_mem_support pair i).2)
    (3 : Fin 6)
  have hclean := orderedEigenvalue_cleanCycleHarmonic_six (3 : Fin 6)
  change orderedEigenvalue (cleanCycleHarmonicHermitian 6) (3 : Fin 6) = 1
    at hclean
  rw [hclean] at hcompare
  norm_num [massLower, massUpper] at hcompare
  convert hcompare using 1 <;> rfl

/-- The parameter-free part of the non-universal characteristic cubic. -/
def oppositeRootA (energy : Real) : Real :=
  energy ^ 3 - 4 * energy ^ 2 + 3 * energy

/-- Coefficient of `x+y` in the cubic. -/
def oppositeRootB (energy : Real) : Real :=
  -2 * energy ^ 2 + 6 * energy - 2

/-- Coefficient of `x*y` in the cubic. -/
def oppositeRootC (energy : Real) : Real :=
  4 * energy - 8

theorem oppositeSixSiteCubic_eq_root_linear
    (x y energy : Real) :
    oppositeSixSiteCubic x y energy =
      oppositeRootA energy + (x + y) * oppositeRootB energy +
        (x * y) * oppositeRootC energy := by
  simp [oppositeSixSiteCubic, oppositeRootA, oppositeRootB, oppositeRootC]
  ring

/-- Determinant of the two root equations used to recover `(x+y,x*y)`. -/
def oppositeRootLinearDet (energy : Real × Real) : Real :=
  oppositeRootB energy.1 * oppositeRootC energy.2 -
    oppositeRootB energy.2 * oppositeRootC energy.1

/-- Cramer's-rule recovery of the reciprocal-mass sum and product. -/
def oppositeRootCoefficientRecover (energy : Real × Real) : Real × Real :=
  ((oppositeRootC energy.1 * oppositeRootA energy.2 -
      oppositeRootC energy.2 * oppositeRootA energy.1) /
      oppositeRootLinearDet energy,
    (oppositeRootB energy.2 * oppositeRootA energy.1 -
      oppositeRootB energy.1 * oppositeRootA energy.2) /
      oppositeRootLinearDet energy)

/-- Squaring the two physical frequencies. -/
def oppositeFrequencyEnergy (frequency : Real × Real) : Real × Real :=
  (frequency.1 ^ 2, frequency.2 ^ 2)

/-- An invertible affine-linear postprocessing of the recovered sum and
product, chosen to match the existing explicit three-site symmetric map. -/
def oppositeRecoveredThreeSiteSymmetric (frequency : Real × Real) :
    Real × Real :=
  let coefficient :=
    oppositeRootCoefficientRecover (oppositeFrequencyEnergy frequency)
  (2 * (coefficient.1 + 1), 3 * (coefficient.2 + coefficient.1))

/-- Exact Cramer's-rule soundness for any two roots with nonzero recovery
determinant. -/
theorem oppositeRootCoefficientRecover_eq
    {alpha beta sigma pi : Real}
    (halpha : oppositeRootA alpha + sigma * oppositeRootB alpha +
      pi * oppositeRootC alpha = 0)
    (hbeta : oppositeRootA beta + sigma * oppositeRootB beta +
      pi * oppositeRootC beta = 0)
    (hdet : oppositeRootLinearDet (alpha, beta) ≠ 0) :
    oppositeRootCoefficientRecover (alpha, beta) = (sigma, pi) := by
  have hsum :
      oppositeRootC alpha * oppositeRootA beta -
          oppositeRootC beta * oppositeRootA alpha =
        sigma * oppositeRootLinearDet (alpha, beta) := by
    dsimp [oppositeRootLinearDet]
    linear_combination oppositeRootC alpha * hbeta -
      oppositeRootC beta * halpha
  have hprod :
      oppositeRootB beta * oppositeRootA alpha -
          oppositeRootB alpha * oppositeRootA beta =
        pi * oppositeRootLinearDet (alpha, beta) := by
    dsimp [oppositeRootLinearDet]
    linear_combination oppositeRootB beta * halpha -
      oppositeRootB alpha * hbeta
  apply Prod.ext
  · dsimp [oppositeRootCoefficientRecover]
    exact (div_eq_iff hdet).2 hsum
  · dsimp [oppositeRootCoefficientRecover]
    exact (div_eq_iff hdet).2 hprod

/-- Selected squared-frequency pair in decreasing mode order `(0,3)`. -/
def oppositeSelectedEnergy (pair : Real × Real) : Real × Real :=
  (orderedEigenvalue (oppositeTwoMassHarmonic pair) 0,
    orderedEigenvalue (oppositeTwoMassHarmonic pair) 3)

/-- Squaring the actual selected frequency chart gives exactly the selected
ordered-energy pair. -/
theorem oppositeFrequencyEnergy_actualChart (pair : Real × Real) :
    oppositeFrequencyEnergy
        (actualTwoMassChildFrequencyChart frozenUnitMassSix
          (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3 pair) =
      oppositeSelectedEnergy pair := by
  apply Prod.ext
  · change orderedModeFrequency
      (harmonicHermitian (oppositeTwoMassConfig pair)) 0 ^ 2 =
        orderedEigenvalue (harmonicHermitian (oppositeTwoMassConfig pair)) 0
    exact orderedModeFrequency_sq_eq_orderedEigenvalue
      (oppositeTwoMassConfig pair) (0 : Fin 6)
  · change orderedModeFrequency
      (harmonicHermitian (oppositeTwoMassConfig pair)) 3 ^ 2 =
        orderedEigenvalue (harmonicHermitian (oppositeTwoMassConfig pair)) 3
    exact orderedModeFrequency_sq_eq_orderedEigenvalue
      (oppositeTwoMassConfig pair) (3 : Fin 6)

/-- Any selected ordered energy away from the structural roots belongs to
the non-universal cubic factor. -/
theorem opposite_orderedEnergy_cubic_root_of_structural_ne
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (k : Fin 6)
    (hstruct :
      let energy := orderedEigenvalue (oppositeTwoMassHarmonic pair) k
      energy * (energy - 1) * (energy - 3) ≠ 0) :
    oppositeSixSiteCubic pair.1⁻¹ pair.2⁻¹
      (orderedEigenvalue (oppositeTwoMassHarmonic pair) k) = 0 := by
  let energy := orderedEigenvalue (oppositeTwoMassHarmonic pair) k
  have hroot :
      (Matrix.charpoly (oppositeTwoMassHarmonic pair).1).eval energy = 0 :=
    charpoly_eval_orderedEigenvalue_eq_zero
      (oppositeTwoMassHarmonic pair) k
  rw [oppositeTwoMassHarmonic_charpoly_eval hpair] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left hstruct

/-- Pointwise recovery identity for the genuine chart whenever its two
selected energies avoid the structural roots and the recovery determinant
is nonzero. -/
theorem oppositeRecoveredThreeSiteSymmetric_actualChart
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hparentStruct :
      let alpha := (oppositeSelectedEnergy pair).1
      alpha * (alpha - 1) * (alpha - 3) ≠ 0)
    (hchildStruct :
      let beta := (oppositeSelectedEnergy pair).2
      beta * (beta - 1) * (beta - 3) ≠ 0)
    (hdet : oppositeRootLinearDet (oppositeSelectedEnergy pair) ≠ 0) :
    oppositeRecoveredThreeSiteSymmetric
        (actualTwoMassChildFrequencyChart frozenUnitMassSix
          (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3 pair) =
      inverseMassEnergySymmetric pair := by
  let alpha := (oppositeSelectedEnergy pair).1
  let beta := (oppositeSelectedEnergy pair).2
  have hrootAlpha := opposite_orderedEnergy_cubic_root_of_structural_ne
    hpair (0 : Fin 6) hparentStruct
  have hrootBeta := opposite_orderedEnergy_cubic_root_of_structural_ne
    hpair (3 : Fin 6) hchildStruct
  have halpha :
      oppositeRootA alpha + (pair.1⁻¹ + pair.2⁻¹) * oppositeRootB alpha +
        (pair.1⁻¹ * pair.2⁻¹) * oppositeRootC alpha = 0 := by
    rw [← oppositeSixSiteCubic_eq_root_linear]
    exact hrootAlpha
  have hbeta :
      oppositeRootA beta + (pair.1⁻¹ + pair.2⁻¹) * oppositeRootB beta +
        (pair.1⁻¹ * pair.2⁻¹) * oppositeRootC beta = 0 := by
    rw [← oppositeSixSiteCubic_eq_root_linear]
    exact hrootBeta
  have hrecover : oppositeRootCoefficientRecover (alpha, beta) =
      (pair.1⁻¹ + pair.2⁻¹, pair.1⁻¹ * pair.2⁻¹) :=
    oppositeRootCoefficientRecover_eq halpha hbeta hdet
  rw [oppositeRecoveredThreeSiteSymmetric,
    oppositeFrequencyEnergy_actualChart]
  change
    (2 * ((oppositeRootCoefficientRecover (alpha, beta)).1 + 1),
      3 * ((oppositeRootCoefficientRecover (alpha, beta)).2 +
        (oppositeRootCoefficientRecover (alpha, beta)).1)) = _
  rw [hrecover]
  simp [inverseMassEnergySymmetric]
  ring

/-- On a child-repeated resonance ray `alpha=4 beta`, the recovery
determinant has a simple explicit factorization. -/
theorem oppositeRootLinearDet_resonance (energy : Real) :
    oppositeRootLinearDet (4 * energy, energy) =
      -24 * energy * (4 * energy ^ 2 - 10 * energy + 5) := by
  simp [oppositeRootLinearDet, oppositeRootB, oppositeRootC]
  ring

/-- The recovery determinant is nonzero throughout the clean-comparison
window for the selected child energy. -/
theorem oppositeRootLinearDet_resonance_ne_zero
    {energy : Real} (henergy : energy ∈ Set.Icc ((5 : Real) / 6) (5 / 4)) :
    oppositeRootLinearDet (4 * energy, energy) ≠ 0 := by
  rw [oppositeRootLinearDet_resonance]
  have henergyPos : 0 < energy := lt_of_lt_of_le (by norm_num) henergy.1
  have hfirst : 0 ≤ energy - (5 : Real) / 6 := sub_nonneg.mpr henergy.1
  have hsecond : 4 * (energy + (5 : Real) / 6) - 10 < 0 := by
    linarith [henergy.2]
  have hproduct :
      (energy - (5 : Real) / 6) *
          (4 * (energy + (5 : Real) / 6) - 10) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfirst (le_of_lt hsecond)
  have hquadratic : 4 * energy ^ 2 - 10 * energy + 5 < 0 := by
    nlinarith [hproduct]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt henergyPos))
    (ne_of_lt hquadratic)

/-- The raw slice point is genuinely interior to the two-dimensional iid
mass square. -/
theorem oppositeMassPair_mem_interior
    {s : Real} (hs : s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6)) :
    oppositeMassPair s ∈ interior iidMassPairSupport := by
  rw [iidMassPairSupport, interior_prod_eq]
  constructor
  · norm_num [oppositeMassPair, massSupport, massLower, massUpper]
  · norm_num [oppositeMassPair, massSupport, massLower, massUpper] at hs ⊢
    constructor <;> linarith

/-- At an interior exact resonance, the parent and child selected energies
avoid the structural factors and the root-recovery determinant is nonzero. -/
theorem exactResonance_structural_and_recovery_regular
    {s : Real} (hs : s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6))
    (hres : oppositeChildRepeatedMismatch s = 0) :
    (let alpha := (oppositeSelectedEnergy (oppositeMassPair s)).1
     alpha * (alpha - 1) * (alpha - 3) ≠ 0) ∧
    (let beta := (oppositeSelectedEnergy (oppositeMassPair s)).2
     beta * (beta - 1) * (beta - 3) ≠ 0) ∧
    oppositeRootLinearDet
      (oppositeSelectedEnergy (oppositeMassPair s)) ≠ 0 := by
  let pair := oppositeMassPair s
  let alpha := (oppositeSelectedEnergy pair).1
  let beta := (oppositeSelectedEnergy pair).2
  have hpairSupport : pair ∈ iidMassPairSupport :=
    interior_subset (oppositeMassPair_mem_interior hs)
  have hbounds : beta ∈ Set.Icc ((5 : Real) / 6) (5 / 4) := by
    simpa [beta, pair, oppositeSelectedEnergy] using
      oppositeTwoMass_child_energy_bounds pair
  have hfrequency :
      orderedModeFrequency (oppositeSixSiteHarmonic s) 0 =
        2 * orderedModeFrequency (oppositeSixSiteHarmonic s) 3 := by
    change
      orderedModeFrequency (oppositeSixSiteHarmonic s) 0 -
        2 * orderedModeFrequency (oppositeSixSiteHarmonic s) 3 = 0 at hres
    linarith
  have halphaBeta : alpha = 4 * beta := by
    have hfrequencyPair :
        (actualTwoMassChildFrequencyChart frozenUnitMassSix
          (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3 pair).1 =
        2 * (actualTwoMassChildFrequencyChart frozenUnitMassSix
          (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3 pair).2 := by
      simpa [pair, actualTwoMassChildFrequencyChart, oppositeSixSiteHarmonic]
        using hfrequency
    have hparentSq := congrArg Prod.fst
      (oppositeFrequencyEnergy_actualChart pair)
    have hchildSq := congrArg Prod.snd
      (oppositeFrequencyEnergy_actualChart pair)
    change (actualTwoMassChildFrequencyChart frozenUnitMassSix
      (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3 pair).1 ^ 2 = alpha
      at hparentSq
    change (actualTwoMassChildFrequencyChart frozenUnitMassSix
      (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3 pair).2 ^ 2 = beta
      at hchildSq
    rw [← hparentSq, ← hchildSq, hfrequencyPair]
    ring
  have halphaGtThree : 3 < alpha := by
    rw [halphaBeta]
    nlinarith [hbounds.1]
  have hparentStruct : alpha * (alpha - 1) * (alpha - 3) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (ne_of_gt (lt_trans (by norm_num) halphaGtThree))
        (sub_ne_zero.mpr (ne_of_gt (lt_trans (by norm_num) halphaGtThree))))
      (sub_ne_zero.mpr (ne_of_gt halphaGtThree))
  have hbetaPos : 0 < beta := lt_of_lt_of_le (by norm_num) hbounds.1
  have hbetaLtThree : beta < 3 := lt_of_le_of_lt hbounds.2 (by norm_num)
  have hparentRoot :
      oppositeSixSiteCubic pair.1⁻¹ pair.2⁻¹ alpha = 0 := by
    exact opposite_orderedEnergy_cubic_root_of_structural_ne
      hpairSupport (0 : Fin 6) hparentStruct
  have hbetaNeOne : beta ≠ 1 := by
    intro hbetaOne
    have halphaFour : alpha = 4 := by rw [halphaBeta, hbetaOne]; norm_num
    have hsPos : 0 < s := lt_trans (by norm_num) hs.1
    have hinvPos : 0 < s⁻¹ := inv_pos.mpr hsPos
    have hformula :
        oppositeSixSiteCubic ((6 : Real) / 5) s⁻¹ 4 =
          -((2 : Real) / 5) * s⁻¹ := by
      simp [oppositeSixSiteCubic]
      ring
    have hpairFirst : pair.1⁻¹ = (6 : Real) / 5 := by
      norm_num [pair, oppositeMassPair]
    have hpairSecond : pair.2⁻¹ = s⁻¹ := by rfl
    rw [halphaFour, hpairFirst, hpairSecond, hformula] at hparentRoot
    nlinarith
  have hchildStruct : beta * (beta - 1) * (beta - 3) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (ne_of_gt hbetaPos) (sub_ne_zero.mpr hbetaNeOne))
      (sub_ne_zero.mpr (ne_of_lt hbetaLtThree))
  have hdet : oppositeRootLinearDet (oppositeSelectedEnergy pair) ≠ 0 := by
    change oppositeRootLinearDet (alpha, beta) ≠ 0
    rw [halphaBeta]
    exact oppositeRootLinearDet_resonance_ne_zero hbounds
  exact ⟨hparentStruct, hchildStruct, hdet⟩

/-- The actual two-frequency raw-mass Jacobian is nondegenerate at every
interior exact resonance on the opposite-site slice. -/
theorem actualOppositeChildFrequencyJacobian_det_ne_zero
    {s : Real} (hs : s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6))
    (hres : oppositeChildRepeatedMismatch s = 0) :
    (actualTwoMassChildFrequencyJacobian frozenUnitMassSix
      (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3
      (oppositeMassPair s)).det ≠ 0 := by
  let pair := oppositeMassPair s
  let chart := actualTwoMassChildFrequencyChart frozenUnitMassSix
    (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3
  let J := actualTwoMassChildFrequencyJacobian frozenUnitMassSix
    (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3 pair
  have hpair : pair ∈ interior iidMassPairSupport :=
    oppositeMassPair_mem_interior hs
  have hsimple : SimpleOrderedSpectrum (oppositeTwoMassHarmonic pair) := by
    simpa [pair] using oppositeSixSiteHarmonic_simpleOrderedSpectrum hs
  have hregular := exactResonance_structural_and_recovery_regular hs hres
  have hparentStruct := hregular.1
  have hchildStruct := hregular.2.1
  have hrootDet := hregular.2.2
  have hparentFreq : 0 < (chart pair).1 := by
    change 0 < orderedModeFrequency (oppositeTwoMassHarmonic pair) 0
    simpa [pair] using opposite_parent_frequency_pos s
  have hchildFreq : 0 < (chart pair).2 := by
    change 0 < orderedModeFrequency (oppositeTwoMassHarmonic pair) 3
    simpa [pair] using opposite_child_frequency_pos s
  have hparentEnergy : 0 < orderedEigenvalue (oppositeTwoMassHarmonic pair) 0 := by
    have hsq := sq_pos_of_pos hparentFreq
    have heq := congrArg Prod.fst
      (oppositeFrequencyEnergy_actualChart pair)
    change (chart pair).1 ^ 2 =
      orderedEigenvalue (oppositeTwoMassHarmonic pair) 0 at heq
    rw [heq] at hsq
    exact hsq
  have hchildEnergy : 0 < orderedEigenvalue (oppositeTwoMassHarmonic pair) 3 := by
    have hsq := sq_pos_of_pos hchildFreq
    have heq := congrArg Prod.snd
      (oppositeFrequencyEnergy_actualChart pair)
    change (chart pair).2 ^ 2 =
      orderedEigenvalue (oppositeTwoMassHarmonic pair) 3 at heq
    rw [heq] at hsq
    exact hsq
  obtain ⟨chartDerivative, hchartDerivative⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassChildFrequencyChart
      frozenUnitMassSix (by decide : (0 : Lattice.Site 6) ≠ 3)
      hpair hsimple 0 3 hparentEnergy hchildEnergy
  have hJ : J = chartDerivative := by
    simpa [J, chart, actualTwoMassChildFrequencyJacobian] using
      hchartDerivative.hasFDerivAt.fderiv
  have hchartJ : HasFDerivAt chart J pair := by
    rw [hJ]
    exact hchartDerivative.hasFDerivAt
  have hchartRootDet :
      oppositeRootLinearDet (oppositeFrequencyEnergy (chart pair)) ≠ 0 := by
    rw [oppositeFrequencyEnergy_actualChart]
    exact hrootDet
  unfold oppositeRootLinearDet oppositeFrequencyEnergy oppositeRootB
    oppositeRootC at hchartRootDet
  have houter : DifferentiableAt Real oppositeRecoveredThreeSiteSymmetric
      (chart pair) := by
    unfold oppositeRecoveredThreeSiteSymmetric oppositeRootCoefficientRecover
      oppositeFrequencyEnergy oppositeRootLinearDet oppositeRootA oppositeRootB
      oppositeRootC
    fun_prop (disch := assumption)
  have hcomposition : HasFDerivAt
      (fun nearby => oppositeRecoveredThreeSiteSymmetric (chart nearby))
      (fderiv Real oppositeRecoveredThreeSiteSymmetric (chart pair) ∘L J)
      pair := by
    simpa [Function.comp_def] using houter.hasFDerivAt.comp pair hchartJ
  have hcontinuousSelected : Continuous
      (fun nearby => oppositeSelectedEnergy nearby) := by
    unfold oppositeSelectedEnergy oppositeTwoMassHarmonic
    exact
      ((continuous_orderedEigenvalue 0).comp
        (continuous_twoSiteHarmonicHermitian frozenUnitMassSix
          (0 : Lattice.Site 6) (3 : Lattice.Site 6))).prodMk
      ((continuous_orderedEigenvalue 3).comp
        (continuous_twoSiteHarmonicHermitian frozenUnitMassSix
          (0 : Lattice.Site 6) (3 : Lattice.Site 6)))
  have heventParent : ∀ᶠ nearby in nhds pair,
      let alpha := (oppositeSelectedEnergy nearby).1
      alpha * (alpha - 1) * (alpha - 3) ≠ 0 := by
    have hc : Continuous fun nearby =>
        let alpha := (oppositeSelectedEnergy nearby).1
        alpha * (alpha - 1) * (alpha - 3) :=
      (hcontinuousSelected.fst.mul
        (hcontinuousSelected.fst.sub continuous_const)).mul
          (hcontinuousSelected.fst.sub continuous_const)
    exact hc.continuousAt.eventually_ne hparentStruct
  have heventChild : ∀ᶠ nearby in nhds pair,
      let beta := (oppositeSelectedEnergy nearby).2
      beta * (beta - 1) * (beta - 3) ≠ 0 := by
    have hc : Continuous fun nearby =>
        let beta := (oppositeSelectedEnergy nearby).2
        beta * (beta - 1) * (beta - 3) :=
      (hcontinuousSelected.snd.mul
        (hcontinuousSelected.snd.sub continuous_const)).mul
          (hcontinuousSelected.snd.sub continuous_const)
    exact hc.continuousAt.eventually_ne hchildStruct
  have heventDet : ∀ᶠ nearby in nhds pair,
      oppositeRootLinearDet (oppositeSelectedEnergy nearby) ≠ 0 := by
    have hB : Continuous oppositeRootB := by
      unfold oppositeRootB
      fun_prop
    have hC : Continuous oppositeRootC := by
      unfold oppositeRootC
      fun_prop
    have hc : Continuous fun nearby =>
        oppositeRootLinearDet (oppositeSelectedEnergy nearby) := by
      unfold oppositeRootLinearDet
      exact ((hB.comp hcontinuousSelected.fst).mul
        (hC.comp hcontinuousSelected.snd)).sub
          ((hB.comp hcontinuousSelected.snd).mul
            (hC.comp hcontinuousSelected.fst))
    exact hc.continuousAt.eventually_ne hrootDet
  have heventIdentity :
      (fun nearby => oppositeRecoveredThreeSiteSymmetric (chart nearby))
        =ᶠ[nhds pair] inverseMassEnergySymmetric := by
    filter_upwards [isOpen_interior.mem_nhds hpair,
      heventParent, heventChild, heventDet] with nearby hnearby
        hparentNearby hchildNearby hdetNearby
    exact oppositeRecoveredThreeSiteSymmetric_actualChart
      (interior_subset hnearby) hparentNearby hchildNearby hdetNearby
  have hinverseByComposition : HasFDerivAt inverseMassEnergySymmetric
      (fderiv Real oppositeRecoveredThreeSiteSymmetric (chart pair) ∘L J)
      pair :=
    hcomposition.congr_of_eventuallyEq heventIdentity.symm
  have hmassNe : pair.1 ≠ pair.2 := by
    dsimp [pair, oppositeMassPair]
    linarith [hs.1]
  obtain ⟨explicitDerivative, hexplicitDerivative, hexplicitInjective⟩ :=
    exists_hasFDerivAt_inverseMassEnergySymmetric_injective
      (interior_subset hpair) hmassNe
  have hderivativeEquality :
      explicitDerivative =
        fderiv Real oppositeRecoveredThreeSiteSymmetric (chart pair) ∘L J :=
    hexplicitDerivative.unique hinverseByComposition
  have hJInjective : Function.Injective J := by
    intro u v huv
    apply hexplicitInjective
    rw [hderivativeEquality]
    exact congrArg
      (fderiv Real oppositeRecoveredThreeSiteSymmetric (chart pair)) huv
  have hker : J.ker = ⊥ := LinearMap.ker_eq_bot.mpr hJInjective
  have hdetLinear : LinearMap.det J.toLinearMap ≠ 0 := by
    intro hzero
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) hker
  simpa [J, ContinuousLinearMap.det] using hdetLinear

/-- The exact resonance seed can be chosen with full simple spectrum,
positive selected modes, and a nonzero true two-mass frequency Jacobian. -/
theorem exists_interior_simple_positive_jacobian_oppositeChildRepeated_exactResonance :
    ∃ s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6),
      oppositeChildRepeatedMismatch s = 0 ∧
      SimpleOrderedSpectrum (oppositeSixSiteHarmonic s) ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 0 ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 3 ∧
      (actualTwoMassChildFrequencyJacobian frozenUnitMassSix
        (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3
        (oppositeMassPair s)).det ≠ 0 := by
  obtain ⟨s, hs, hres, hsimple, hparent, hchild⟩ :=
    exists_interior_simple_positive_oppositeChildRepeated_exactResonance
  exact ⟨s, hs, hres, hsimple, hparent, hchild,
    actualOppositeChildFrequencyJacobian_det_ne_zero hs hres⟩

end

end ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedJacobian

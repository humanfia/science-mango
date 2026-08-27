import ArchonPhysics.ActualFourSitePositiveProjectorWitness
import ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
import ArchonPhysics.ActualSixSiteNearResonantPathSeparable

/-!
# Simple spectrum along the six-site near-resonant mass path

This module transports the exact characteristic polynomial of the explicit
two-weight six-cycle back to the physical three-mass harmonic matrix.  The
Bezout certificate for the one-parameter quintic then gives simple ordered
spectrum at every supported nonzero path point away from the two reciprocal
mass poles.
-/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum

open ArchonPhysics
open ArchonPhysics.ActualFourSitePositiveProjectorWitness
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathSeparable
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Polynomial
open Set

noncomputable section

@[simp] theorem nearResonantMassTriple_zero :
    nearResonantMassTriple 0 = unitMassTriple := by
  norm_num [nearResonantMassTriple, unitMassTriple]

theorem continuous_nearResonantMassTriple :
    Continuous nearResonantMassTriple := by
  unfold nearResonantMassTriple
  fun_prop

/-- The abstract weighted-cycle matrix on the reciprocal-mass path is the
displayed six-by-six matrix used by the exact determinant computation. -/
theorem finWeightedCycleLaplacian_nearResonantInverseWeights (t : Real) :
    finWeightedCycleLaplacian (nearResonantInverseWeights t) =
      explicitSixSiteNearResonantLaplacian t := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_succ]
  <;> norm_num +decide [nearResonantInverseWeights,
    explicitSixSiteNearResonantLaplacian,
    explicitSixSiteTwoWeightLaplacian, finCycleEdgeVector,
    SingleMassRankOnePerturbation.cycleMassPerturbationVector,
    differenceMatrix, siteEquivFin]
  all_goals simp
  all_goals ring

/-- The inverse-coordinate embedding of the raw mass path agrees with the
explicit reciprocal-weight path. -/
theorem sixSiteSliceInverseWeights_nearResonantMassTriple (t : Real) :
    sixSiteSliceInverseWeights
        (iidInverseMassTripleCoordinates (nearResonantMassTriple t)) =
      nearResonantInverseWeights t := by
  funext k
  fin_cases k <;>
    simp [sixSiteSliceInverseWeights, iidInverseMassTripleCoordinates,
      nearResonantMassTriple, nearResonantInverseWeights]

/-- Characteristic equation of the genuine physical six-site matrix along
the reciprocal-mass path. -/
theorem actualSixSiteNearResonant_charpoly_eval
    {t : Real}
    (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0) (energy : Real) :
    (Matrix.charpoly
      (Matrix.of (actualSixSiteThreeMassHarmonic
        (nearResonantMassTriple t)).val)).eval energy =
      energy / (1 - t ^ 2) *
        ((1 - t ^ 2) * energy ^ 5 +
          (-12 + 8 * t ^ 2) * energy ^ 4 +
          (54 - 21 * t ^ 2) * energy ^ 3 +
          (-112 + 20 * t ^ 2) * energy ^ 2 +
          (105 - 5 * t ^ 2) * energy - 36) := by
  let m := actualSixSiteThreeMassConfig (nearResonantMassTriple t)
  have hchar :
      (massWeightedHarmonicMatrix m).charpoly =
        (finWeightedCycleLaplacian
          (inverseMassCoordinates m)).charpoly := by
    calc
      (massWeightedHarmonicMatrix m).charpoly =
          (massWeightedDifferenceMatrix m *
            Matrix.transpose (massWeightedDifferenceMatrix m)).charpoly := by
        exact Matrix.charpoly_mul_comm
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
  rw [hchar,
    inverseMassCoordinates_actualSixSiteThreeMassConfig hsupport,
    sixSiteSliceInverseWeights_nearResonantMassTriple,
    finWeightedCycleLaplacian_nearResonantInverseWeights]
  exact explicitSixSiteNearResonantLaplacian_charpoly_eval t energy hpole

/-- A nonzero scalar multiple of a separable polynomial remains separable. -/
theorem separable_C_mul_of_ne_zero
    {c : Real} (hc : c ≠ 0) {p : Real[X]} (hp : p.Separable) :
    (Polynomial.C c * p).Separable := by
  rw [Polynomial.separable_def] at hp ⊢
  have hunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  simpa [Polynomial.derivative_mul] using
    (isCoprime_mul_unit_left hunit p p.derivative).2 hp

/-- Polynomial identity behind the pathwise simple-spectrum certificate. -/
theorem actualSixSiteNearResonant_charpoly_eq
    {t : Real}
    (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0) :
    Matrix.charpoly
        (Matrix.of (actualSixSiteThreeMassHarmonic
          (nearResonantMassTriple t)).val) =
      Polynomial.C (1 - t ^ 2)⁻¹ *
        (Polynomial.X * nearResonantPathQuintic (t ^ 2)) := by
  apply Polynomial.funext
  intro energy
  rw [actualSixSiteNearResonant_charpoly_eval hsupport hpole]
  simp [nearResonantPathQuintic]
  field_simp [hpole]

/-- The physical six-site characteristic polynomial is separable at every
supported nonzero path point away from the reciprocal-mass poles. -/
theorem actualSixSiteNearResonant_charpoly_separable
    {t : Real} (ht : t ≠ 0)
    (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0) :
    (Matrix.charpoly
      (Matrix.of (actualSixSiteThreeMassHarmonic
        (nearResonantMassTriple t)).val)).Separable := by
  rw [actualSixSiteNearResonant_charpoly_eq hsupport hpole]
  exact separable_C_mul_of_ne_zero (inv_ne_zero hpole)
    (X_mul_nearResonantPathQuintic_separable_sq ht)

/-- The actual ordered spectrum is simple at every supported nonzero path
point away from the two reciprocal-mass poles. -/
theorem actualSixSiteNearResonant_simpleOrderedSpectrum
    {t : Real} (ht : t ≠ 0)
    (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0) :
    SimpleOrderedSpectrum
      (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)) := by
  apply simpleOrderedSpectrum_of_charpoly_separable
  exact actualSixSiteNearResonant_charpoly_separable ht hsupport hpole

end

end ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum

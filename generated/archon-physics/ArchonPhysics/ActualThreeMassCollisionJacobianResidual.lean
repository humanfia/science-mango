import ArchonPhysics.ActualThreeMassLiftedJacobianDeterminantIdentity

/-!
# Exact collision-weight / Jacobian residual

For the genuine three-mass random harmonic chart, this module divides the
physical normalized three-wave collision weight by the absolute lifted
Jacobian and simplifies every elementary scale.

The three positive-frequency normalization factors cancel exactly against
the Hellmann--Feynman row scales.  The three raw-mass column scales invert to
the product of the selected squared masses.  What remains is precisely one
inverse power of the genuine dual-cycle projector minor.  Thus projector
minor summability cannot by itself control the coarea density: a weighted
inverse-minor distribution estimate is still required.
-/

open scoped Matrix BigOperators

namespace ArchonPhysics.ActualThreeMassCollisionJacobianResidual

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedJacobianDeterminantIdentity
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Set

noncomputable section

/-- Exact residual after all frequency and mass-coordinate scale
cancellations.  The only remaining Jacobian singularity is the first inverse
power of the actual projector-weight minor. -/
theorem harmonicOrderedNormalizedInteractionWeight_div_abs_liftedJacobian_eq
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    harmonicOrderedNormalizedInteractionWeight
        (threeMassSiteConfig fixed site₀ site₁ site₂ triple) modes /
        |(actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes triple).det| =
      harmonicOrderedInteractionWeightSq
          (threeMassSiteConfig fixed site₀ site₁ site₂ triple) modes *
        (∏ s, (actualThreeMassRawCoordinate triple s) ^ 2) /
          |(actualThreeMassProjectorWeightMatrix
            fixed site₀ site₁ site₂ modes triple).det| := by
  rw [actualThreeMassLiftedFrequencyJacobian_det_eq_projectorScales
    fixed h₁₀ h₂₀ h₂₁ sign modes htriple hsimple hpositive]
  unfold harmonicOrderedNormalizedInteractionWeight
  change
    harmonicOrderedInteractionWeightSq
        (threeMassSiteConfig fixed site₀ site₁ site₂ triple) modes *
          (∏ r, actualThreeMassFrequencyRowScale
            fixed site₀ site₁ site₂ modes triple r) /
      |(sign 0).coefficient *
        ((∏ r, actualThreeMassFrequencyRowScale
          fixed site₀ site₁ site₂ modes triple r) *
          (actualThreeMassProjectorWeightMatrix
            fixed site₀ site₁ site₂ modes triple).det *
          (∏ s, actualThreeMassRawMassColumnScale triple s))| = _
  simp only [abs_mul, Finset.abs_prod]
  have hrow (r : Fin 3) : 0 < actualThreeMassFrequencyRowScale
      fixed site₀ site₁ site₂ modes triple r := by
    unfold actualThreeMassFrequencyRowScale orderedModeFrequency
    exact inv_pos.mpr
      (mul_pos (by norm_num) (Real.sqrt_pos.2 (hpositive r)))
  have hcolumn (s : Fin 3) :
      |actualThreeMassRawMassColumnScale triple s| =
        ((actualThreeMassRawCoordinate triple s) ^ 2)⁻¹ := by
    unfold actualThreeMassRawMassColumnScale
    rw [abs_neg, abs_of_pos]
    exact inv_pos.mpr (sq_pos_of_ne_zero
      (actualThreeMassRawCoordinate_ne_zero htriple s))
  simp_rw [abs_of_pos (hrow _), hcolumn]
  have hsign : |(sign 0).coefficient| = 1 := by
    cases sign 0 <;> simp
  rw [hsign, one_mul]
  simp only [Fin.prod_univ_three]
  by_cases hminor :
      (actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det = 0
  · simp [hminor]
  · have habsminor :
        |(actualThreeMassProjectorWeightMatrix
          fixed site₀ site₁ site₂ modes triple).det| ≠ 0 :=
      abs_ne_zero.mpr hminor
    field_simp [ne_of_gt (hrow 0), ne_of_gt (hrow 1),
      ne_of_gt (hrow 2)]

end

end ArchonPhysics.ActualThreeMassCollisionJacobianResidual

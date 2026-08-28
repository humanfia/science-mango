import ArchonPhysics.ActualThreeMassProjectorMinorSummability
import ArchonPhysics.ActualThreeMassWeightedProjectorMinorScaleBound

/-!
# Positive moment of the actual weighted projector minor

The global projector-minor sum rule combines with the physical acoustic
collision-weight ceiling and the frozen residual-scale ceiling to give an
explicit support-pointwise bound on the positive first moment of the actual
all-distinct weighted minor distribution.  The bound is `O(N⁻¹)` and requires
neither spectral simplicity nor projector-minor nonvanishing.

This is intentionally a positive moment.  It does not control the reciprocal
minor appearing in coarea and gives no small-minor tail estimate.
-/

open scoped Matrix BigOperators ENNReal

namespace ArchonPhysics.ActualThreeMassWeightedProjectorMinorPositiveMoment

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
open ArchonPhysics.ActualThreeMassProjectorMinorSummability
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorScaleBound
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- On every iid-support mass triple, the normalized physical residual weight
times the genuine actual projector minor has an explicit `48 / N` ceiling.
No simplicity, minor lower bound, or polynomial nonvanishing is assumed. -/
theorem actualThreeMassAllDistinctProjectorResidualMinorMoment_le
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (triple : MassTriple) (htriple : triple ∈ iidMassTripleSupport) :
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualThreeMassAllDistinctProjectorResidualWeight
              fixed site₀ site₁ site₂ modes triple *
            ENNReal.ofReal
              (actualThreeMassProjectorMinorMagnitude
                fixed site₀ site₁ site₂ modes triple) <=
      (N : ENNReal)⁻¹ *
        (actualThreeMassProjectorResidualScaleCeiling *
          ENNReal.ofReal
            (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) *
          48) := by
  classical
  let C : ENNReal :=
    actualThreeMassProjectorResidualScaleCeiling *
      ENNReal.ofReal (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8)
  have hweight (modes : OrderedModeTriple N) :
      actualThreeMassAllDistinctProjectorResidualWeight
          fixed site₀ site₁ site₂ modes triple <= C := by
    unfold actualThreeMassAllDistinctProjectorResidualWeight C
    calc
      _ <= ENNReal.ofReal
            (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) *
          actualThreeMassProjectorResidualScaleCeiling :=
        mul_le_mul
          (actualThreeMassAllDistinctTupleWeight_le_acousticCeiling
            fixed hfixed site₀ site₁ site₂ modes triple)
          (actualThreeMassProjectorResidualScale_le
            fixed hfixed site₀ site₁ site₂ modes triple htriple)
          bot_le bot_le
      _ = _ := by ac_rfl
  apply mul_le_mul_right _ _
  calc
    (∑ modes : OrderedModeTriple N,
        actualThreeMassAllDistinctProjectorResidualWeight
            fixed site₀ site₁ site₂ modes triple *
          ENNReal.ofReal
            (actualThreeMassProjectorMinorMagnitude
              fixed site₀ site₁ site₂ modes triple)) <=
      ∑ modes : OrderedModeTriple N,
        C * ENNReal.ofReal
          (actualThreeMassProjectorMinorMagnitude
            fixed site₀ site₁ site₂ modes triple) := by
      apply Finset.sum_le_sum
      intro modes _hmodes
      exact mul_le_mul (hweight modes) le_rfl bot_le bot_le
    _ = C * ENNReal.ofReal
        (∑ modes : OrderedModeTriple N,
          actualThreeMassProjectorMinorMagnitude
            fixed site₀ site₁ site₂ modes triple) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · rw [Finset.mul_sum]
      · intro modes _hmodes
        exact abs_nonneg _
    _ <= C * 48 := by
      simpa [actualThreeMassProjectorMinorMagnitude] using
        (mul_le_mul_right
          (ENNReal.ofReal_le_ofReal
            (actualThreeMassProjectorWeightMatrix_sum_abs_det_le_48_global
              hN fixed site₀ site₁ site₂ triple)) C)
    _ = _ := rfl

end

end ArchonPhysics.ActualThreeMassWeightedProjectorMinorPositiveMoment

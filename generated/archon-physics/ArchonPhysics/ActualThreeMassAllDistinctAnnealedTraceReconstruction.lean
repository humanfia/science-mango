import ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace

/-!
# Exact reconstruction of the all-distinct annealed trace

This layer identifies the explicit finite all-distinct sum with the
squared-sinc test of its scalar sector measure and with the genuine
three-mass conditional lifted chart.  The subsequent complement integral is
therefore an exact iid Fubini identity, not a quenched density assertion.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctAnnealedTraceReconstruction

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformCollisionDensityTransfer
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The explicit trace is exactly the normalized squared-sinc test of the
all-distinct scalar sector measure. -/
theorem allDistinctPerSiteBroadenedTrace_eq_lintegral
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) {T : Real} (hT : 0 < T) :
    allDistinctPerSiteBroadenedTrace mass sign T =
      ∫⁻ mismatch,
        ENNReal.ofReal
          (normalizedFiniteTimeResonanceKernel mismatch T)
        ∂(perSitePositiveWeightedMismatchFiniteMeasureWhere
          mass sign AllDistinctModes : Measure Real) := by
  classical
  unfold allDistinctPerSiteBroadenedTrace
    perSitePositiveWeightedMismatchFiniteMeasureWhere
  rw [FiniteMeasure.toMeasure_smul, lintegral_smul_measure]
  change (N : ENNReal)⁻¹ *
      (∑ modes : OrderedModeTriple N,
        if IsPositiveOrderedTriple mass modes ∧ AllDistinctModes modes then
          ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight mass modes) *
            ENNReal.ofReal (normalizedFiniteTimeResonanceKernel
              (orderedThreeWaveMismatch mass sign modes) T)
        else 0) =
    ((N : NNReal)⁻¹) • ∫⁻ mismatch,
      ENNReal.ofReal (normalizedFiniteTimeResonanceKernel mismatch T)
        ∂positiveWeightedMismatchMeasureWhere mass sign AllDistinctModes
  unfold positiveWeightedMismatchMeasureWhere
  rw [lintegral_finsetSum_measure]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro modes _hmodes
    by_cases hkeep :
        IsPositiveOrderedTriple mass modes ∧ AllDistinctModes modes
    · simp only [if_pos hkeep]
      rw [lintegral_smul_measure]
      rw [lintegral_dirac' _
        ((continuous_normalizedFiniteTimeResonanceKernel hT).measurable.ennreal_ofReal)]
      simp only [smul_eq_mul]
    · simp [hkeep]

end


end ArchonPhysics.ActualThreeMassAllDistinctAnnealedTraceReconstruction

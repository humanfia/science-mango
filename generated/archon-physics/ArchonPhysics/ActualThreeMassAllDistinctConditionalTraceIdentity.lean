import ArchonPhysics.ActualThreeMassAllDistinctAnnealedTraceReconstruction

/-!
# Conditional trace identity for the genuine three-mass chart

The all-distinct finite sum after replacing three physical masses is exactly
the mass of the genuine lifted, collision-weighted conditional child law.
This is the local identity used before integrating the complementary iid
environment.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctConditionalTraceIdentity

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformCollisionDensityTransfer
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Pointwise expansion of the resampled all-distinct trace in the exact
weight and lifted chart used by the coarea modules. -/
theorem allDistinctPerSiteBroadenedTrace_threeMassSiteConfig
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) (T : Real) (triple : MassTriple) :
    allDistinctPerSiteBroadenedTrace
        (threeMassSiteConfig fixed site₀ site₁ site₂ triple) sign T =
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes triple *
            liftedResonanceKernelDensity T
              (actualThreeMassLiftedFrequencyChart
                fixed site₀ site₁ site₂ sign modes triple) := by
  classical
  unfold allDistinctPerSiteBroadenedTrace
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hdistinct : AllDistinctModes modes
  · by_cases hpositive : IsPositiveOrderedTriple
        (threeMassSiteConfig fixed site₀ site₁ site₂ triple) modes
    · simp [actualThreeMassAllDistinctTupleWeight,
        actualThreeMassPositiveTupleWeight, hdistinct, hpositive,
        liftedResonanceKernelDensity,
        actualThreeMassLiftedFrequencyChart,
        threeMassHarmonicHermitian, orderedThreeWaveMismatch]
    · simp [actualThreeMassAllDistinctTupleWeight,
        actualThreeMassPositiveTupleWeight, hdistinct, hpositive]
  · simp [actualThreeMassAllDistinctTupleWeight, hdistinct]

/-- The total mass of one conditional tuple child law is the iid-triple
integral of its true collision weight times the lifted squared-sinc kernel. -/
theorem actualThreeMassConditionalTupleBroadenedChildMeasure_univ_eq_lintegral
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N)
    (weight : MassTriple → ENNReal) (hweight : Measurable weight)
    {T : Real} (hT : 0 < T) :
    actualThreeMassConditionalTupleBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign modes weight T Set.univ =
      ∫⁻ triple,
        weight triple *
          liftedResonanceKernelDensity T
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes triple)
        ∂iidMassTripleLaw := by
  unfold actualThreeMassConditionalTupleBroadenedChildMeasure
  rw [Measure.map_apply measurable_fst MeasurableSet.univ]
  simp only [preimage_univ]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [lintegral_map
    (measurable_liftedResonanceKernelDensity hT)
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable]
  have hkernelChart : Measurable fun triple =>
      liftedResonanceKernelDensity T
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes triple) :=
    (measurable_liftedResonanceKernelDensity hT).comp
      (continuous_actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes).measurable
  rw [lintegral_withDensity_eq_lintegral_mul
    iidMassTripleLaw hweight hkernelChart]
  rfl

end


end ArchonPhysics.ActualThreeMassAllDistinctConditionalTraceIdentity

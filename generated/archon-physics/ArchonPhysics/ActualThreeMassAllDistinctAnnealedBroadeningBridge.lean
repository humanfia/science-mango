import ArchonPhysics.ActualThreeMassAllDistinctConditionalTraceIdentity

/-!
# Annealed broadened trace bridge for the actual all-distinct sector

The genuine three-mass conditional trace is integrated over the finite iid
complement here.  The result is an expectation-level finite-volume theorem;
no realization-wise density claim is made.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningBridge

open ArchonPhysics
open ArchonPhysics.ActualLiftedMismatchSmallBall
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctConditionalTraceIdentity
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- Averaging the explicit resampled all-distinct trace over the selected iid
mass triple is exactly the total mass of the genuine conditional lifted child
law. -/
theorem lintegral_allDistinctPerSiteBroadenedTrace_threeMassSiteConfig_eq
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) {T : Real} (hT : 0 < T) :
    (∫⁻ triple,
      allDistinctPerSiteBroadenedTrace
        (threeMassSiteConfig fixed site₀ site₁ site₂ triple) sign T
      ∂iidMassTripleLaw) =
      actualThreeMassAllDistinctConditionalBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign T Set.univ := by
  classical
  have hsummandMeasurable (modes : OrderedModeTriple N) :
      Measurable fun triple =>
        actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes triple *
          liftedResonanceKernelDensity T
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes triple) :=
    (measurable_actualThreeMassAllDistinctTupleWeight
      fixed site₀ site₁ site₂ modes).mul
        ((measurable_liftedResonanceKernelDensity hT).comp
          (continuous_actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes).measurable)
  have hsumMeasurable : Measurable fun triple =>
      ∑ modes : OrderedModeTriple N,
        actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes triple *
          liftedResonanceKernelDensity T
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes triple) :=
    Finset.measurable_sum _ fun modes _hmodes => hsummandMeasurable modes
  calc
    (∫⁻ triple,
        allDistinctPerSiteBroadenedTrace
          (threeMassSiteConfig fixed site₀ site₁ site₂ triple) sign T
        ∂iidMassTripleLaw) =
      ∫⁻ triple,
        (N : ENNReal)⁻¹ *
          ∑ modes : OrderedModeTriple N,
            actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes triple *
              liftedResonanceKernelDensity T
                (actualThreeMassLiftedFrequencyChart
                  fixed site₀ site₁ site₂ sign modes triple)
        ∂iidMassTripleLaw := by
      apply lintegral_congr
      intro triple
      exact allDistinctPerSiteBroadenedTrace_threeMassSiteConfig
        fixed site₀ site₁ site₂ sign T triple
    _ = (N : ENNReal)⁻¹ *
        ∫⁻ triple,
          ∑ modes : OrderedModeTriple N,
            actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes triple *
              liftedResonanceKernelDensity T
                (actualThreeMassLiftedFrequencyChart
                  fixed site₀ site₁ site₂ sign modes triple)
          ∂iidMassTripleLaw :=
      lintegral_const_mul (N : ENNReal)⁻¹ hsumMeasurable
    _ = (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          ∫⁻ triple,
            actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes triple *
              liftedResonanceKernelDensity T
                (actualThreeMassLiftedFrequencyChart
                  fixed site₀ site₁ site₂ sign modes triple)
            ∂iidMassTripleLaw := by
      rw [lintegral_finsetSum Finset.univ]
      intro modes _hmodes
      exact hsummandMeasurable modes
    _ = (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualThreeMassConditionalTupleBroadenedChildMeasure
            fixed site₀ site₁ site₂ sign modes
              (actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes) T Set.univ := by
      congr 1
      apply Finset.sum_congr rfl
      intro modes _hmodes
      exact
        (actualThreeMassConditionalTupleBroadenedChildMeasure_univ_eq_lintegral
          fixed site₀ site₁ site₂ sign modes
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes)
          (measurable_actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes) hT).symm
    _ = actualThreeMassAllDistinctConditionalBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign T Set.univ := by
      unfold actualThreeMassAllDistinctConditionalBroadenedChildMeasure
        actualThreeMassConditionalPerSiteBroadenedChildMeasure
      rw [Measure.smul_apply, Measure.coe_finsetSum]
      simp only [Finset.sum_apply, smul_eq_mul]

end


end ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningBridge

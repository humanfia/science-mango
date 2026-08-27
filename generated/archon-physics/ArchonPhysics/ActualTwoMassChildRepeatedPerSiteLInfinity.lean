import ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
import ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit
import ArchonPhysics.ChildRepeatedScalarClusterHybridLift

/-!
# L-infinity closure of the child-repeated reduced law

The actual two-mass estimate is aggregated here for arbitrary measurable
subsets of the parent/child frequency plane, not only resonance strips.  A
uniform regular budget and a vanishing bad budget therefore give forward
absolute continuity, with an explicit `L∞` measure bound, for every reduced
parent/child weak cluster in a child-repeated hybrid lift.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.ActualTwoMassChildRepeatedPerSiteLInfinity

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ChildRepeatedCanonicalClusterLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedScalarClusterHybridLift
open ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralAveragingDensityUpper
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Arbitrary-set form of the exact per-site good/bad estimate. -/
theorem actualTwoMassChildRepeatedConditionalPerSite_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (weight : ChildRepeatedModePair N → Real × Real → ENNReal)
    (weightCeiling : ChildRepeatedModePair N → ENNReal)
    (hweight : ∀ modes, ∀ᵐ point ∂iidMassPairLaw,
      weight modes point ≤ weightCeiling modes)
    (good : ChildRepeatedModePair N → Set (Real × Real))
    (hgood : ∀ modes, MeasurableSet (good modes))
    (hderivative : ∀ modes point, point ∈ good modes →
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ modes.1 modes.2)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ modes.1 modes.2 point)
        (good modes) point)
    (hinjective : ∀ modes, InjOn
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ modes.1 modes.2) (good modes))
    (detLower : ChildRepeatedModePair N → Real)
    (hdetLower : ∀ modes, 0 < detLower modes)
    (hdet : ∀ modes point, point ∈ good modes →
      detLower modes ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ modes.1 modes.2 point).det|)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    actualTwoMassChildRepeatedConditionalPerSiteMeasure
        fixed site₁ site₂ weight target ≤
      actualTwoMassChildRepeatedRegularPerSiteBudget
          weightCeiling detLower *
        (volume : Measure (Real × Real)) target +
      actualTwoMassChildRepeatedBadPerSiteBudget weight good := by
  unfold actualTwoMassChildRepeatedConditionalPerSiteMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply]
  have hlocal : ∀ modes : ChildRepeatedModePair N,
      actualTwoMassChildRepeatedConditionalPairMeasure
          fixed site₁ site₂ modes (weight modes) target ≤
        (weightCeiling modes * 9 *
            (ENNReal.ofReal (detLower modes))⁻¹) *
            (volume : Measure (Real × Real)) target +
          (iidMassPairLaw.withDensity (weight modes)) (good modes)ᶜ := by
    intro modes
    exact actualTwoMass_boundedDensity_frequencyPair_apply_le
      fixed site₁ site₂ modes.1 modes.2
      (weight modes) (weightCeiling modes) (hweight modes)
      (hgood modes) (hderivative modes) (hinjective modes)
      (hdetLower modes) (hdet modes) htarget
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : ChildRepeatedModePair N,
          actualTwoMassChildRepeatedConditionalPairMeasure
            fixed site₁ site₂ modes (weight modes) target ≤
      (N : ENNReal)⁻¹ *
        ∑ modes : ChildRepeatedModePair N,
          ((weightCeiling modes * 9 *
              (ENNReal.ofReal (detLower modes))⁻¹) *
              (volume : Measure (Real × Real)) target +
            (iidMassPairLaw.withDensity (weight modes)) (good modes)ᶜ) :=
      mul_le_mul_right
        (Finset.sum_le_sum fun modes _ => hlocal modes) _
    _ = actualTwoMassChildRepeatedRegularPerSiteBudget
          weightCeiling detLower *
          (volume : Measure (Real × Real)) target +
        actualTwoMassChildRepeatedBadPerSiteBudget weight good := by
      unfold actualTwoMassChildRepeatedRegularPerSiteBudget
        actualTwoMassChildRepeatedBadPerSiteBudget
      rw [Finset.sum_add_distrib, mul_add, ← Finset.sum_mul]
      ac_rfl

/-- Uniform bounds on the exact regular and bad budgets give an arbitrary-set
planar density estimate. -/
theorem actualTwoMassChildRepeatedConditionalPerSite_apply_le_of_budgets
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (weight : ChildRepeatedModePair N → Real × Real → ENNReal)
    (weightCeiling : ChildRepeatedModePair N → ENNReal)
    (hweight : ∀ modes, ∀ᵐ point ∂iidMassPairLaw,
      weight modes point ≤ weightCeiling modes)
    (good : ChildRepeatedModePair N → Set (Real × Real))
    (hgood : ∀ modes, MeasurableSet (good modes))
    (hderivative : ∀ modes point, point ∈ good modes →
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ modes.1 modes.2)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ modes.1 modes.2 point)
        (good modes) point)
    (hinjective : ∀ modes, InjOn
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ modes.1 modes.2) (good modes))
    (detLower : ChildRepeatedModePair N → Real)
    (hdetLower : ∀ modes, 0 < detLower modes)
    (hdet : ∀ modes point, point ∈ good modes →
      detLower modes ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ modes.1 modes.2 point).det|)
    (regularCeiling badCeiling : ENNReal)
    (hregular : actualTwoMassChildRepeatedRegularPerSiteBudget
      weightCeiling detLower ≤ regularCeiling)
    (hbad : actualTwoMassChildRepeatedBadPerSiteBudget
      weight good ≤ badCeiling)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    actualTwoMassChildRepeatedConditionalPerSiteMeasure
        fixed site₁ site₂ weight target ≤
      regularCeiling * (volume : Measure (Real × Real)) target +
        badCeiling := by
  calc
    _ ≤ actualTwoMassChildRepeatedRegularPerSiteBudget
          weightCeiling detLower *
          (volume : Measure (Real × Real)) target +
        actualTwoMassChildRepeatedBadPerSiteBudget weight good :=
      actualTwoMassChildRepeatedConditionalPerSite_apply_le
        fixed site₁ site₂ weight weightCeiling hweight good hgood
        hderivative hinjective detLower hdetLower hdet htarget
    _ ≤ regularCeiling * (volume : Measure (Real × Real)) target +
          badCeiling :=
      add_le_add
        (mul_le_mul_left hregular
          ((volume : Measure (Real × Real)) target)) hbad

/-- Forward `L∞` planar domination for the reduced parent/child law of a
hybrid lift, from a finite-volume arbitrary-set estimate with vanishing
error. -/
theorem childRepeatedScalarClusterHybridLift_reduced_le_volume_of_vanishingError
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ j A, MeasurableSet A →
      (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure ensemble
          (size (lift.subsequence j)) omega).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real)) A ≤
        C * (volume : Measure (Real × Real)) A + error j) :
    ((((lift.markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
      FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
      C • (volume : Measure (Real × Real)) := by
  let source : Nat → FiniteMeasure (Real × Real) := fun j =>
    (canonicalChildRepeatedFrequencyPerSiteFiniteMeasure ensemble
      (size (lift.subsequence j)) omega).map
        childRepeatedFrequencyProjection
  let target : FiniteMeasure (Real × Real) :=
    (lift.markedTarget.map forgetRankFrequencyTriple).map
      childRepeatedFrequencyProjection
  have hfrequency := canonicalChildRepeated_frequencyMarginal_tendsto
    ensemble omega (fun j => size (lift.subsequence j))
      lift.markedTarget lift.markedTendsto
  have hpair : Tendsto source atTop (nhds target) := by
    exact FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (fun j => canonicalChildRepeatedFrequencyPerSiteFiniteMeasure ensemble
        (size (lift.subsequence j)) omega)
      (lift.markedTarget.map forgetRankFrequencyTriple)
      hfrequency continuous_childRepeatedFrequencyProjection
  exact finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
    source target hpair (volume : Measure (Real × Real))
      C hC error herror (by
        intro j A hA
        exact hbound j A hA)

/-- The preceding quantitative result implies forward planar absolute
continuity of the reduced cluster law. -/
theorem childRepeatedScalarClusterHybridLift_reduced_absolutelyContinuous_volume_of_vanishingError
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ j A, MeasurableSet A →
      (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure ensemble
          (size (lift.subsequence j)) omega).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real)) A ≤
        C * (volume : Measure (Real × Real)) A + error j) :
    ((((lift.markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
      FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≪
      (volume : Measure (Real × Real)) := by
  exact
    (childRepeatedScalarClusterHybridLift_reduced_le_volume_of_vanishingError
      lift C hC error herror hbound).absolutelyContinuous.trans
        Measure.smul_absolutelyContinuous

end

end ArchonPhysics.ActualTwoMassChildRepeatedPerSiteLInfinity

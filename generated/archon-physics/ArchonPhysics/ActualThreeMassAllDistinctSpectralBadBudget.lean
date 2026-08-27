import ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
import ArchonPhysics.CouplingWeightedJacobianSpectralBudget
import ArchonPhysics.NormalizedResonanceBadRegionDecay

/-!
# Volume-uniform spectral budget for the actual all-distinct bad sector

The compact-atlas good part and the sinc-squared bad part have different
volume-scaling mechanisms.  Local inverse charts do not share a common mass
preimage across different mode triples, so projector orthogonality does not
by itself control their reciprocal-Jacobian atlas cost.  The bad source mass,
however, is summed at one and the same resampled mass configuration.  The
exact spectral factorization can therefore be applied before iid integration.

This file proves that the genuine all-distinct collision-weighted source has
an `N`-uniform per-site mass.  If every complementary chart sector has a
common positive mismatch gap, its exact sinc-squared-weighted bad budget is
then `O(1 / (T * eta^2))`, again uniformly in `N`.  No tuple-cardinality or
atlas-cardinality factor is used in this bad-sector estimate.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctSpectralBadBudget

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.CouplingWeightedJacobianSpectralBudget
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.LocalCollisionDensityTransfer
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonanceBadRegionDecay
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The explicit Parseval ceiling for the actual positive cubic collision
weight after the canonical inverse-volume normalization. -/
def actualThreeMassSpectralPerSiteWeightCeiling : ENNReal :=
  ENNReal.ofReal ((Real.sqrt 5 / 2) ^ 3)

/-- Pointwise in the three resampled masses, projector orthogonality removes
the apparent `N^2` loss from summing the genuine all-distinct weights. -/
theorem actualThreeMassAllDistinctTupleWeight_sum_div_volume_le_spectral
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple) :
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes triple ≤
      actualThreeMassSpectralPerSiteWeightCeiling := by
  classical
  let mass := threeMassSiteConfig fixed site₀ site₁ site₂ triple
  let spectralSum := positiveCouplingWeightedTupleSum mass (fun _ => 1)
  have hsumNonneg : 0 ≤ spectralSum := by
    unfold spectralSum positiveCouplingWeightedTupleSum
    apply Finset.sum_nonneg
    intro modes _hmodes
    split_ifs
    · exact mul_nonneg
        (harmonicOrderedNormalizedInteractionWeight_nonneg mass modes)
        (by norm_num)
    · norm_num
  have hspectral : spectralSum / (N : Real) ≤
      (Real.sqrt 5 / 2) ^ 3 := by
    have hbase :=
      positiveCouplingWeightedTupleSum_div_volume_le_of_envelope_ceiling
        mass (fun _ => 1) (fun _ _ => 1)
        (by intro modes hpositive; simp)
        (fun _ => 1) (by simp) (by simp)
        (Real.sqrt 5) (Real.sqrt_nonneg 5)
        (by
          intro mode
          exact actualThreeMass_orderedModeFrequency_le_sqrt_five
            fixed hfixed site₀ site₁ site₂ triple mode)
    simpa [spectralSum, pow_succ] using hbase
  have hweightSum :
      (∑ modes : OrderedModeTriple N,
          actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes triple) ≤
        ENNReal.ofReal spectralSum := by
    calc
      (∑ modes : OrderedModeTriple N,
          actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes triple) ≤
          ∑ modes : OrderedModeTriple N,
            ENNReal.ofReal
              (if IsPositiveOrderedTriple mass modes then
                harmonicOrderedNormalizedInteractionWeight mass modes * 1
              else 0) := by
        apply Finset.sum_le_sum
        intro modes _hmodes
        unfold actualThreeMassAllDistinctTupleWeight
          actualThreeMassPositiveTupleWeight
        by_cases hdistinct : AllDistinctModes modes
        · simp only [if_pos hdistinct]
          by_cases hpositive : IsPositiveOrderedTriple mass modes
          · simp [mass, hpositive]
          · simp [mass, hpositive]
        · simp [hdistinct]
      _ = ENNReal.ofReal spectralSum := by
        unfold spectralSum positiveCouplingWeightedTupleSum
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro modes _hmodes
        split_ifs
        · exact mul_nonneg
            (harmonicOrderedNormalizedInteractionWeight_nonneg mass modes)
            (by norm_num)
        · norm_num
  have hNpos : (0 : Real) < N := by
    exact_mod_cast NeZero.pos N
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes triple ≤
      (N : ENNReal)⁻¹ * ENNReal.ofReal spectralSum :=
        mul_le_mul_right hweightSum _
    _ = ENNReal.ofReal (spectralSum / (N : Real)) := by
      rw [ENNReal.ofReal_div_of_pos hNpos, ENNReal.ofReal_natCast]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ ENNReal.ofReal ((Real.sqrt 5 / 2) ^ 3) :=
      ENNReal.ofReal_le_ofReal hspectral
    _ = actualThreeMassSpectralPerSiteWeightCeiling := rfl

/-- After iid integration of the selected masses, the full genuine
all-distinct source still has the same volume-independent per-site ceiling. -/
theorem actualThreeMassAllDistinct_sourceMass_div_volume_le_spectral
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N) :
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes)) univ ≤
      actualThreeMassSpectralPerSiteWeightCeiling := by
  classical
  let _ : IsProbabilityMeasure iidMassPairLaw := by
    unfold iidMassPairLaw
    infer_instance
  let _ : IsProbabilityMeasure iidMassTripleLaw := by
    unfold iidMassTripleLaw
    infer_instance
  have hmeasurable (modes : OrderedModeTriple N) : Measurable
      (actualThreeMassAllDistinctTupleWeight
        fixed site₀ site₁ site₂ modes) :=
    measurable_actualThreeMassAllDistinctTupleWeight
      fixed site₀ site₁ site₂ modes
  have hsumMeasurable : Measurable fun triple =>
      ∑ modes : OrderedModeTriple N,
        actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂ modes triple := by
    fun_prop
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes)) univ =
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          ∫⁻ triple,
            actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes triple
            ∂iidMassTripleLaw := by
        congr 1
        apply Finset.sum_congr rfl
        intro modes _hmodes
        rw [withDensity_apply _ MeasurableSet.univ,
          Measure.restrict_univ]
    _ = (N : ENNReal)⁻¹ *
        ∫⁻ triple,
          ∑ modes : OrderedModeTriple N,
            actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes triple
          ∂iidMassTripleLaw := by
        rw [lintegral_finsetSum Finset.univ]
        intro modes _hmodes
        exact hmeasurable modes
    _ = ∫⁻ triple,
          (N : ENNReal)⁻¹ *
            ∑ modes : OrderedModeTriple N,
              actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes triple
          ∂iidMassTripleLaw := by
        rw [lintegral_const_mul _ hsumMeasurable]
    _ ≤ ∫⁻ _triple,
          actualThreeMassSpectralPerSiteWeightCeiling
          ∂iidMassTripleLaw := by
        apply lintegral_mono
        intro triple
        exact
          actualThreeMassAllDistinctTupleWeight_sum_div_volume_le_spectral
            fixed hfixed site₀ site₁ site₂ triple
    _ = actualThreeMassSpectralPerSiteWeightCeiling := by simp

/-- A common mismatch gap on every exact complementary chart sector turns
the sinc-squared bad contribution into an explicit `N`-uniform `O(T⁻¹)`
budget.  The hypothesis is source-side and concerns the genuine actual
frequency chart; no realization-wise density statement is made. -/
theorem actualThreeMassAllDistinctWeightedBadPerSiteBudget_le_offGap_spectral
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (good : OrderedModeTriple N → Set MassTriple)
    (hgood : ∀ modes, MeasurableSet (good modes))
    {eta T : Real} (heta : 0 < eta) (hT : 0 < T)
    (hgap : ∀ modes point, point ∈ (good modes)ᶜ →
      eta ≤ |(actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes point).2|) :
    actualThreeMassWeightedBadPerSiteBudget
        fixed site₀ site₁ site₂ sign
        (actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂)
        good T ≤
      ENNReal.ofReal (offGapCoefficient eta T) *
        actualThreeMassSpectralPerSiteWeightCeiling := by
  classical
  let coefficient : ENNReal := ENNReal.ofReal (offGapCoefficient eta T)
  let source : OrderedModeTriple N → Measure MassTriple := fun modes =>
    iidMassTripleLaw.withDensity
      (actualThreeMassAllDistinctTupleWeight
        fixed site₀ site₁ site₂ modes)
  let chart : OrderedModeTriple N → MassTriple → MassTriple := fun modes =>
    actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes
  have hchart (modes : OrderedModeTriple N) : Measurable (chart modes) :=
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  have hlocal (modes : OrderedModeTriple N) :
      (Measure.map (chart modes)
          ((source modes).restrict (good modes)ᶜ)).withDensity
            (liftedResonanceKernelDensity T) univ ≤
        coefficient * (source modes) univ := by
    have hgapAE : ∀ᵐ value ∂Measure.map (chart modes)
        ((source modes).restrict (good modes)ᶜ), eta ≤ |value.2| := by
      apply (ae_map_iff
        (p := fun value : MassTriple => eta ≤ |value.2|)
        (hchart modes).aemeasurable
        (measurableSet_le measurable_const measurable_snd.abs)).2
      exact ae_restrict_of_forall_mem (hgood modes).compl
        (fun point hpoint => hgap modes point hpoint)
    calc
      (Measure.map (chart modes)
          ((source modes).restrict (good modes)ᶜ)).withDensity
            (liftedResonanceKernelDensity T) univ ≤
        coefficient *
          Measure.map (chart modes)
            ((source modes).restrict (good modes)ᶜ) univ :=
        liftedResonanceKernelDensity_weightedBad_le_offGap
          (Measure.map (chart modes)
            ((source modes).restrict (good modes)ᶜ)) heta hT hgapAE
      _ ≤ coefficient * (source modes) univ := by
        apply mul_le_mul_right
        rw [Measure.map_apply (hchart modes) MeasurableSet.univ]
        simp only [preimage_univ]
        exact Measure.restrict_le_self univ
  unfold actualThreeMassWeightedBadPerSiteBudget
  change (N : ENNReal)⁻¹ *
      ∑ modes : OrderedModeTriple N,
        (Measure.map (chart modes)
          ((source modes).restrict (good modes)ᶜ)).withDensity
            (liftedResonanceKernelDensity T) univ ≤
      coefficient * actualThreeMassSpectralPerSiteWeightCeiling
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          (Measure.map (chart modes)
            ((source modes).restrict (good modes)ᶜ)).withDensity
              (liftedResonanceKernelDensity T) univ ≤
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          coefficient * (source modes) univ := by
        exact mul_le_mul_right
          (Finset.sum_le_sum fun modes _hmodes => hlocal modes) _
    _ = coefficient *
        ((N : ENNReal)⁻¹ *
          ∑ modes : OrderedModeTriple N, (source modes) univ) := by
        rw [← Finset.mul_sum]
        ac_rfl
    _ ≤ coefficient * actualThreeMassSpectralPerSiteWeightCeiling :=
      mul_le_mul_right
        (actualThreeMassAllDistinct_sourceMass_div_volume_le_spectral
          fixed hfixed site₀ site₁ site₂) _

end

end ArchonPhysics.ActualThreeMassAllDistinctSpectralBadBudget

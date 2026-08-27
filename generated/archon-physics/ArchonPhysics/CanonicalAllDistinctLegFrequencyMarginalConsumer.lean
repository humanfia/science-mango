import ArchonPhysics.ActualThreeMassAllDistinctLegMismatchDomination
import ArchonPhysics.CanonicalAllDistinctRawLiftedLawIdentification

/-!
# Canonical all-distinct leg-frequency marginal consumer

This file connects the genuine actual three-mass good coarea estimate to the
canonical all-distinct raw sector and then applies the normalized resonance
kernel.  For each of the three decay legs, the broadened frequency marginal
has the `N`-uniform good density constant `C * sqrt 5`; the exact pre-existing
kernel-weighted bad mass is retained additively.

No raw density is asserted for the bad law.  The final off-gap theorem uses
the existing spectral bad budget and therefore has no tuple-cardinality loss.
-/

open scoped ENNReal

namespace ArchonPhysics.CanonicalAllDistinctLegFrequencyMarginalConsumer

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
open ArchonPhysics.ActualThreeMassAllDistinctLegMismatchDomination
open ArchonPhysics.ActualThreeMassAllDistinctSpectralBadBudget
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.CanonicalAllDistinctRawLiftedLawIdentification
open ArchonPhysics.CanonicalOnShellChildPairUniformIntegrability
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FrequencyMismatchKernelMarginalDomination
open ArchonPhysics.LocalCollisionDensityTransfer
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.NormalizedResonanceBadRegionDecay
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformCollisionDensityTransfer
open MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Exact canonical raw-law projection adapters -/

/-- Recovering a decay-leg frequency from the lifted child--mismatch chart
returns the corresponding coordinate of the original frequency triple. -/
theorem decayLiftedLegFrequency_plainChildMismatchCoordinates
    (leg : Fin 3) (frequency : Fin 3 → Real) :
    decayLiftedLegFrequency leg
        (plainChildMismatchCoordinates decayInteractionSign frequency) =
      frequency leg := by
  fin_cases leg
  all_goals simp [decayLiftedLegFrequency, plainChildMismatchCoordinates,
    frequencyTripleMismatch, decayInteractionSign, Fin.sum_univ_three]
  all_goals ring

/-- Pushing the canonical all-distinct raw lifted law to
`(omega_leg, mismatch)` is exactly the direct pushforward of the underlying
frequency-triple sector. -/
theorem map_legFrequencyMismatch_allDistinctPerSiteRawLiftedMeasure_eq
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (leg : Fin 3) :
    Measure.map
        (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd)
        (allDistinctPerSiteRawLiftedMeasure mass decayInteractionSign) =
      Measure.map
        (frequencyMismatchCoordinates (fun frequency : Fin 3 → Real =>
            frequency leg) (frequencyTripleMismatch decayInteractionSign))
        (perSitePositiveWeightedFrequencyTripleMeasureWhere
          mass AllDistinctModes) := by
  unfold allDistinctPerSiteRawLiftedMeasure
  rw [Measure.map_map
    (measurable_frequencyMismatchCoordinates
      (measurable_decayLiftedLegFrequency leg) measurable_snd)
    (measurable_plainChildMismatchCoordinates decayInteractionSign)]
  congr 1
  funext frequency
  apply Prod.ext
  · exact decayLiftedLegFrequency_plainChildMismatchCoordinates leg frequency
  · rfl

/-- Exact two-dimensional raw-law identification after conditioning on the
three selected iid masses. -/
theorem actualThreeMassAllDistinctJoint_map_legFrequencyMismatch_apply_eq_lintegral_raw
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (leg : Fin 3)
    {A : Set (Real × Real)} (hA : MeasurableSet A) :
    Measure.map
        (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd)
        (actualThreeMassAllDistinctJointLiftedMeasure
          fixed site₀ site₁ site₂ decayInteractionSign) A =
      ∫⁻ triple,
        allDistinctPerSiteRawLiftedMeasure
          (threeMassSiteConfig fixed site₀ site₁ site₂ triple)
          decayInteractionSign
          (frequencyMismatchCoordinates
              (decayLiftedLegFrequency leg) Prod.snd ⁻¹' A)
        ∂iidMassTripleLaw := by
  rw [Measure.map_apply
    (measurable_frequencyMismatchCoordinates
      (measurable_decayLiftedLegFrequency leg) measurable_snd) hA]
  exact actualThreeMassAllDistinctJointLiftedMeasure_apply_eq_lintegral_raw
    fixed site₀ site₁ site₂ decayInteractionSign
    (hA.preimage (measurable_frequencyMismatchCoordinates
      (measurable_decayLiftedLegFrequency leg) measurable_snd))

/-- Combined exact adapter: the actual projected law is the selected-mass
conditional average of the direct canonical `(omega_leg, mismatch)` raw law,
with no intermediate lifted coordinates remaining on the right-hand side. -/
theorem actualThreeMassAllDistinctJoint_map_legFrequencyMismatch_apply_eq_lintegral_canonical
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (leg : Fin 3)
    {A : Set (Real × Real)} (hA : MeasurableSet A) :
    Measure.map
        (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd)
        (actualThreeMassAllDistinctJointLiftedMeasure
          fixed site₀ site₁ site₂ decayInteractionSign) A =
      ∫⁻ triple,
        Measure.map
          (frequencyMismatchCoordinates (fun frequency : Fin 3 → Real =>
              frequency leg) (frequencyTripleMismatch decayInteractionSign))
          (perSitePositiveWeightedFrequencyTripleMeasureWhere
            (threeMassSiteConfig fixed site₀ site₁ site₂ triple)
            AllDistinctModes) A
        ∂iidMassTripleLaw := by
  rw [actualThreeMassAllDistinctJoint_map_legFrequencyMismatch_apply_eq_lintegral_raw
    fixed site₀ site₁ site₂ leg hA]
  apply lintegral_congr
  intro triple
  calc
    allDistinctPerSiteRawLiftedMeasure
          (threeMassSiteConfig fixed site₀ site₁ site₂ triple)
          decayInteractionSign
          (frequencyMismatchCoordinates
              (decayLiftedLegFrequency leg) Prod.snd ⁻¹' A) =
        Measure.map
          (frequencyMismatchCoordinates
            (decayLiftedLegFrequency leg) Prod.snd)
          (allDistinctPerSiteRawLiftedMeasure
            (threeMassSiteConfig fixed site₀ site₁ site₂ triple)
            decayInteractionSign) A := by
      rw [Measure.map_apply
        (measurable_frequencyMismatchCoordinates
          (measurable_decayLiftedLegFrequency leg) measurable_snd) hA]
    _ = Measure.map
          (frequencyMismatchCoordinates (fun frequency : Fin 3 → Real =>
              frequency leg) (frequencyTripleMismatch decayInteractionSign))
          (perSitePositiveWeightedFrequencyTripleMeasureWhere
            (threeMassSiteConfig fixed site₀ site₁ site₂ triple)
            AllDistinctModes) A := by
      rw [map_legFrequencyMismatch_allDistinctPerSiteRawLiftedMeasure_eq]

/-! ## Broadening and one-dimensional frequency projection -/

/-- Measure-level version of the normalized resonance-kernel consumer.  It
does not require packaging the raw measure as a `FiniteMeasure`; the proof
uses only the supplied joint domination. -/
theorem map_decayLiftedLegFrequency_withDensity_le_of_jointDomination
    (measure : Measure MassTriple) (leg : Fin 3)
    {T : Real} (hT : 0 < T) (D : ENNReal)
    (hjoint :
      Measure.map
          (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd)
          measure ≤
        D • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (decayLiftedLegFrequency leg)
        (measure.withDensity (liftedResonanceKernelDensity T)) ≤
      D • (volume : Measure Real) := by
  let coordinates :=
    frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd
  let kernelDensity : Real × Real → ENNReal := fun value =>
    ENNReal.ofReal (normalizedFiniteTimeResonanceKernel value.2 T)
  have hcoordinates : Measurable coordinates :=
    measurable_frequencyMismatchCoordinates
      (measurable_decayLiftedLegFrequency leg) measurable_snd
  have hkernelDensity : Measurable kernelDensity := by
    exact ENNReal.measurable_ofReal.comp
      ((continuous_normalizedFiniteTimeResonanceKernel hT).measurable.comp
        measurable_snd)
  have hbroadLift :
      Measure.map coordinates
          (measure.withDensity (liftedResonanceKernelDensity T)) =
        (Measure.map coordinates measure).withDensity kernelDensity := by
    have hmap := map_withDensity_comp
      measure coordinates hcoordinates kernelDensity hkernelDensity
    apply hmap.trans
    congr 2
  calc
    Measure.map (decayLiftedLegFrequency leg)
        (measure.withDensity (liftedResonanceKernelDensity T)) =
        Measure.map Prod.fst
          (Measure.map coordinates
            (measure.withDensity (liftedResonanceKernelDensity T))) := by
      rw [Measure.map_map measurable_fst hcoordinates]
      rfl
    _ = Measure.map Prod.fst
        ((Measure.map coordinates measure).withDensity kernelDensity) := by
      rw [hbroadLift]
    _ ≤ Measure.map Prod.fst
        ((D • ((volume : Measure Real).prod
          (volume : Measure Real))).withDensity kernelDensity) :=
      Measure.map_mono
        (withDensity_mono_measure hjoint kernelDensity) measurable_fst
    _ = D • (volume : Measure Real) := by
      rw [withDensity_smul_measure, Measure.map_smul]
      change D • Measure.map Prod.fst
          (((volume : Measure Real).prod
            (volume : Measure Real)).withDensity (fun value =>
              ENNReal.ofReal
                (normalizedFiniteTimeResonanceKernel value.2 T))) = _
      have hkernelMeasurable : Measurable (fun mismatch : Real =>
          ENNReal.ofReal (normalizedFiniteTimeResonanceKernel mismatch T)) :=
        ENNReal.measurable_ofReal.comp
          (continuous_normalizedFiniteTimeResonanceKernel hT).measurable
      have hprod :
          (((volume : Measure Real).prod
            (volume : Measure Real)).withDensity (fun value =>
              ENNReal.ofReal
                (normalizedFiniteTimeResonanceKernel value.2 T))) =
            (volume : Measure Real).prod
              ((volume : Measure Real).withDensity (fun mismatch =>
                ENNReal.ofReal
                  (normalizedFiniteTimeResonanceKernel mismatch T))) := by
        simpa only [Function.comp_apply] using
          (prod_withDensity_right hkernelMeasurable).symm
      rw [hprod]
      change D • Measure.map Prod.fst
          ((volume : Measure Real).prod
            (normalizedFiniteTimeResonanceKernelFiniteMeasure T hT :
              Measure Real)) = _
      rw [Measure.map_fst_prod,
        normalizedFiniteTimeResonanceKernelFiniteMeasure_univ, one_smul]

/-- The complete actual all-distinct broadened one-leg marginal is bounded by
the uniform good density plus the exact kernel-weighted bad budget. -/
theorem actualThreeMassAllDistinctJoint_broadenedLeg_apply_le_of_jointCoarea
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (good : OrderedModeTriple N → Set MassTriple)
    (hgood : ∀ modes, MeasurableSet (good modes))
    (C : ENNReal)
    (hcoarea : actualThreeMassAllDistinctJointGoodCoareaBound
      fixed site₀ site₁ site₂ decayInteractionSign good C)
    {T : Real} (hT : 0 < T) (leg : Fin 3)
    {target : Set Real} (htarget : MeasurableSet target) :
    Measure.map (decayLiftedLegFrequency leg)
        ((actualThreeMassAllDistinctJointLiftedMeasure
          fixed site₀ site₁ site₂ decayInteractionSign).withDensity
            (liftedResonanceKernelDensity T)) target ≤
      (C * ENNReal.ofReal (Real.sqrt 5)) *
          (volume : Measure Real) target +
        actualThreeMassWeightedBadPerSiteBudget
          fixed site₀ site₁ site₂ decayInteractionSign
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂) good T := by
  let goodLifted := actualThreeMassAllDistinctJointGoodLiftedMeasure
    fixed site₀ site₁ site₂ decayInteractionSign good
  let badLifted := actualThreeMassAllDistinctJointBadLiftedMeasure
    fixed site₀ site₁ site₂ decayInteractionSign good
  have hgoodBound :
      Measure.map (decayLiftedLegFrequency leg)
          (goodLifted.withDensity (liftedResonanceKernelDensity T)) ≤
        (C * ENNReal.ofReal (Real.sqrt 5)) •
          (volume : Measure Real) :=
    map_decayLiftedLegFrequency_withDensity_le_of_jointDomination
      goodLifted leg hT (C * ENNReal.ofReal (Real.sqrt 5))
      (actualThreeMassAllDistinctJointGood_map_legFrequencyMismatch_le_volume
        fixed hfixed site₀ site₁ site₂ good C hcoarea leg)
  have hgoodTarget :
      Measure.map (decayLiftedLegFrequency leg)
          (goodLifted.withDensity (liftedResonanceKernelDensity T)) target ≤
        (C * ENNReal.ofReal (Real.sqrt 5)) *
          (volume : Measure Real) target := by
    simpa only [Measure.smul_apply, smul_eq_mul] using
      (Measure.le_iff.mp hgoodBound) target htarget
  have hbadTarget :
      Measure.map (decayLiftedLegFrequency leg)
          (badLifted.withDensity (liftedResonanceKernelDensity T)) target ≤
        badLifted.withDensity (liftedResonanceKernelDensity T) univ := by
    rw [Measure.map_apply (measurable_decayLiftedLegFrequency leg) htarget]
    exact measure_mono (subset_univ _)
  rw [actualThreeMassAllDistinctJointLiftedMeasure_eq_good_add_bad
      fixed site₀ site₁ site₂ decayInteractionSign good hgood,
    withDensity_add_measure,
    Measure.map_add _ _ (measurable_decayLiftedLegFrequency leg),
    Measure.add_apply]
  calc
    Measure.map (decayLiftedLegFrequency leg)
          (goodLifted.withDensity (liftedResonanceKernelDensity T)) target +
        Measure.map (decayLiftedLegFrequency leg)
          (badLifted.withDensity (liftedResonanceKernelDensity T)) target ≤
      (C * ENNReal.ofReal (Real.sqrt 5)) *
          (volume : Measure Real) target +
        badLifted.withDensity (liftedResonanceKernelDensity T) univ :=
      add_le_add hgoodTarget hbadTarget
    _ = (C * ENNReal.ofReal (Real.sqrt 5)) *
          (volume : Measure Real) target +
        actualThreeMassWeightedBadPerSiteBudget
          fixed site₀ site₁ site₂ decayInteractionSign
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂) good T := by
      rw [actualThreeMassAllDistinctJointBad_withDensity_univ_eq_budget]

/-- With a uniform source-side mismatch gap on the bad charts, the additive
error is the existing explicit `N`-uniform spectral `O(T⁻¹)` budget. -/
theorem actualThreeMassAllDistinctJoint_broadenedLeg_apply_le_of_jointCoarea_offGap
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (good : OrderedModeTriple N → Set MassTriple)
    (hgood : ∀ modes, MeasurableSet (good modes))
    (C : ENNReal)
    (hcoarea : actualThreeMassAllDistinctJointGoodCoareaBound
      fixed site₀ site₁ site₂ decayInteractionSign good C)
    {eta T : Real} (heta : 0 < eta) (hT : 0 < T)
    (hgap : ∀ modes point, point ∈ (good modes)ᶜ →
      eta ≤ |(actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ decayInteractionSign modes point).2|)
    (leg : Fin 3) {target : Set Real} (htarget : MeasurableSet target) :
    Measure.map (decayLiftedLegFrequency leg)
        ((actualThreeMassAllDistinctJointLiftedMeasure
          fixed site₀ site₁ site₂ decayInteractionSign).withDensity
            (liftedResonanceKernelDensity T)) target ≤
      (C * ENNReal.ofReal (Real.sqrt 5)) *
          (volume : Measure Real) target +
        ENNReal.ofReal (offGapCoefficient eta T) *
          actualThreeMassSpectralPerSiteWeightCeiling := by
  calc
    _ ≤ (C * ENNReal.ofReal (Real.sqrt 5)) *
          (volume : Measure Real) target +
        actualThreeMassWeightedBadPerSiteBudget
          fixed site₀ site₁ site₂ decayInteractionSign
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂) good T :=
      actualThreeMassAllDistinctJoint_broadenedLeg_apply_le_of_jointCoarea
        fixed hfixed site₀ site₁ site₂ good hgood C hcoarea hT leg htarget
    _ ≤ (C * ENNReal.ofReal (Real.sqrt 5)) *
          (volume : Measure Real) target +
        ENNReal.ofReal (offGapCoefficient eta T) *
          actualThreeMassSpectralPerSiteWeightCeiling :=
      add_le_add_right
        (actualThreeMassAllDistinctWeightedBadPerSiteBudget_le_offGap_spectral
          fixed hfixed site₀ site₁ site₂ decayInteractionSign good hgood
          heta hT hgap) _

end

end ArchonPhysics.CanonicalAllDistinctLegFrequencyMarginalConsumer

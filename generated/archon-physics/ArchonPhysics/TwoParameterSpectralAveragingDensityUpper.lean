import ArchonPhysics.ActualTwoMassRegularSpectralPatch
import ArchonPhysics.QuantitativeJacobianPushforward
import ArchonPhysics.ThreeParameterSpectralAveragingDensity

/-!
# Quantitative upper spectral averaging for two iid masses

The existing two-mass atlas supplies the reverse null-set direction used by
frequency-balance rigidity.  Child-repeated resonance nullity needs the
opposite, quantitative direction.  Here the iid two-mass law is bounded by
`9` times planar Lebesgue measure and the area formula is applied on a genuine
actual two-frequency regular patch.

The complement of the patch remains explicit.  This is essential: a merely
nonzero Jacobian gives qualitative finite-volume absolute continuity but no
volume-uniform small-ball estimate.
-/

namespace ArchonPhysics.TwoParameterSpectralAveragingDensityUpper

open ArchonPhysics
open ArchonPhysics.ActualTwoMassRegularSpectralPatch
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The product of two canonical mass laws has the explicit planar density
ceiling `9`. -/
theorem iidMassPairLaw_le_nine_smul_volume :
    iidMassPairLaw ≤
      (9 : ENNReal) • (volume : Measure (Real × Real)) := by
  unfold iidMassPairLaw
  have hone := massCoordinateLaw_le_three_smul_volume
  have hprod := Measure.prod_mono hone hone
  have hconstant : (3 : ENNReal) * 3 = 9 := by norm_num
  simpa [Measure.volume_eq_prod, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, hconstant] using hprod

/-- Quantitative good/bad estimate for an arbitrary source dominated by the
iid two-mass law. -/
theorem actualTwoMass_weightedSource_frequencyPair_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (child₁ child₂ : Fin (Fintype.card (Lattice.Site N)))
    (source : Measure (Real × Real)) (sourceCeiling : ENNReal)
    (hsource : source ≤ sourceCeiling • iidMassPairLaw)
    {good : Set (Real × Real)} (hgood : MeasurableSet good)
    (hderivative : ∀ point ∈ good,
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ child₁ child₂)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ child₁ child₂ point) good point)
    (hinjective : InjOn
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ child₁ child₂) good)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ good,
      detLower ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ child₁ child₂ point).det|)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    Measure.map
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ child₁ child₂) source target ≤
      (sourceCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target +
        source goodᶜ := by
  let chart := actualTwoMassChildFrequencyChart
    fixed site₁ site₂ child₁ child₂
  have hchart : Measurable chart :=
    (continuous_actualTwoMassChildFrequencyChart
      fixed site₁ site₂ child₁ child₂).measurable
  have hsourceVolume : source ≤
      (sourceCeiling * 9) • (volume : Measure (Real × Real)) := by
    calc
      source ≤ sourceCeiling • iidMassPairLaw := hsource
      _ ≤ sourceCeiling •
          ((9 : ENNReal) • (volume : Measure (Real × Real))) :=
        smul_mono_right sourceCeiling iidMassPairLaw_le_nine_smul_volume
      _ = (sourceCeiling * 9) •
          (volume : Measure (Real × Real)) := by
        rw [mul_smul]
  have hsourceGood : source.restrict good ≤
      (sourceCeiling * 9) •
        (volume : Measure (Real × Real)).restrict good := by
    calc
      source.restrict good ≤
          ((sourceCeiling * 9) •
            (volume : Measure (Real × Real))).restrict good :=
        Measure.restrict_mono_measure hsourceVolume good
      _ = (sourceCeiling * 9) •
          (volume : Measure (Real × Real)).restrict good := by
        rw [Measure.restrict_smul]
  have hgoodMap : Measure.map chart (source.restrict good) ≤
      (sourceCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) •
        (volume : Measure (Real × Real)) :=
    map_le_smul_volume_of_le_volume_restrict_of_det_lower
      (volume : Measure (Real × Real)) hgood chart hchart
      (fun point => actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ child₁ child₂ point)
      hderivative hinjective hdetLower hdet
      (source.restrict good) (sourceCeiling * 9) hsourceGood
  have hmapSplit : Measure.map chart source =
      Measure.map chart (source.restrict good) +
        Measure.map chart (source.restrict goodᶜ) := by
    rw [← Measure.map_add _ _ hchart,
      source.restrict_add_restrict_compl hgood]
  rw [hmapSplit]
  simp only [Measure.add_apply]
  calc
    Measure.map chart (source.restrict good) target +
        Measure.map chart (source.restrict goodᶜ) target ≤
      (sourceCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target +
        Measure.map chart (source.restrict goodᶜ) target := by
      gcongr
      simpa only [Measure.smul_apply, smul_eq_mul] using hgoodMap target
    _ ≤ (sourceCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target + source goodᶜ := by
      apply add_le_add_right
      rw [Measure.map_apply hchart htarget,
        Measure.restrict_apply (htarget.preimage hchart)]
      exact measure_mono inter_subset_right

/-- Specialization to a bounded measurable collision weight. -/
theorem actualTwoMass_boundedDensity_frequencyPair_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (child₁ child₂ : Fin (Fintype.card (Lattice.Site N)))
    (weight : Real × Real → ENNReal) (weightCeiling : ENNReal)
    (hweight : ∀ᵐ point ∂iidMassPairLaw,
      weight point ≤ weightCeiling)
    {good : Set (Real × Real)} (hgood : MeasurableSet good)
    (hderivative : ∀ point ∈ good,
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ child₁ child₂)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ child₁ child₂ point) good point)
    (hinjective : InjOn
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ child₁ child₂) good)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ good,
      detLower ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ child₁ child₂ point).det|)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    Measure.map
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ child₁ child₂)
        (iidMassPairLaw.withDensity weight) target ≤
      (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target +
        (iidMassPairLaw.withDensity weight) goodᶜ := by
  apply actualTwoMass_weightedSource_frequencyPair_apply_le
    fixed site₁ site₂ child₁ child₂
    (iidMassPairLaw.withDensity weight) weightCeiling
  · calc
      iidMassPairLaw.withDensity weight ≤
          iidMassPairLaw.withDensity (fun _ => weightCeiling) :=
        withDensity_mono hweight
      _ = weightCeiling • iidMassPairLaw :=
        withDensity_const weightCeiling
  · exact hgood
  · exact hderivative
  · exact hinjective
  · exact hdetLower
  · exact hdet
  · exact htarget

end


end ArchonPhysics.TwoParameterSpectralAveragingDensityUpper

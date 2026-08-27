import ArchonPhysics.ChildRepeatedReducedResonanceStripVolume
import ArchonPhysics.TwoParameterSpectralAveragingDensityUpper
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Actual two-mass small-ball bound for child-repeated resonance

This file joins the quantitative upper area formula for an actual two-mass
spectral chart to the planar `O(delta)` bound for the reduced resonance strip
`|omega_parent - 2 * omega_child| <= delta`.

The frozen environment is assumed to lie in the iid mass support.  Hence the
whole frequency chart is supported in `[0, sqrt 5]^2`; no unproved spectral
support assumption remains.  The only explicit error is the source mass on
the complement of the chosen regular Jacobian patch.
-/

namespace ArchonPhysics.ActualTwoMassChildRepeatedResonanceStripBound

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ChildRepeatedReducedResonanceStripVolume
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralAveragingDensityUpper
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The two-mass replacement family retains the frozen iid lower mass bound. -/
theorem massLower_le_twoSiteMassConfig_mass
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₁ site₂ site : Lattice.Site N) (pair : Real × Real) :
    massLower ≤
      (twoSiteMassConfig fixed site₁ site₂ pair).mass site := by
  unfold twoSiteMassConfig
  change massLower ≤
    (if site = site₁ then clippedMass pair.1
      else if site = site₂ then clippedMass pair.2
      else fixed.mass site)
  split_ifs
  · exact (clippedMass_mem_support pair.1).1
  · exact (clippedMass_mem_support pair.2).1
  · exact (hfixed site).1

/-- Every actual two-frequency chart from a frozen iid environment lies in
the common physical square `[0, sqrt 5]^2`. -/
theorem actualTwoMassChildFrequencyChart_mem_frequencySquare
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₁ site₂ : Lattice.Site N)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    (pair : Real × Real) :
    actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child pair ∈
      childRepeatedFrequencySquare (Real.sqrt 5) := by
  let mass := twoSiteMassConfig fixed site₁ site₂ pair
  have hmass : ∀ site, massLower ≤ mass.mass site := by
    intro site
    exact massLower_le_twoSiteMassConfig_mass
      fixed hfixed site₁ site₂ site pair
  have hupper (mode : Fin (Fintype.card (Lattice.Site N))) :
      orderedModeFrequency (harmonicHermitian mass) mode ≤ Real.sqrt 5 := by
    simpa [mass, twoSiteHarmonicHermitian, massLower] using
      orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
        mass massLower massLower_pos hmass mode
  change
    (orderedModeFrequency (harmonicHermitian mass) parent,
      orderedModeFrequency (harmonicHermitian mass) child) ∈
        Icc 0 (Real.sqrt 5) ×ˢ Icc 0 (Real.sqrt 5)
  exact ⟨⟨Real.sqrt_nonneg _, hupper parent⟩,
    ⟨Real.sqrt_nonneg _, hupper child⟩⟩

/-- On a frozen iid environment, evaluating a chart pushforward on the full
resonance strip is the same as evaluating it on the bounded physical part. -/
theorem map_actualTwoMassChildFrequencyChart_resonanceStrip_eq_inter_square
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₁ site₂ : Lattice.Site N)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    (source : Measure (Real × Real)) (delta : Real) :
    Measure.map
        (actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child)
        source (childRepeatedReducedResonanceStrip delta) =
      Measure.map
        (actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child)
        source
        (childRepeatedReducedResonanceStrip delta ∩
          childRepeatedFrequencySquare (Real.sqrt 5)) := by
  let chart :=
    actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child
  have hchart : Measurable chart :=
    (continuous_actualTwoMassChildFrequencyChart
      fixed site₁ site₂ parent child).measurable
  rw [Measure.map_apply hchart
      (childRepeatedReducedResonanceStrip_isClosed delta).measurableSet,
    Measure.map_apply hchart
      ((childRepeatedReducedResonanceStrip_isClosed delta).measurableSet.inter
        (childRepeatedFrequencySquare_isClosed (Real.sqrt 5)).measurableSet)]
  congr 1
  ext pair
  simp only [mem_preimage, mem_inter_iff]
  constructor
  · intro hstrip
    exact ⟨hstrip,
      actualTwoMassChildFrequencyChart_mem_frequencySquare
        fixed hfixed site₁ site₂ parent child pair⟩
  · exact fun h => h.1

/-- Quantitative child-repeated resonance-strip estimate for an arbitrary
source dominated by the iid two-mass law.  This is the finite-volume
coarea-to-small-ball interface: the first term is linear in `delta`, and the
second is precisely the bad-Jacobian mass. -/
theorem actualTwoMass_weightedSource_childRepeatedResonanceStrip_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₁ site₂ : Lattice.Site N)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    (source : Measure (Real × Real)) (sourceCeiling : ENNReal)
    (hsource : source ≤ sourceCeiling • iidMassPairLaw)
    {good : Set (Real × Real)} (hgood : MeasurableSet good)
    (hderivative : ∀ point ∈ good,
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child point) good point)
    (hinjective : InjOn
      (actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child)
      good)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ good,
      detLower ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child point).det|)
    {delta : Real} (hdelta : 0 ≤ delta) :
    Measure.map
        (actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child)
        source (childRepeatedReducedResonanceStrip delta) ≤
      (sourceCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
          ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
        source goodᶜ := by
  let target := childRepeatedReducedResonanceStrip delta ∩
    childRepeatedFrequencySquare (Real.sqrt 5)
  have htarget : MeasurableSet target :=
    (childRepeatedReducedResonanceStrip_isClosed delta).measurableSet.inter
      (childRepeatedFrequencySquare_isClosed (Real.sqrt 5)).measurableSet
  rw [map_actualTwoMassChildFrequencyChart_resonanceStrip_eq_inter_square
    fixed hfixed site₁ site₂ parent child source delta]
  calc
    Measure.map
        (actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child)
        source target ≤
      (sourceCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target + source goodᶜ :=
      actualTwoMass_weightedSource_frequencyPair_apply_le
        fixed site₁ site₂ parent child source sourceCeiling hsource
        hgood hderivative hinjective hdetLower hdet htarget
    _ ≤ (sourceCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
          ENNReal.ofReal (2 * Real.sqrt 5 * delta) + source goodᶜ := by
      gcongr
      exact
        volume_childRepeatedReducedResonanceStrip_inter_frequencySquare_le
          (Real.sqrt_nonneg 5) hdelta

/-- Bounded-density specialization of the actual two-mass resonance-strip
estimate. -/
theorem actualTwoMass_boundedDensity_childRepeatedResonanceStrip_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₁ site₂ : Lattice.Site N)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    (weight : Real × Real → ENNReal) (weightCeiling : ENNReal)
    (hweight : ∀ᵐ point ∂iidMassPairLaw, weight point ≤ weightCeiling)
    {good : Set (Real × Real)} (hgood : MeasurableSet good)
    (hderivative : ∀ point ∈ good,
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child point) good point)
    (hinjective : InjOn
      (actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child)
      good)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ good,
      detLower ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child point).det|)
    {delta : Real} (hdelta : 0 ≤ delta) :
    Measure.map
        (actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child)
        (iidMassPairLaw.withDensity weight)
        (childRepeatedReducedResonanceStrip delta) ≤
      (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
          ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
        (iidMassPairLaw.withDensity weight) goodᶜ := by
  apply actualTwoMass_weightedSource_childRepeatedResonanceStrip_apply_le
    fixed hfixed site₁ site₂ parent child
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
  · exact hdelta

end

end ArchonPhysics.ActualTwoMassChildRepeatedResonanceStripBound

import ArchonPhysics.QuantitativeJacobianPushforward

/-!
# Quantitative good/bad Jacobian decomposition

A spectral chart can have a Jacobian which vanishes on an exceptional set, so
a global `L∞` density estimate need not be true.  This module records the
estimate actually needed for uniform absolute continuity: on a measurable
good set where the determinant is bounded below, the pushforward has an
explicit density bound; the complement contributes only its source mass.
-/

namespace ArchonPhysics.QuantitativeJacobianGoodBadPushforward

open Set MeasureTheory
open scoped ENNReal
open ArchonPhysics.QuantitativeJacobianPushforward
open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- A source split into a regular part and an arbitrary exceptional part is
sent to an explicit Haar-density bound plus the pushed exceptional measure. -/
theorem map_good_add_bad_le_density_smul_add_map_bad
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {good : Set E} (hgood : MeasurableSet good)
    (chart : E → E) (hchart : Measurable chart)
    (derivative : E → E →L[Real] E)
    (hderivative : ∀ point ∈ good,
      HasFDerivWithinAt chart (derivative point) good point)
    (hinjective : InjOn chart good)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ good,
      detLower ≤ |(derivative point).det|)
    (goodSource badSource : Measure E) (sourceDensity : ENNReal)
    (hgoodSource : goodSource ≤ sourceDensity • μ.restrict good) :
    Measure.map chart (goodSource + badSource) ≤
      (sourceDensity * (ENNReal.ofReal detLower)⁻¹) • μ +
        Measure.map chart badSource := by
  have hgoodMap :
      Measure.map chart goodSource ≤
        (sourceDensity * (ENNReal.ofReal detLower)⁻¹) • μ :=
    map_le_smul_volume_of_le_volume_restrict_of_det_lower μ hgood chart hchart
      derivative hderivative hinjective hdetLower hdet goodSource
      sourceDensity hgoodSource
  calc
    Measure.map chart (goodSource + badSource) =
        Measure.map chart goodSource + Measure.map chart badSource := by
      rw [Measure.map_add goodSource badSource hchart]
    _ ≤ (sourceDensity * (ENNReal.ofReal detLower)⁻¹) • μ +
        Measure.map chart badSource := add_le_add_left hgoodMap _

/-- Pointwise version: if the exceptional source has mass at most
`badMass`, every measurable target is bounded by the regular density term
plus `badMass`. -/
theorem map_good_add_bad_apply_le_density_mul_add_badMass
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {good : Set E} (hgood : MeasurableSet good)
    (chart : E → E) (hchart : Measurable chart)
    (derivative : E → E →L[Real] E)
    (hderivative : ∀ point ∈ good,
      HasFDerivWithinAt chart (derivative point) good point)
    (hinjective : InjOn chart good)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ good,
      detLower ≤ |(derivative point).det|)
    (goodSource badSource : Measure E) (sourceDensity badMass : ENNReal)
    (hgoodSource : goodSource ≤ sourceDensity • μ.restrict good)
    (hbadMass : badSource univ ≤ badMass)
    {target : Set E} (htarget : MeasurableSet target) :
    Measure.map chart (goodSource + badSource) target ≤
      (sourceDensity * (ENNReal.ofReal detLower)⁻¹) * μ target + badMass := by
  have hmeasure :=
    map_good_add_bad_le_density_smul_add_map_bad μ hgood chart hchart
      derivative hderivative hinjective hdetLower hdet goodSource badSource
      sourceDensity hgoodSource
  have hmapBad : Measure.map chart badSource target ≤ badMass := by
    rw [Measure.map_apply hchart htarget]
    exact (measure_mono (subset_univ _)).trans hbadMass
  calc
    Measure.map chart (goodSource + badSource) target ≤
        (((sourceDensity * (ENNReal.ofReal detLower)⁻¹) • μ) +
          Measure.map chart badSource) target := hmeasure target
    _ = (sourceDensity * (ENNReal.ofReal detLower)⁻¹) * μ target +
        Measure.map chart badSource target := by
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    _ ≤ (sourceDensity * (ENNReal.ofReal detLower)⁻¹) * μ target + badMass :=
      add_le_add_right hmapBad _

/-- Direct good/bad estimate for one source measure.  A global domination on
`patch` is restricted to `good`; no regularity is requested on `goodᶜ`. -/
theorem map_apply_le_density_mul_add_complMass_of_good_patch
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {patch good : Set E} (hgood : MeasurableSet good)
    (hgoodSubset : good ⊆ patch)
    (chart : E → E) (hchart : Measurable chart)
    (derivative : E → E →L[Real] E)
    (hderivative : ∀ point ∈ good,
      HasFDerivWithinAt chart (derivative point) good point)
    (hinjective : InjOn chart good)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ good,
      detLower ≤ |(derivative point).det|)
    (source : Measure E) (sourceDensity : ENNReal)
    (hsource : source ≤ sourceDensity • μ.restrict patch)
    {target : Set E} (htarget : MeasurableSet target) :
    Measure.map chart source target ≤
      (sourceDensity * (ENNReal.ofReal detLower)⁻¹) * μ target +
        source goodᶜ := by
  have hgoodSource :
      source.restrict good ≤ sourceDensity • μ.restrict good := by
    calc
      source.restrict good ≤
          (sourceDensity • μ.restrict patch).restrict good :=
        Measure.restrict_mono_measure hsource good
      _ = sourceDensity • μ.restrict good := by
        rw [Measure.restrict_smul,
          Measure.restrict_restrict_of_subset hgoodSubset]
  have hbadMass : (source.restrict goodᶜ) univ ≤ source goodᶜ := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  calc
    Measure.map chart source target =
        Measure.map chart
          (source.restrict good + source.restrict goodᶜ) target := by
      rw [source.restrict_add_restrict_compl hgood]
    _ ≤ (sourceDensity * (ENNReal.ofReal detLower)⁻¹) * μ target +
        source goodᶜ :=
      map_good_add_bad_apply_le_density_mul_add_badMass μ hgood chart hchart
        derivative hderivative hinjective hdetLower hdet
        (source.restrict good) (source.restrict goodᶜ) sourceDensity
        (source goodᶜ) hgoodSource hbadMass htarget


omit [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [BorelSpace E] in
/-- If measurable good levels increase and cover the source almost
everywhere, their unweighted exceptional mass tends to zero.  This is the
measure-theoretic half of a good/bad spectral decomposition.  For a peaked
finite-time resonance kernel one still has to control the kernel-weighted
exceptional mass. -/
theorem tendsto_measure_compl_good_zero_of_monotone_of_ae_iUnion
    (source : Measure E) [IsFiniteMeasure source]
    (good : Nat → Set E)
    (hgood : ∀ n, MeasurableSet (good n))
    (hmono : Monotone good)
    (hcover : ∀ᵐ point ∂source, point ∈ ⋃ n, good n) :
    Tendsto (fun n => source (good n)ᶜ) atTop (nhds 0) := by
  have hanti : Antitone (fun n => (good n)ᶜ) := by
    intro n m hnm
    exact compl_subset_compl.mpr (hmono hnm)
  have hinterZero : source (⋂ n, (good n)ᶜ) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hcover] with point hpoint
    intro hinter
    obtain ⟨n, hn⟩ := mem_iUnion.mp hpoint
    exact (mem_iInter.mp hinter n) hn
  have hlimit := tendsto_measure_iInter_atTop
    (μ := source) (s := fun n => (good n)ᶜ)
    (fun n => (hgood n).compl.nullMeasurableSet) hanti
    ⟨0, measure_ne_top source _⟩
  rw [hinterZero] at hlimit
  change Tendsto (fun n => source (good n)ᶜ) atTop (nhds 0) at hlimit
  exact hlimit

end

end ArchonPhysics.QuantitativeJacobianGoodBadPushforward

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Quantitative patch around a nonzero Jacobian point

An invertible strict derivative gives a local inverse-function chart.  If a
chosen derivative field is continuous at the base point and represents the
true derivative throughout a neighbourhood, that chart can be shrunk so its
absolute determinant has a fixed positive lower bound.  This is the local
input required by quantitative area-formula pushforward estimates.
-/

namespace ArchonPhysics.LocalNonzeroJacobianQuantitativePatch

open Filter Set
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [CompleteSpace E] [FiniteDimensional Real E]

/-- A nonzero Jacobian at one regular point yields an open injective patch,
inside any prescribed neighbourhood, with a uniform positive determinant
lower bound and the true within-derivative at every point. -/
theorem exists_open_injective_detLower_patch
    {point : E} {chart : E → E}
    {baseDerivative : E →L[Real] E}
    (hstrict : HasStrictFDerivAt chart baseDerivative point)
    (hinvertible : baseDerivative.IsInvertible)
    (derivativeField : E → E →L[Real] E)
    (hfieldAt : derivativeField point = baseDerivative)
    (hfieldContinuous : ContinuousAt derivativeField point)
    {regularity neighborhood : Set E}
    (hregularity : regularity ∈ nhds point)
    (hneighborhood : neighborhood ∈ nhds point)
    (hderivative : ∀ nearby ∈ regularity,
      HasFDerivAt chart (derivativeField nearby) nearby) :
    ∃ patch : Set E, ∃ detLower : Real,
      IsOpen patch ∧ point ∈ patch ∧
      patch ⊆ regularity ∧ patch ⊆ neighborhood ∧
      0 < detLower ∧ InjOn chart patch ∧
      IsOpen (chart '' patch) ∧
      (∀ nearby ∈ patch,
        HasFDerivWithinAt chart (derivativeField nearby) patch nearby) ∧
      ∀ nearby ∈ patch,
        detLower ≤ |(derivativeField nearby).det| := by
  have hbaseDet : baseDerivative.det ≠ 0 := by
    intro hdet
    have hker : baseDerivative.ker ≠ ⊥ :=
      LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
    exact hker (LinearMap.ker_eq_bot.mpr hinvertible.injective)
  have hpointDetPos : 0 < |(derivativeField point).det| := by
    rw [hfieldAt]
    exact abs_pos.mpr hbaseDet
  let detLower : Real := |(derivativeField point).det| / 2
  have hdetLower : 0 < detLower := by
    dsimp [detLower]
    positivity
  have hdetContinuous : ContinuousAt
      (fun nearby => |(derivativeField nearby).det|) point :=
    continuous_abs.continuousAt.comp
      (ContinuousLinearMap.continuous_det.continuousAt.comp hfieldContinuous)
  have hdetEventually : ∀ᶠ nearby in nhds point,
      detLower < |(derivativeField nearby).det| := by
    have htarget : ∀ᶠ value in nhds |(derivativeField point).det|,
        detLower < value :=
      Ioi_mem_nhds (by dsimp [detLower]; linarith)
    exact hdetContinuous.eventually htarget
  have hcombined :
      {nearby |
        nearby ∈ regularity ∧ nearby ∈ neighborhood ∧
          detLower < |(derivativeField nearby).det|} ∈ nhds point := by
    filter_upwards [hregularity, hneighborhood, hdetEventually] with nearby
      hnearbyRegular hnearbyNeighborhood hnearbyDet
    exact ⟨hnearbyRegular, hnearbyNeighborhood, hnearbyDet⟩
  obtain ⟨regularOpen, hopenSubset, hregularOpen, hpointRegular⟩ :=
    mem_nhds_iff.mp hcombined
  have hker : baseDerivative.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinvertible.injective
  have hrange : baseDerivative.range = ⊤ :=
    LinearMap.range_eq_top.mpr hinvertible.surjective
  let derivativeEquiv : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective baseDerivative hker hrange
  have hderivativeEquiv :
      (derivativeEquiv : E →L[Real] E) = baseDerivative :=
    ContinuousLinearEquiv.coe_ofBijective baseDerivative hker hrange
  have hstrictEquiv :
      HasStrictFDerivAt chart (derivativeEquiv : E →L[Real] E) point := by
    rw [hderivativeEquiv]
    exact hstrict
  let localChart := hstrictEquiv.toOpenPartialHomeomorph chart
  have hpointSource : point ∈ localChart.source :=
    hstrictEquiv.mem_toOpenPartialHomeomorph_source
  let patch : Set E := localChart.source ∩ regularOpen
  have hpatchOpen : IsOpen patch := localChart.open_source.inter hregularOpen
  have hpatchSource : patch ⊆ localChart.source := inter_subset_left
  have hpatchCombined : patch ⊆
      {nearby |
        nearby ∈ regularity ∧ nearby ∈ neighborhood ∧
          detLower < |(derivativeField nearby).det|} := fun _ hnearby =>
    hopenSubset hnearby.2
  refine ⟨patch, detLower, hpatchOpen, ⟨hpointSource, hpointRegular⟩,
    (fun _ hnearby => (hpatchCombined hnearby).1),
    (fun _ hnearby => (hpatchCombined hnearby).2.1), hdetLower,
    localChart.injOn.mono hpatchSource,
    localChart.isOpen_image_of_subset_source hpatchOpen hpatchSource, ?_, ?_⟩
  · intro nearby hnearby
    exact (hderivative nearby (hpatchCombined hnearby).1).hasFDerivWithinAt
  · intro nearby hnearby
    exact (hpatchCombined hnearby).2.2.le

end

end ArchonPhysics.LocalNonzeroJacobianQuantitativePatch

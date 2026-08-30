import ArchonPhysics.ParametricPartialJacobianAugmentedLocalChart

/-!
# A selected-first square chart from an invertible partial Jacobian

The implicit-function construction naturally maps
`parameter × selected` to `observable × parameter`.  For coarea and
Jacobian estimates it is convenient to store both source and target as
`selected × parameter`.  When the observable and selected-coordinate spaces
agree, this module precomposes by the product swap and obtains a genuine
endomorphism with an invertible strict derivative.

This is the coordinate-order bridge needed before applying determinant-based
pushforward bounds to an augmented full-IID spectral chart.
-/

namespace ArchonPhysics.SelectedFirstPartialJacobianChart

open Filter Set
open scoped Topology

noncomputable section

variable {K : Type*} [NontriviallyNormedField K]
variable {Parameter : Type*} [NormedAddCommGroup Parameter]
  [NormedSpace K Parameter] [CompleteSpace Parameter]
variable {Selected : Type*} [NormedAddCommGroup Selected]
  [NormedSpace K Selected] [CompleteSpace Selected]

/-- Reorder an augmented family map so that selected coordinates come first
in both its source and target. -/
def selectedFirstAugmentedMap
    (f : Parameter × Selected → Selected) :
    Selected × Parameter → Selected × Parameter :=
  fun point => (f (point.2, point.1), point.2)

/-- An invertible derivative in the selected variables gives an invertible
strict derivative for the selected-first augmented endomorphism. -/
theorem exists_strictDerivative_isInvertible_selectedFirstAugmentedMap
    {point : Parameter × Selected}
    {f : Parameter × Selected → Selected}
    {derivative : Parameter × Selected →L[K] Selected}
    (hderivative : HasStrictFDerivAt f derivative point)
    (hpartial :
      (derivative ∘L ContinuousLinearMap.inr K Parameter Selected).IsInvertible) :
    ∃ augmentedDerivative :
        (Selected × Parameter) →L[K] (Selected × Parameter),
      HasStrictFDerivAt (selectedFirstAugmentedMap f) augmentedDerivative
          (point.2, point.1) ∧
        augmentedDerivative.IsInvertible := by
  let data := hderivative.implicitFunctionDataOfProdDomain hpartial
  let dataEquiv : (Parameter × Selected) ≃L[K] (Selected × Parameter) :=
    data.leftDeriv.equivProdOfSurjectiveOfIsCompl data.rightDeriv
      data.range_leftDeriv data.range_rightDeriv data.isCompl_ker
  let swapEquiv : (Selected × Parameter) ≃L[K] (Parameter × Selected) :=
    ContinuousLinearEquiv.prodComm K Selected Parameter
  let augmentedEquiv :
      (Selected × Parameter) ≃L[K] (Selected × Parameter) :=
    swapEquiv.trans dataEquiv
  refine ⟨(augmentedEquiv :
      (Selected × Parameter) →L[K] (Selected × Parameter)), ?_, ?_⟩
  · have hswap : HasStrictFDerivAt
        (fun point : Selected × Parameter => (point.2, point.1))
        (swapEquiv : (Selected × Parameter) →L[K]
          (Parameter × Selected)) (point.2, point.1) :=
      (swapEquiv : (Selected × Parameter) →L[K]
        (Parameter × Selected)).hasStrictFDerivAt
    have hcomp := data.hasStrictFDerivAt.comp (point.2, point.1) hswap
    change HasStrictFDerivAt
      (fun point : Selected × Parameter => (f (point.2, point.1), point.2))
      (augmentedEquiv : (Selected × Parameter) →L[K]
        (Selected × Parameter)) (point.2, point.1)
    simpa [selectedFirstAugmentedMap, data, dataEquiv, swapEquiv,
      augmentedEquiv, ImplicitFunctionData.prodFun, Function.comp_def] using hcomp
  · exact ContinuousLinearMap.isInvertible_equiv

/-- Finite-dimensional form: the selected-first augmented derivative has
nonzero determinant at the base point. -/
theorem exists_strictDerivative_det_ne_zero_selectedFirstAugmentedMap
    [FiniteDimensional K Parameter] [FiniteDimensional K Selected]
    {point : Parameter × Selected}
    {f : Parameter × Selected → Selected}
    {derivative : Parameter × Selected →L[K] Selected}
    (hderivative : HasStrictFDerivAt f derivative point)
    (hpartial :
      (derivative ∘L ContinuousLinearMap.inr K Parameter Selected).IsInvertible) :
    ∃ augmentedDerivative :
        (Selected × Parameter) →L[K] (Selected × Parameter),
      HasStrictFDerivAt (selectedFirstAugmentedMap f) augmentedDerivative
          (point.2, point.1) ∧
        augmentedDerivative.det ≠ 0 := by
  obtain ⟨augmentedDerivative, hstrict, hinvertible⟩ :=
    exists_strictDerivative_isInvertible_selectedFirstAugmentedMap
      hderivative hpartial
  refine ⟨augmentedDerivative, hstrict, ?_⟩
  intro hdet
  have hker : augmentedDerivative.ker ≠ ⊥ := by
    exact LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
  exact hker (LinearMap.ker_eq_bot.mpr hinvertible.injective)

/-- The selected-first augmented map is injective on an open patch inside any
prescribed neighbourhood of the reordered base point. -/
theorem exists_open_injective_selectedFirstAugmentedPatch
    {point : Parameter × Selected}
    {f : Parameter × Selected → Selected}
    {derivative : Parameter × Selected →L[K] Selected}
    (hderivative : HasStrictFDerivAt f derivative point)
    (hpartial :
      (derivative ∘L ContinuousLinearMap.inr K Parameter Selected).IsInvertible)
    {neighborhood : Set (Selected × Parameter)}
    (hneighborhood : neighborhood ∈ nhds (point.2, point.1)) :
    ∃ patch : Set (Selected × Parameter),
      IsOpen patch ∧ (point.2, point.1) ∈ patch ∧
      patch ⊆ neighborhood ∧
      InjOn (selectedFirstAugmentedMap f) patch ∧
      IsOpen (selectedFirstAugmentedMap f '' patch) := by
  obtain ⟨augmentedDerivative, hstrict, _hinvertible⟩ :=
    exists_strictDerivative_isInvertible_selectedFirstAugmentedMap
      hderivative hpartial
  have hker : augmentedDerivative.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr _hinvertible.injective
  have hrange : augmentedDerivative.range = ⊤ :=
    LinearMap.range_eq_top.mpr _hinvertible.surjective
  let derivativeEquiv :
      (Selected × Parameter) ≃L[K] (Selected × Parameter) :=
    ContinuousLinearEquiv.ofBijective augmentedDerivative hker hrange
  have hderivativeEquiv :
      (derivativeEquiv : (Selected × Parameter) →L[K]
        (Selected × Parameter)) = augmentedDerivative :=
    ContinuousLinearEquiv.coe_ofBijective augmentedDerivative hker hrange
  have hstrictEquiv : HasStrictFDerivAt
      (selectedFirstAugmentedMap f)
      (derivativeEquiv : (Selected × Parameter) →L[K]
        (Selected × Parameter)) (point.2, point.1) := by
    rw [hderivativeEquiv]
    exact hstrict
  let localChart := hstrictEquiv.toOpenPartialHomeomorph
    (selectedFirstAugmentedMap f)
  have hpointSource : (point.2, point.1) ∈ localChart.source :=
    hstrictEquiv.mem_toOpenPartialHomeomorph_source
  obtain ⟨regularOpen, hregularSubset, hregularOpen, hpointRegular⟩ :=
    mem_nhds_iff.mp hneighborhood
  let patch : Set (Selected × Parameter) :=
    localChart.source ∩ regularOpen
  have hpatchOpen : IsOpen patch := localChart.open_source.inter hregularOpen
  have hpatchSource : patch ⊆ localChart.source := inter_subset_left
  refine ⟨patch, hpatchOpen, ⟨hpointSource, hpointRegular⟩,
    (fun _ hpoint => hregularSubset hpoint.2), ?_, ?_⟩
  · exact localChart.injOn.mono hpatchSource
  · exact localChart.isOpen_image_of_subset_source hpatchOpen hpatchSource

end

end ArchonPhysics.SelectedFirstPartialJacobianChart

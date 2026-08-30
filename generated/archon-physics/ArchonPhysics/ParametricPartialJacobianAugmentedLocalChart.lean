import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-!
# A partial Jacobian gives an augmented local chart

Let `f : E₁ × E₂ → F` be strictly differentiable at `(x, y)`.  If its
partial derivative in the `E₂` direction is invertible, then adjoining the
unchanged parameter `x` gives a square local coordinate map

`(x, y) ↦ (f (x, y), x)`.

This is the block-triangular inverse-function step needed when a spectral
chart is invertible in a selected group of masses while all remaining masses
are retained as environment coordinates.  The theorem below is purely local
calculus: it introduces no probabilistic, spectral, or kinetic hypothesis.
-/

namespace ArchonPhysics.ParametricPartialJacobianAugmentedLocalChart

open Filter Set
open scoped Topology

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [CompleteSpace E₁]
variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [CompleteSpace E₂]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F]

/-- Adjoin the unchanged parameter coordinates to the output of a family of
maps.  The output order agrees with `ImplicitFunctionData.prodFun`. -/
def augmentedMap (f : E₁ × E₂ → F) : E₁ × E₂ → F × E₁ :=
  fun point => (f point, point.1)

/-- The augmented map is locally an open partial homeomorphism. -/
def augmentedOpenPartialHomeomorph
    {point : E₁ × E₂} {f : E₁ × E₂ → F}
    {derivative : E₁ × E₂ →L[𝕜] F}
    (hderivative : HasStrictFDerivAt f derivative point)
    (hpartial :
      (derivative ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible) :
    OpenPartialHomeomorph (E₁ × E₂) (F × E₁) :=
  (hderivative.implicitFunctionDataOfProdDomain hpartial).toOpenPartialHomeomorph

@[simp]
theorem augmentedOpenPartialHomeomorph_coe
    {point : E₁ × E₂} {f : E₁ × E₂ → F}
    {derivative : E₁ × E₂ →L[𝕜] F}
    (hderivative : HasStrictFDerivAt f derivative point)
    (hpartial :
      (derivative ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible) :
    ⇑(augmentedOpenPartialHomeomorph hderivative hpartial) =
      augmentedMap f := by
  rfl

/-- Inside every prescribed neighbourhood of the base point there is an
open patch on which the augmented map is injective and whose image is open.
This form is convenient for intersecting a spectral chart with the interior
of a product probability support. -/
theorem exists_open_injective_augmentedPatch
    {point : E₁ × E₂} {f : E₁ × E₂ → F}
    {derivative : E₁ × E₂ →L[𝕜] F}
    (hderivative : HasStrictFDerivAt f derivative point)
    (hpartial :
      (derivative ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible)
    {neighborhood : Set (E₁ × E₂)}
    (hneighborhood : neighborhood ∈ 𝓝 point) :
    ∃ patch : Set (E₁ × E₂),
      IsOpen patch ∧ point ∈ patch ∧ patch ⊆ neighborhood ∧
      InjOn (augmentedMap f) patch ∧
      IsOpen (augmentedMap f '' patch) := by
  let localChart := augmentedOpenPartialHomeomorph hderivative hpartial
  have hpointSource : point ∈ localChart.source := by
    exact
      (hderivative.implicitFunctionDataOfProdDomain hpartial).pt_mem_toOpenPartialHomeomorph_source
  obtain ⟨regularOpen, hregularSubset, hregularOpen, hpointRegular⟩ :=
    mem_nhds_iff.mp hneighborhood
  let patch : Set (E₁ × E₂) := localChart.source ∩ regularOpen
  have hpatchOpen : IsOpen patch := localChart.open_source.inter hregularOpen
  have hpatchSource : patch ⊆ localChart.source := inter_subset_left
  have hpatchInjective : InjOn (augmentedMap f) patch := by
    rw [← augmentedOpenPartialHomeomorph_coe hderivative hpartial]
    exact localChart.injOn.mono hpatchSource
  have hpatchImageOpen : IsOpen (augmentedMap f '' patch) := by
    rw [← augmentedOpenPartialHomeomorph_coe hderivative hpartial]
    exact localChart.isOpen_image_of_subset_source hpatchOpen hpatchSource
  refine ⟨patch, hpatchOpen, ⟨hpointSource, hpointRegular⟩, ?_,
    hpatchInjective, hpatchImageOpen⟩
  intro x hx
  exact hregularSubset hx.2

end

end ArchonPhysics.ParametricPartialJacobianAugmentedLocalChart

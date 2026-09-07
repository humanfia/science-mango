import Family8Grounding.Family8SelectedParentJohnBoxAffineTransportV16
import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentJohnPlankProductionV18

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnBoxAffineTransportV16
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

theorem normalizedJohnBox_one_side_eq_plankSides
    {H : ConvexBody Space} (J : PositiveJohnFrame H) :
    (normalizedJohnBox J 1).side = plankSides 1 1 := by
  funext i
  fin_cases i <;> rfl

theorem normalizedJohnBox_one_rescale
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (r : NNReal) :
    (normalizedJohnBox J 1).rescale r = normalizedJohnBox J r := by
  simp [normalizedJohnBox, FrameBox.rescale]

theorem affineImage_hasBoxDimensions_unit
    {H : ConvexBody Space} (J : PositiveJohnFrame H) :
    HasBoxDimensions 288 (plankSides 1 1)
      (affineImageConvexBody J.affineEquiv H) := by
  refine ⟨by norm_num, normalizedJohnBox J 1,
    normalizedJohnBox_one_side_eq_plankSides J, ?_, ?_⟩
  · change ((normalizedJohnBox J 1).rescale (288 : NNReal)⁻¹).carrier ⊆
      J.affineEquiv '' (H : Set Space)
    rw [normalizedJohnBox_one_rescale]
    exact (normalizedJohnBox_subset_image_rescaledBox J (288 : NNReal)⁻¹).trans
      (Set.image_mono J.certificate.inner_le)
  · change J.affineEquiv '' (H : Set Space) ⊆
      (normalizedJohnBox J 1).carrier
    have hrescale : J.certificate.box.rescale 1 = J.certificate.box := by
      simp [FrameBox.rescale]
    have hout := image_rescaledBox_subset_normalizedJohnBox J 1
    rw [hrescale] at hout
    exact (Set.image_mono J.certificate.outer_le).trans hout

theorem affineImage_isPlank_unit
    {H : ConvexBody Space} (J : PositiveJohnFrame H) :
    IsPlank 288 1 1 (affineImageConvexBody J.affineEquiv H) := by
  exact ⟨by norm_num, le_rfl, le_rfl, affineImage_hasBoxDimensions_unit J⟩

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Family 6 input built from an actual greedy selected-parent block.  Its
only non-automatic premise is genuine memberwise normalized `IsPlank`
geometry at the two short scales `a,b`. -/
noncomputable def selectedParentGreedyBlockJohnPlankFamily
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (C a b : NNReal)
    (hplank : ∀ p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
      IsPlank C a b
        (selectedParentAffineFamily
          (selectedParentGreedyBlockJohnFrame S hrho P k).affineEquiv S
          (blockAt S.activeCoarseFamily P k).fiber p)) :
    ShadedConvexPlankFamily
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} a b := by
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let H := (blockAt S.activeCoarseFamily P k).body
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := J.affineEquiv
  exact
    { family := selectedParentAffineFamily e S B
      shading := selectedParentAffineShading e S Y B
      comparisonConstant := C
      all_isPlank := hplank
      ambient := affineImageConvexBody e H
      ambientComparisonConstant := 288
      ambient_is_unit_scale := affineImage_isPlank_unit J
      contained_in_ambient := by
        intro p
        change e '' (S.activeCoarseFamily p.1 : Set Space) ⊆
          e '' (H : Set Space)
        exact Set.image_mono
          ((blockAt S.activeCoarseFamily P k).contained p.1 p.2) }

theorem selectedParentGreedyBlockJohnPlankFamily_averageMultiplicity
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (C a b : NNReal)
    (hplank : ∀ p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
      IsPlank C a b
        (selectedParentAffineFamily
          (selectedParentGreedyBlockJohnFrame S hrho P k).affineEquiv S
          (blockAt S.activeCoarseFamily P k).fiber p)) :
    (selectedParentGreedyBlockJohnPlankFamily S Y hrho P k C a b
      hplank).shading.averageMultiplicity =
        (selectedParentActualShading S Y
          (blockAt S.activeCoarseFamily P k).fiber).averageMultiplicity :=
  selectedParentAffineShading_averageMultiplicity _ _ _ _

#print axioms normalizedJohnBox_one_rescale
#print axioms affineImage_hasBoxDimensions_unit
#print axioms affineImage_isPlank_unit
#print axioms selectedParentGreedyBlockJohnPlankFamily
#print axioms selectedParentGreedyBlockJohnPlankFamily_averageMultiplicity

end
end Family8SelectedParentJohnPlankProductionV18

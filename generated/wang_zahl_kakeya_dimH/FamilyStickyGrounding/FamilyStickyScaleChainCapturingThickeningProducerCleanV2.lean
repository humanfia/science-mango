import FamilyStickyGrounding.FamilyStickyCapturedTubeBoxWidthCleanV2
import FamilyStickyGrounding.FamilyStickyScaleChainNestedMassLocalizationV1

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainCapturingThickeningProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyAdjacentTestBodyGeometryV1
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Actual producer for captured-test-body thickening control

Nonempty contained indices provide a literal active fine tube inside the
test body.  The captured-tube box theorem then supplies the exact
`CapturingThickeningVolumeControl`; no volume comparison is passed in.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A captured member of the actual active fine family is a literal tube
whose carrier lies in the test body. -/
theorem exists_fineTube_subset_of_containedIndices_nonempty
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (hcaptured : (containedIndices (activeFineFamily S) K).Nonempty) :
    ∃ i : {i // i ∈ S.activeFine},
      (fine.tubes i.1).carrier ⊆ (K : Set Space) := by
  obtain ⟨i, hi⟩ := hcaptured
  refine ⟨i, ?_⟩
  have hiBody := (mem_containedIndices (activeFineFamily S) K i).mp hi
  simpa [activeFineFamily, UniformTubeFamily.bodyFamily, Tube.coe_body] using hiBody

/-- The actual tube captured by a nonempty test body automatically produces
the required closed-thickening volume control with the explicit John-box
loss `capturedTubeBoxLoss delta rho`. -/
theorem actualCapturingThickeningVolumeControl
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta) :
    CapturingThickeningVolumeControl S (capturedTubeBoxLoss delta rho) := by
  constructor
  intro K hcaptured
  obtain ⟨i, hiK⟩ :=
    exists_fineTube_subset_of_containedIndices_nonempty S K hcaptured
  have hgrowth :=
    volume_four_rho_closedThickening_le_capturedTubeBoxLoss
      hdelta (fine.tubes i.1) hiK (rho := rho)
  simpa [closedThickeningBody, NNReal.coe_mul] using hgrowth

#print axioms exists_fineTube_subset_of_containedIndices_nonempty
#print axioms actualCapturingThickeningVolumeControl

end StickyScaleCover

end
end FamilyStickyScaleChainCapturingThickeningProducerV1

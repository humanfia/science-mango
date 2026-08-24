import FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
import FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32ProjectedTubeVerticalCarrierStripV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1

noncomputable section

/-!
# Actual projected vertical carriers are literal PYZ graph strips

The two APIs use the same `(vertical, parameter)` coordinate order.  This
module records their exact set identity, with no dilation or hidden
containment loss.
-/

theorem projectedTubeVerticalCarrier_Icc_eq_pyzCarrierGraphStrip
    {delta : NNReal} (f : Real → Real) (a b R : Real)
    (T : Tube delta) :
    projectedTubeVerticalCarrier f (Icc a b) R T =
      pyzCarrierGraphStrip a b (projectedTubeCinematicTrace f T) R := by
  ext q
  simp only [projectedTubeVerticalCarrier, pyzCarrierGraphStrip,
    Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rcases abs_le.mp h.2 with ⟨hlow, hupp⟩
    constructor <;> linarith
  · intro h
    refine ⟨h.1, ?_⟩
    apply abs_le.mpr
    rcases h.2 with ⟨hlow, hupp⟩
    constructor <;> linarith

#print axioms projectedTubeVerticalCarrier_Icc_eq_pyzCarrierGraphStrip

end
end FamilyStickyCinematicL32ProjectedTubeVerticalCarrierStripV1

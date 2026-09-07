import Family8Grounding.Family8Family7CoordinateToVerticalTubeTransportV1
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import Mathlib.Tactic

/-!
# Exact ambient volume for a coordinate-transported tube body, V2

V1 is frozen after direct validation exposed the affine-equivalence versus
rigid-motion image coercion.  This ADD-only successor changes the image goal
to the rigid-motion form before applying exact volume invariance.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7CoordinateTubeAmbientVolumeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family6AffineConvexVolumeCoreV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8GeneralizedFrostmanMultiplicityV1

noncomputable section

/-- The coordinate-transported affine ambient has exactly the volume of the
source tube carrier. -/
theorem coordinateTubeAmbient_volume
    {radius : NNReal} (axis : Fin 3) (T : Tube radius) :
    volume (affineImageConvexBody
      (coordinateToVerticalRigidMotion axis).toAffineEquiv T.body : Set Space) =
        volume T.carrier := by
  rw [coe_affineImageConvexBody]
  change volume ((coordinateToVerticalRigidMotion axis) '' T.carrier) =
    volume T.carrier
  exact volume_rigidMotion_image
    (coordinateToVerticalRigidMotion axis) T.carrier

/-- Positive tube radius makes the coordinate-transported ambient volume
nonzero. -/
theorem coordinateTubeAmbient_volume_ne_zero
    {radius : NNReal} (axis : Fin 3) (T : Tube radius)
    (hradius : 0 < radius) :
    volume (affineImageConvexBody
      (coordinateToVerticalRigidMotion axis).toAffineEquiv T.body : Set Space) ≠
        0 := by
  rw [coordinateTubeAmbient_volume]
  exact (T.volume_pos hradius).ne'

/-- The coordinate-transported ambient volume is finite. -/
theorem coordinateTubeAmbient_volume_ne_top
    {radius : NNReal} (axis : Fin 3) (T : Tube radius) :
    volume (affineImageConvexBody
      (coordinateToVerticalRigidMotion axis).toAffineEquiv T.body : Set Space) ≠
        ∞ := by
  rw [coordinateTubeAmbient_volume]
  exact T.volume_lt_top.ne

#print axioms coordinateTubeAmbient_volume
#print axioms coordinateTubeAmbient_volume_ne_zero
#print axioms coordinateTubeAmbient_volume_ne_top

end
end Family8Family7CoordinateTubeAmbientVolumeV2

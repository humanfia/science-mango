import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
open FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Actual tubes snapped independently to a staggered graph-C grid

For a fixed grid label, this operation is a function of one tube only.  It
therefore preserves the sampled-family cardinality bound under `Finset.image`,
unlike pair-dependent normalization to the other endpoint's exact C value.
-/

/-- Replace one tube's graph-C coordinate by the centre of its staggered-grid
cell, preserving its graph coordinates `a`, `b`, and `d`. -/
def threeShiftCGridNormalizeTube {radius : NNReal}
    (k : Fin 3) (T : Tube radius) : Tube radius :=
  normalizeTubeC T
    (threeShiftNormalizedC (radius : Real) k (tubeGraphC T))

@[simp] theorem tubeGraphA_threeShiftCGridNormalizeTube
    {radius : NNReal} (k : Fin 3) (T : Tube radius) :
    tubeGraphA (threeShiftCGridNormalizeTube k T) = tubeGraphA T := by
  simp [threeShiftCGridNormalizeTube]

@[simp] theorem tubeGraphB_threeShiftCGridNormalizeTube
    {radius : NNReal} (k : Fin 3) (T : Tube radius) :
    tubeGraphB (threeShiftCGridNormalizeTube k T) = tubeGraphB T := by
  simp [threeShiftCGridNormalizeTube]

@[simp] theorem tubeGraphC_threeShiftCGridNormalizeTube
    {radius : NNReal} (k : Fin 3) (T : Tube radius) :
    tubeGraphC (threeShiftCGridNormalizeTube k T) =
      threeShiftNormalizedC (radius : Real) k (tubeGraphC T) := by
  simp [threeShiftCGridNormalizeTube]

@[simp] theorem tubeGraphD_threeShiftCGridNormalizeTube
    {radius : NNReal} (k : Fin 3) (T : Tube radius) :
    tubeGraphD (threeShiftCGridNormalizeTube k T) = tubeGraphD T := by
  simp [threeShiftCGridNormalizeTube]

/-- Snapping one actual tube changes graph C by at most one tube radius. -/
theorem abs_tubeGraphC_threeShiftCGridNormalizeTube_sub_le
    {radius : NNReal} (hradius : 0 < radius)
    (k : Fin 3) (T : Tube radius) :
    |tubeGraphC (threeShiftCGridNormalizeTube k T) - tubeGraphC T| <=
      (radius : Real) := by
  rw [tubeGraphC_threeShiftCGridNormalizeTube, abs_sub_comm]
  exact abs_sub_threeShiftNormalizedC_le (by exact_mod_cast hradius) k

/-- A good grid label gives literal common C after the two endpoints are
snapped independently. -/
theorem tubeGraphC_threeShiftCGridNormalizeTube_eq_of_good
    {radius : NNReal} {k : Fin 3} {T U : Tube radius}
    (hgood : GoodThreeShiftCGridPair (radius : Real)
      (tubeGraphC T) (tubeGraphC U) k) :
    tubeGraphC (threeShiftCGridNormalizeTube k T) =
      tubeGraphC (threeShiftCGridNormalizeTube k U) := by
  simp only [tubeGraphC_threeShiftCGridNormalizeTube]
  exact goodThreeShiftCGridPair_normalized_eq hgood

/-- The reduced `(a,b,d)` distance used throughout the cinematic argument is
unchanged when both endpoints are snapped to the grid. -/
@[simp] theorem tubePairCoefficientDistance_threeShiftCGridNormalizeTube
    {radius : NNReal} (k : Fin 3) (T U : Tube radius) :
    tubePairCoefficientDistance
        (threeShiftCGridNormalizeTube k T)
        (threeShiftCGridNormalizeTube k U) =
      tubePairCoefficientDistance T U := by
  simp [threeShiftCGridNormalizeTube]

/-- The projected reduced metric is unchanged as well. -/
@[simp] theorem projectedTubePairCoefficientDistance_threeShiftCGridNormalizeTube
    {radius : NNReal} (k : Fin 3) (T U : Tube radius) :
    projectedTubePairCoefficientDistance
        (threeShiftCGridNormalizeTube k T)
        (threeShiftCGridNormalizeTube k U) =
      projectedTubePairCoefficientDistance T U := by
  simp [threeShiftCGridNormalizeTube]

#print axioms abs_tubeGraphC_threeShiftCGridNormalizeTube_sub_le
#print axioms tubeGraphC_threeShiftCGridNormalizeTube_eq_of_good
#print axioms tubePairCoefficientDistance_threeShiftCGridNormalizeTube

end

end FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1

import FamilyStickyGrounding.FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
import FamilyStickyGrounding.FamilyStickyWZ2FixedVerticalChartNonzeroV1

set_option autoImplicit false

namespace FamilyStickyWZ2FixedVerticalChartContainmentV1

open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2CinematicTubeContainmentV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2FixedVerticalChartNonzeroV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# WZ2 carrier containment for tubes in the literal fixed vertical chart

This module plugs the tracked-only fixed-chart nonzero producer into the
previously proved physical-tube coordinate adapter.  Thus the caller supplies
literal chart membership rather than the geometric denominator conclusion.
It makes no cardinality-retention or final projection-estimate claim.
-/

/-- The full carrier of a tube selected by the literal vertical chart has the
WZ2 cinematic-box containment. -/
theorem twistedProjection_image_tubeCarrier_subset_of_mem_fixedVerticalChart
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    {i : iota} (hi : i ∈ fixedVerticalChartIndices fine source)
    (f : Real -> Real) (F L : Real)
    (hF : 0 <= F) (hL : 0 <= L)
    (hfBound : forall z, |f z| <= F)
    (hfLip : forall z t, |f z - f t| <= L * |z - t|) :
    twistedProjection f '' (fine.tubes i).carrier ⊆
      cinematicBoxNeighborhood f (tubeAxisHeightSet (fine.tubes i))
        (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
        (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i))
        ((radius : Real) + F * radius +
          L * radius * tubeAxisYBound (fine.tubes i)) := by
  exact twistedProjection_image_tubeCarrier_subset
    (fine.tubes i)
    (direction_two_ne_zero_of_mem_fixedVerticalChartIndices fine source hi)
    f F L hF hL hfBound hfLip

/-- Every actual shading piece indexed by the literal fixed chart inherits
the same callback-free cinematic-box containment. -/
theorem twistedProjection_image_shadingCarrier_subset_of_mem_fixedVerticalChart
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    (Y : Shading (tubeBodyFamily fine.tubes))
    {i : iota} (hi : i ∈ fixedVerticalChartIndices fine source)
    (f : Real -> Real) (F L : Real)
    (hF : 0 <= F) (hL : 0 <= L)
    (hfBound : forall z, |f z| <= F)
    (hfLip : forall z t, |f z - f t| <= L * |z - t|) :
    twistedProjection f '' Y.carrier i ⊆
      cinematicBoxNeighborhood f (tubeAxisHeightSet (fine.tubes i))
        (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
        (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i))
        ((radius : Real) + F * radius +
          L * radius * tubeAxisYBound (fine.tubes i)) := by
  exact (Set.image_mono (Y.carrier_subset i)).trans
    (twistedProjection_image_tubeCarrier_subset_of_mem_fixedVerticalChart
      fine source hi f F L hF hL hfBound hfLip)

#print axioms twistedProjection_image_tubeCarrier_subset_of_mem_fixedVerticalChart
#print axioms twistedProjection_image_shadingCarrier_subset_of_mem_fixedVerticalChart

end
end FamilyStickyWZ2FixedVerticalChartContainmentV1

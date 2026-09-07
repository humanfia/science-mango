import FamilyStickyCinematicL32ActualProjectedSourceCoefficientCapV1
import FamilyStickyCinematicL32ActualExtremalSameScaleCoverV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal

namespace Family8Family7ProjectedSourceAmbientScaleCoverCoefficientCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedSourceAmbientDistinctSelectionV1
open FamilyStickyCinematicL32ActualProjectedSourceCoefficientCapV1
open FamilyStickyCinematicL32ActualSameScaleCoverParallelLossCapV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32ActualExtremalSameScaleCoverV1

noncomputable section

universe u v

/-!
# Projected coefficient cap from an ambient same-scale cover

This is the primitive geometry read by the native-high selector.  The
projected physical datum may be any subfamily of the ambient cover; no
extremal mass or union-volume field is required for the selected subfamily.
-/

theorem activeNearCoefficientIndices_cap_on_band_of_ambientScaleCover
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (Z : FiniteProjectedShading point iota)
    {ambient : Finset iota}
    (hambient : Z.ambient ⊆ ambient)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (ambient : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (C : @TubeScaleCover delta delta iota _ fine ambient)
    {parallelLoss : Nat}
    (hcluster : ∀ U : Tube delta,
      (C.parallelCluster U).card ≤ parallelLoss)
    {lower upper multiplicity : Nat}
    (hvertical : ∀ i, i ∈ Z.ambient ->
      (fine.tubes i).axis.direction 2 ≠ 0)
    (hcBucket : ∀ i, i ∈ Z.ambient -> ∀ j, j ∈ Z.ambient ->
      |projectedTubeGraphC (fine.tubes i) -
        projectedTubeGraphC (fine.tubes j)| ≤ (delta : Real) / 2)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤
      multiplicity) :
    ∀ x, x ∈ Z.multiplicityBand lower upper -> ∀ center,
      center ∈ actualProjectedCriticalFamily fine (Z.activeAtPoint x) ->
      (activeNearCoefficientIndices fine (Z.activeAtPoint x) center
        (delta : Real)).card ≤ multiplicity := by
  intro x _hx center _hcenter
  let Cx : @TubeScaleCover delta delta iota _ fine (Z.activeAtPoint x) :=
    restrictActualTubeScaleCover C <| by
      intro i hi
      exact hambient ((Z.mem_activeAtPoint x i).mp hi).1
  apply activeNearCoefficientIndices_card_le_multiplicity_of_parallelLoss
    Cx hdelta
  · exact essentiallyDistinct_activeAtPoint_of_ambient fine Z
      (fun i hi j hj hij => hpair (hambient hi) (hambient hj) hij) x
  · intro U
    change (C.parallelCluster U).card ≤ parallelLoss
    exact hcluster U
  · intro j hj i hi
    exact halfCoefficient_parallel_of_ambient_bucket fine Z hvertical
      hcBucket x j hj i hi
  · exact hloss

#print axioms activeNearCoefficientIndices_cap_on_band_of_ambientScaleCover

end

end Family8Family7ProjectedSourceAmbientScaleCoverCoefficientCapV1

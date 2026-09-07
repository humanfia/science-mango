import Family8Grounding.Family8Family7CoordinateToVerticalParallelTransportV1
import Family8Grounding.Family8Family7ProjectedSourceAmbientScaleCoverCoefficientCapV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal

namespace Family8Family7CoordinateToVerticalExtremalCoefficientCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8GeneralizedFrostmanMultiplicityV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalParallelTransportV1
open Family8Family7ProjectedSourceAmbientScaleCoverCoefficientCapV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32ActualExtremalSameScaleCoverV1

noncomputable section

universe u v

/-!
# Coordinate-transported extremal coefficient cap

Only the upstream extremal family's distinctness and same-scale cover are
used.  The vertical projected datum is allowed to be an arbitrary ambient
subfamily, so restricting to a graph-c bucket incurs no extremality premise.
-/

theorem activeNearCoefficientIndices_cap_on_band_of_coordinateExtremal
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {Y : Shading fine.bodyFamily} {ambient : Finset iota}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily fine Y ambient parallelLoss epsilon sigma)
    (k : Fin 3)
    (Z : FiniteProjectedShading point iota)
    (hambient : Z.ambient ⊆ ambient)
    {lower upper multiplicity : Nat}
    (hvertical : ∀ i, i ∈ Z.ambient ->
      ((coordinateToVerticalFamily k fine).tubes i).axis.direction 2 ≠ 0)
    (hcBucket : ∀ i, i ∈ Z.ambient -> ∀ j, j ∈ Z.ambient ->
      |projectedTubeGraphC ((coordinateToVerticalFamily k fine).tubes i) -
        projectedTubeGraphC ((coordinateToVerticalFamily k fine).tubes j)| ≤
          (delta : Real) / 2)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤
      multiplicity) :
    ∀ x, x ∈ Z.multiplicityBand lower upper -> ∀ center,
      center ∈ actualProjectedCriticalFamily
        (coordinateToVerticalFamily k fine) (Z.activeAtPoint x) ->
      (activeNearCoefficientIndices (coordinateToVerticalFamily k fine)
        (Z.activeAtPoint x) center (delta : Real)).card ≤ multiplicity := by
  let C := coordinateToVerticalTubeScaleCover k
    (actualExtremalSameScaleCover G)
  refine activeNearCoefficientIndices_cap_on_band_of_ambientScaleCover
    Z hambient G.delta_pos ?_ C ?_ hvertical hcBucket hloss
  · intro i hi j hj hij
    rw [coordinateToVerticalFamily_tubes,
      coordinateToVerticalFamily_tubes,
      essentiallyDistinct_rigidTube_iff]
    exact G.essentially_distinct hi hj hij
  · intro U
    exact coordinateToVerticalTubeScaleCover_cluster_card_le k
      (actualExtremalSameScaleCover G)
      (actualExtremalSameScaleCover_cluster_bound G) U

#print axioms activeNearCoefficientIndices_cap_on_band_of_coordinateExtremal

end

end Family8Family7CoordinateToVerticalExtremalCoefficientCapV1

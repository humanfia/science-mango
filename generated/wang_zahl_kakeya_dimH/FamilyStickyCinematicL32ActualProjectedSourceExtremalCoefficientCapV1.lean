import FamilyStickyCinematicL32ActualProjectedSourceCoefficientCapV1
import FamilyStickyCinematicL32ActualExtremalSameScaleCoverV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyCinematicL32ActualProjectedSourceExtremalCoefficientCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedSourceCoefficientCapV1
open FamilyStickyCinematicL32ActualSameScaleCoverParallelLossCapV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32ActualExtremalSameScaleCoverV1

noncomputable section

universe u v

/-!
# Extremal-family producer for the projected-source coefficient cap

The primitive extremal record supplies positive radius, global essential
distinctness, and an actual same-scale cover with cluster loss.  Restricting
that cover to every projected incidence fibre, and using only the ambient
upper-chart/c-bucket facts, removes the former pointwise `hpair` and
`hactiveCap` callbacks completely.
-/

theorem activeNearCoefficientIndices_cap_on_band_of_extremal
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {Y : Shading fine.bodyFamily}
    (Z : FiniteProjectedShading point iota)
    {parallelLoss : Nat} {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily fine Y Z.ambient parallelLoss
      epsilon sigma)
    {lower upper multiplicity : Nat}
    (hvertical : forall i, i ∈ Z.ambient ->
      (fine.tubes i).axis.direction 2 ≠ 0)
    (hcBucket : forall i, i ∈ Z.ambient -> forall j, j ∈ Z.ambient ->
      |projectedTubeGraphC (fine.tubes i) -
        projectedTubeGraphC (fine.tubes j)| ≤ (delta : Real) / 2)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤
      multiplicity) :
    forall x, x ∈ Z.multiplicityBand lower upper -> forall center,
      center ∈ actualProjectedCriticalFamily fine (Z.activeAtPoint x) ->
      (activeNearCoefficientIndices fine (Z.activeAtPoint x) center
        (delta : Real)).card ≤ multiplicity := by
  intro x hx center _hcenter
  let C := actualExtremalProjectedActiveCover G Z (fun _ hi => hi) x
  apply activeNearCoefficientIndices_card_le_multiplicity_of_parallelLoss
    C G.delta_pos
    (FamilyStickyCinematicL32ActualProjectedSourceAmbientDistinctSelectionV1.essentiallyDistinct_activeAtPoint_of_ambient
      fine Z G.essentially_distinct x)
  · intro U
    exact actualExtremalProjectedActiveCover_cluster_bound
      G Z (fun _ hi => hi) x U
  · intro j hj i hi
    exact halfCoefficient_parallel_of_ambient_bucket fine Z hvertical
      hcBucket x j hj i hi
  · exact hloss

#print axioms activeNearCoefficientIndices_cap_on_band_of_extremal

end

end FamilyStickyCinematicL32ActualProjectedSourceExtremalCoefficientCapV1

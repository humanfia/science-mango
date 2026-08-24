import FamilyStickyCinematicL32ActualProjectedSourceAmbientDistinctSelectionV1
import FamilyStickyCinematicL32ActualSameScaleCoverFullCoefficientCapV1
import FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
import FamilyStickyCinematicL32ActualGraphSlopeParallelV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyCinematicL32ActualProjectedSourceCoefficientCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedSourceAmbientDistinctSelectionV1
open FamilyStickyCinematicL32ActualSameScaleCoverFullCoefficientCapV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32ActualGraphSlopeParallelV1

noncomputable section

universe u v

/-!
# Actual projected-source coefficient-fibre cap

The initial upper-chart/c-bucket ambient family supplies nonverticality and
the half-radius c-slope gap.  Since every literal projected active family is
a filter of that ambient family, these facts restrict automatically.  The
clean graph-slope lemma, same-scale cover rigidity, and finite `13^3` net
then produce the exact local coefficient cap required by critical-family
selection.
-/

/-- The ambient upper-chart and c-bucket facts restrict to a half-scale
coefficient fibre at every projected point. -/
theorem halfCoefficient_parallel_of_ambient_bucket
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Z : FiniteProjectedShading point iota)
    (hvertical : forall i, i ∈ Z.ambient ->
      (fine.tubes i).axis.direction 2 ≠ 0)
    (hcBucket : forall i, i ∈ Z.ambient -> forall j, j ∈ Z.ambient ->
      |projectedTubeGraphC (fine.tubes i) -
        projectedTubeGraphC (fine.tubes j)| ≤ (delta : Real) / 2)
    (x : point) (j : iota) (hj : j ∈ Z.activeAtPoint x)
    (i : iota)
    (hi : i ∈ activeNearCoefficientIndices fine (Z.activeAtPoint x)
      (fine.tubes j) ((delta : Real) / 2)) :
    EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j) := by
  have hjAmbient : j ∈ Z.ambient := ((Z.mem_activeAtPoint x j).mp hj).1
  have hiActive : i ∈ Z.activeAtPoint x := (Finset.mem_filter.mp hi).1
  have hiAmbient : i ∈ Z.ambient :=
    ((Z.mem_activeAtPoint x i).mp hiActive).1
  exact essentiallyParallelAtScale_of_halfCBucket_halfCoefficient
    (fine.tubes i) (fine.tubes j)
    (hvertical i hiAmbient) (hvertical j hjAmbient)
    (hcBucket i hiAmbient j hjAmbient) (Finset.mem_filter.mp hi).2

/-- One actual same-scale cover at a point produces the local full-scale
coefficient cap, with all losses explicit. -/
theorem activeNearCoefficientIndices_cap_of_ambient_bucket_cover
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Z : FiniteProjectedShading point iota)
    (hdelta : 0 < delta)
    (hambient : Set.Pairwise (Z.ambient : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hvertical : forall i, i ∈ Z.ambient ->
      (fine.tubes i).axis.direction 2 ≠ 0)
    (hcBucket : forall i, i ∈ Z.ambient -> forall j, j ∈ Z.ambient ->
      |projectedTubeGraphC (fine.tubes i) -
        projectedTubeGraphC (fine.tubes j)| ≤ (delta : Real) / 2)
    (x : point)
    (C : @TubeScaleCover delta delta iota _ fine (Z.activeAtPoint x))
    {multiplicity : Nat}
    (hcount : actualHalfScaleCoefficientCoverLoss * C.count ≤ multiplicity)
    (center : Tube delta) :
    (activeNearCoefficientIndices fine (Z.activeAtPoint x) center
      (delta : Real)).card ≤ multiplicity := by
  apply activeNearCoefficientIndices_card_le_multiplicity C hdelta
    (essentiallyDistinct_activeAtPoint_of_ambient fine Z hambient x)
  · intro j hj i hi
    exact halfCoefficient_parallel_of_ambient_bucket fine Z hvertical
      hcBucket x j hj i hi
  · exact hcount

/-- Pointwise actual covers and their explicit count budget supply the whole
local-cap function consumed by continuum critical selection. -/
theorem activeNearCoefficientIndices_cap_on_multiplicityBand
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Z : FiniteProjectedShading point iota)
    {lower upper multiplicity : Nat}
    (hdelta : 0 < delta)
    (hambient : Set.Pairwise (Z.ambient : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hvertical : forall i, i ∈ Z.ambient ->
      (fine.tubes i).axis.direction 2 ≠ 0)
    (hcBucket : forall i, i ∈ Z.ambient -> forall j, j ∈ Z.ambient ->
      |projectedTubeGraphC (fine.tubes i) -
        projectedTubeGraphC (fine.tubes j)| ≤ (delta : Real) / 2)
    (C : forall x, x ∈ Z.multiplicityBand lower upper ->
      @TubeScaleCover delta delta iota _ fine (Z.activeAtPoint x))
    (hcount : forall x, forall hx : x ∈ Z.multiplicityBand lower upper,
      actualHalfScaleCoefficientCoverLoss * (C x hx).count ≤ multiplicity) :
    forall x, x ∈ Z.multiplicityBand lower upper -> forall center,
      center ∈ actualProjectedCriticalFamily fine (Z.activeAtPoint x) ->
      (activeNearCoefficientIndices fine (Z.activeAtPoint x) center
        (delta : Real)).card ≤ multiplicity := by
  intro x hx center _hcenter
  exact activeNearCoefficientIndices_cap_of_ambient_bucket_cover
    fine Z hdelta hambient hvertical hcBucket x (C x hx)
      (hcount x hx) center

#print axioms halfCoefficient_parallel_of_ambient_bucket
#print axioms activeNearCoefficientIndices_cap_of_ambient_bucket_cover
#print axioms activeNearCoefficientIndices_cap_on_multiplicityBand

end

end FamilyStickyCinematicL32ActualProjectedSourceCoefficientCapV1

import FamilyStickyCinematicL32ActualSameScaleCoverAlignmentV1
import FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyCinematicL32ActualSameScaleCoverFullCoefficientCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family6ProjectiveSineTriangleV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickySameRadiusTubeContainmentDirectionV1
open FamilyStickyCinematicL32ActualSameScaleCoverFiberCapV1
open FamilyStickyCinematicL32ActualSameScaleCoverAlignmentV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1

noncomputable section

universe u

variable {delta : NNReal} {iota : Type u} [DecidableEq iota]
  {fine : UniformTubeFamily delta iota} {active : Finset iota}
  (C : @TubeScaleCover delta delta iota _ fine active)

/-!
# Full actual coefficient cap from active-centred half-scale alignment

The geometric layer bounds every active-centred half coefficient ball by
the literal number of same-scale cover parents.  The independent finite
three-coordinate net then covers an arbitrary full coefficient ball with
`13^3` such half balls.
-/

/-- Parent localization for a half-scale coefficient fibre centered at an
arbitrary active tube. -/
theorem actualNearCoefficientCoverParents_subset_parallelCluster_of_activeCenter
    {scale : Real} (j : iota) (hj : j ∈ active)
    (hnear : forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j) scale ->
        EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j)) :
    actualNearCoefficientCoverParents C (fine.tubes j) scale ⊆
      C.parallelCluster (C.tubes (C.parent j)) := by
  classical
  intro q hq
  obtain ⟨i, hiNear, rfl⟩ :=
    (mem_actualNearCoefficientCoverParents_iff C (fine.tubes j) scale q).mp hq
  have hi : i ∈ active := (Finset.mem_filter.mp hiNear).1
  have hnearIJ := hnear i hiNear
  have hchildI := Tube.sin_angle_direction_eq_zero_of_sameRadius_carrier_subset
    (fine.tubes i) (C.tubes (C.parent i)) (C.carrier_subset i hi)
  have hchildJ := Tube.sin_angle_direction_eq_zero_of_sameRadius_carrier_subset
    (fine.tubes j) (C.tubes (C.parent j)) (C.carrier_subset j hj)
  have hmiddle : Real.sin (InnerProductGeometry.angle
      (fine.tubes i).axis.direction
      (C.tubes (C.parent j)).axis.direction) ≤ (delta : Real) := by
    calc
      Real.sin (InnerProductGeometry.angle
          (fine.tubes i).axis.direction
          (C.tubes (C.parent j)).axis.direction) ≤
        Real.sin (InnerProductGeometry.angle
          (fine.tubes i).axis.direction
          (fine.tubes j).axis.direction) +
        Real.sin (InnerProductGeometry.angle
          (fine.tubes j).axis.direction
          (C.tubes (C.parent j)).axis.direction) :=
            sin_angle_triangle_projective _ _ _
      _ ≤ (delta : Real) + 0 := add_le_add hnearIJ hchildJ.le
      _ = (delta : Real) := add_zero _
  have hchildIFirst : Real.sin (InnerProductGeometry.angle
      (C.tubes (C.parent i)).axis.direction
      (fine.tubes i).axis.direction) = 0 := by
    simpa only [InnerProductGeometry.angle_comm] using hchildI
  have hparents : Real.sin (InnerProductGeometry.angle
      (C.tubes (C.parent i)).axis.direction
      (C.tubes (C.parent j)).axis.direction) ≤ (delta : Real) := by
    calc
      Real.sin (InnerProductGeometry.angle
          (C.tubes (C.parent i)).axis.direction
          (C.tubes (C.parent j)).axis.direction) ≤
        Real.sin (InnerProductGeometry.angle
          (C.tubes (C.parent i)).axis.direction
          (fine.tubes i).axis.direction) +
        Real.sin (InnerProductGeometry.angle
          (fine.tubes i).axis.direction
          (C.tubes (C.parent j)).axis.direction) :=
            sin_angle_triangle_projective _ _ _
      _ ≤ 0 + (delta : Real) := add_le_add hchildIFirst.le hmiddle
      _ = (delta : Real) := zero_add _
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparents⟩

/-- Every active-centred half coefficient fibre is bounded by the actual
cover count. -/
theorem activeNearCoefficientIndices_card_le_coverCount_of_activeCenter
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real} (j : iota) (hj : j ∈ active)
    (hnear : forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j) scale ->
        EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j)) :
    (activeNearCoefficientIndices fine active (fine.tubes j) scale).card ≤
      C.count := by
  have hfibre := activeNearCoefficientIndices_card_le_parent_card
    C hdelta hpair (fine.tubes j) scale
  have hparents :=
    actualNearCoefficientCoverParents_subset_parallelCluster_of_activeCenter
      C j hj hnear
  exact hfibre.trans <|
    (Finset.card_le_card hparents).trans
      (actualParallelCluster_card_le_count C (C.tubes (C.parent j)))

/-- The complete local cap with all finite losses explicit. -/
theorem activeNearCoefficientIndices_card_le_coverLoss_mul_count
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hhalfParallel : forall j, j ∈ active -> forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j)
        ((delta : Real) / 2) ->
      EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j))
    (center : Tube delta) :
    (activeNearCoefficientIndices fine active center (delta : Real)).card ≤
      actualHalfScaleCoefficientCoverLoss * C.count := by
  apply activeNearCoefficientIndices_card_le_full_of_half
    fine active hdelta
  intro j hj
  exact activeNearCoefficientIndices_card_le_coverCount_of_activeCenter
    C hdelta hpair j hj (hhalfParallel j hj)

/-- Numerical domination turns the explicit geometric count into the exact
`multiplicity` cap consumed upstream. -/
theorem activeNearCoefficientIndices_card_le_multiplicity
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hhalfParallel : forall j, j ∈ active -> forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j)
        ((delta : Real) / 2) ->
      EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j))
    {multiplicity : Nat}
    (hcount : actualHalfScaleCoefficientCoverLoss * C.count ≤ multiplicity)
    (center : Tube delta) :
    (activeNearCoefficientIndices fine active center (delta : Real)).card ≤
      multiplicity :=
  (activeNearCoefficientIndices_card_le_coverLoss_mul_count
    C hdelta hpair hhalfParallel center).trans hcount

#print axioms activeNearCoefficientIndices_card_le_coverCount_of_activeCenter
#print axioms activeNearCoefficientIndices_card_le_coverLoss_mul_count
#print axioms activeNearCoefficientIndices_card_le_multiplicity

end

end FamilyStickyCinematicL32ActualSameScaleCoverFullCoefficientCapV1

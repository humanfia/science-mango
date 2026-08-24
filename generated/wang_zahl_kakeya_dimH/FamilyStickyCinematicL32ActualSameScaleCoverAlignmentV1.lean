import FamilyStickyCinematicL32ActualSameScaleCoverFiberCapV1
import Family6Grounding.Family6ProjectiveSineTriangleV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyCinematicL32ActualSameScaleCoverAlignmentV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family6ProjectiveSineTriangleV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickySameRadiusTubeContainmentDirectionV1
open FamilyStickyCinematicL32ActualSameScaleCoverFiberCapV1

noncomputable section

universe u

variable {delta : NNReal} {iota : Type u} [DecidableEq iota]
  {fine : UniformTubeFamily delta iota} {active : Finset iota}
  (C : @TubeScaleCover delta delta iota _ fine active)

/-!
# Clean actual alignment of coefficient fibres with same-scale cover parents

The only analytic input retained here is a fine--fine projective direction
bound inside each actual coefficient fibre.  Literal child--parent carrier
containment supplies zero projective angle at both ends, and the projective
sine triangle inequality puts every hit parent into one genuine cluster.
-/

/-- The earliest analytic direction obligation on an actual coefficient
fibre.  This is strictly weaker than its desired cardinal conclusion. -/
def ActualNearCoefficientFineParallel (scale : Real) : Prop :=
  forall center,
    center ∈ selectedTubes (activeTubeImage fine active) scale ->
      forall i, i ∈ activeNearCoefficientIndices fine active center scale ->
        EssentiallyParallelAtScale (fine.tubes i) center

/-- Every parent hit by one selected coefficient fibre lies in the cluster
of the actual parent of one active representative of its centre. -/
theorem actualNearCoefficientCoverParents_subset_parallelCluster
    {scale : Real}
    (hnear : ActualNearCoefficientFineParallel
      (fine := fine) (active := active) scale)
    (center : Tube delta)
    (hcenter : center ∈ selectedTubes (activeTubeImage fine active) scale) :
    exists U : Tube delta,
      actualNearCoefficientCoverParents C center scale ⊆
        C.parallelCluster U := by
  classical
  have hcenterImage : center ∈ activeTubeImage fine active :=
    selectedTubes_subset (activeTubeImage fine active) scale hcenter
  obtain ⟨j, hj, hjEq⟩ :=
    (mem_activeTubeImage_iff fine active center).mp hcenterImage
  refine ⟨C.tubes (C.parent j), ?_⟩
  intro q hq
  obtain ⟨i, hiNear, rfl⟩ :=
    (mem_actualNearCoefficientCoverParents_iff C center scale q).mp hq
  have hi : i ∈ active := (Finset.mem_filter.mp hiNear).1
  have hnearIJ : EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j) := by
    rw [hjEq]
    exact hnear center hcenter i hiNear
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

/-- The clean same-scale cover converts the analytic direction obligation
into the fully explicit coefficient-fibre cap `C.count`. -/
theorem activeNearCoefficientIndices_card_le_coverCount
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real}
    (hnear : ActualNearCoefficientFineParallel
      (fine := fine) (active := active) scale)
    (center : Tube delta)
    (hcenter : center ∈ selectedTubes (activeTubeImage fine active) scale) :
    (activeNearCoefficientIndices fine active center scale).card ≤ C.count := by
  have hfibre := activeNearCoefficientIndices_card_le_parent_card
    C hdelta hpair center scale
  obtain ⟨U, hparents⟩ :=
    actualNearCoefficientCoverParents_subset_parallelCluster
      C hnear center hcenter
  exact hfibre.trans <|
    (Finset.card_le_card hparents).trans
      (actualParallelCluster_card_le_count C U)

/-- Any numerical multiplicity dominating the actual cover count therefore
supplies the exact local cap consumed by the continuum selector. -/
theorem activeNearCoefficientIndices_card_le_of_coverCount
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real} {multiplicity : Nat}
    (hnear : ActualNearCoefficientFineParallel
      (fine := fine) (active := active) scale)
    (hcount : C.count ≤ multiplicity)
    (center : Tube delta)
    (hcenter : center ∈ selectedTubes (activeTubeImage fine active) scale) :
    (activeNearCoefficientIndices fine active center scale).card ≤
      multiplicity :=
  (activeNearCoefficientIndices_card_le_coverCount C hdelta hpair hnear
    center hcenter).trans hcount

#print axioms actualNearCoefficientCoverParents_subset_parallelCluster
#print axioms activeNearCoefficientIndices_card_le_coverCount
#print axioms activeNearCoefficientIndices_card_le_of_coverCount

end

end FamilyStickyCinematicL32ActualSameScaleCoverAlignmentV1

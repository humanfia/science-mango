import FamilyStickyCinematicL32ActualSameScaleCoverFiberCapV1
import Family6Grounding.Family6ProjectiveSineTriangleV1
import Mathlib.Tactic

/-!
# Fine directional clusters from a genuine same-scale cover

For a literal same-radius `TubeScaleCover`, positive radius and pairwise
essential distinctness make the parent map injective on the active fine
indices.  Same-radius carrier containment also gives zero projective sine
angle between every fine tube and its supplied parent.  Consequently the
parent map injects an active fine directional cluster into the corresponding
literal `TubeScaleCover.parallelCluster` with the same centre tube.

The final theorem transfers only an explicitly supplied parent-cluster
cardinality bound.  It does not manufacture a `parallelLoss` hypothesis and
does not assert a spatial concentration or `IsKatzTao` property.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set
open scoped ENNReal NNReal InnerProductSpace

namespace Family8EpsilonExtremalSameScaleFineParallelClusterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family6ProjectiveSineTriangleV1
open FamilyStickyCinematicL32ActualSameScaleCoverFiberCapV1

noncomputable section

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

/-- Active fine labels whose actual tube is essentially parallel to `U` at
the literal fine scale. -/
noncomputable def activeFineParallelCluster
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (U : Tube delta) : Finset iota := by
  classical
  exact active.filter fun i =>
    EssentiallyParallelAtScale (fine.tubes i) U

@[simp]
theorem mem_activeFineParallelCluster
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (U : Tube delta) (i : iota) :
    i ∈ activeFineParallelCluster fine active U ↔
      i ∈ active ∧ EssentiallyParallelAtScale (fine.tubes i) U := by
  classical
  simp [activeFineParallelCluster]

/-- Positive-radius essential distinctness and the existing same-scale
parent-fibre cap make the supplied parent map injective on all active fine
labels. -/
theorem parent_injectiveOn_active
    (C : @TubeScaleCover delta delta iota _ fine active)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Set.InjOn C.parent (active : Set iota) := by
  classical
  intro i hi j hj hparent
  have hcap := actualCoverParentFiber_card_le_one C hdelta hpair (C.parent i)
  apply (Finset.card_le_one.mp hcap)
  · exact Finset.mem_filter.mpr ⟨hi, rfl⟩
  · exact Finset.mem_filter.mpr ⟨hj, hparent.symm⟩

/-- A fine tube and its same-radius supplied parent have the same projective
direction.  Hence essential parallelism to an arbitrary same-scale centre
passes from the fine tube to its parent. -/
theorem parent_parallel_of_fine_parallel
    (C : @TubeScaleCover delta delta iota _ fine active)
    (i : iota) (hi : i ∈ active) (U : Tube delta)
    (hparallel : EssentiallyParallelAtScale (fine.tubes i) U) :
    EssentiallyParallelAtScale (C.tubes (C.parent i)) U := by
  have hchildParent :=
    FamilyStickySameRadiusTubeContainmentDirectionV1.Tube.sin_angle_direction_eq_zero_of_sameRadius_carrier_subset
      (fine.tubes i) (C.tubes (C.parent i)) (C.carrier_subset i hi)
  have hparentChild : Real.sin (InnerProductGeometry.angle
      (C.tubes (C.parent i)).axis.direction
      (fine.tubes i).axis.direction) = 0 := by
    simpa only [InnerProductGeometry.angle_comm] using hchildParent
  unfold EssentiallyParallelAtScale at hparallel ⊢
  calc
    Real.sin (InnerProductGeometry.angle
        (C.tubes (C.parent i)).axis.direction U.axis.direction) <=
      Real.sin (InnerProductGeometry.angle
          (C.tubes (C.parent i)).axis.direction
          (fine.tubes i).axis.direction) +
        Real.sin (InnerProductGeometry.angle
          (fine.tubes i).axis.direction U.axis.direction) :=
      sin_angle_triangle_projective _ _ _
    _ <= 0 + (delta : Real) := add_le_add hparentChild.le hparallel
    _ = (delta : Real) := zero_add _

/-- The supplied parent of every fine directional-cluster member lies in the
literal parent parallel cluster with the same centre. -/
theorem parent_mem_parallelCluster_of_mem_activeFineParallelCluster
    (C : @TubeScaleCover delta delta iota _ fine active)
    (U : Tube delta) (i : iota)
    (hi : i ∈ activeFineParallelCluster fine active U) :
    C.parent i ∈ C.parallelCluster U := by
  classical
  have hi' := (mem_activeFineParallelCluster fine active U i).mp hi
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, parent_parallel_of_fine_parallel C i hi'.1 U hi'.2⟩

/-- The active fine directional cluster injects into the supplied parent's
literal parallel cluster.  This is the lossless same-scale transfer. -/
theorem activeFineParallelCluster_card_le_parentParallelCluster
    (C : @TubeScaleCover delta delta iota _ fine active)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (U : Tube delta) :
    (activeFineParallelCluster fine active U).card <=
      (C.parallelCluster U).card := by
  classical
  have hcard :
      ((activeFineParallelCluster fine active U).image C.parent).card =
        (activeFineParallelCluster fine active U).card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj hparent
    exact parent_injectiveOn_active C hdelta hpair
      ((mem_activeFineParallelCluster fine active U i).mp hi).1
      ((mem_activeFineParallelCluster fine active U j).mp hj).1 hparent
  have hsubset :
      (activeFineParallelCluster fine active U).image C.parent ⊆
        C.parallelCluster U := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact parent_mem_parallelCluster_of_mem_activeFineParallelCluster C U i hi
  calc
    (activeFineParallelCluster fine active U).card =
        ((activeFineParallelCluster fine active U).image C.parent).card :=
      hcard.symm
    _ <= (C.parallelCluster U).card := Finset.card_le_card hsubset

/-- Epsilon-extremality supplies exactly the positivity and essential-
distinctness inputs needed above.  Any explicit uniform parent-cluster bound
therefore transfers to the active fine directional clusters. -/
theorem activeFineParallelCluster_card_le_of_epsilonExtremal_parentBound
    {Y : Shading fine.bodyFamily} {parallelLoss : Nat}
    {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily
      fine Y active parallelLoss epsilon sigma)
    (C : @TubeScaleCover delta delta iota _ fine active)
    {bound : Nat}
    (hcluster : forall U : Tube delta,
      (C.parallelCluster U).card <= bound)
    (U : Tube delta) :
    (activeFineParallelCluster fine active U).card <= bound := by
  exact (activeFineParallelCluster_card_le_parentParallelCluster
    C G.delta_pos G.essentially_distinct U).trans (hcluster U)

#print axioms activeFineParallelCluster
#print axioms parent_injectiveOn_active
#print axioms parent_parallel_of_fine_parallel
#print axioms activeFineParallelCluster_card_le_parentParallelCluster
#print axioms
  activeFineParallelCluster_card_le_of_epsilonExtremal_parentBound

end
end Family8EpsilonExtremalSameScaleFineParallelClusterV1

import Family8Grounding.Family8ActiveCoarseDeltaMaxXUpperV1
import Family8Grounding.Family8TubeScaleCoverOccupiedStickyAdapterV1
import Family4GlobalExtremalUpstream
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EpsilonExtremalActiveStickyXUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8ActiveCoarseDeltaMaxXUpperV1
open Family8TubeScaleCoverOccupiedStickyAdapterV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# Actual epsilon-extremal scale covers give honest active sticky X bounds

An `EpsilonExtremalTubeFamily` already supplies a genuine geometric
`TubeScaleCover` at every requested radius.  This module restricts the fine
family and shading to the literal active subtype, proves that the resulting
`ActualTubeDatum` is admissible directly from the extremal hypotheses, and
passes the supplied cover through the occupied-parent sticky adapter.

The resulting parent map is not an identity surrogate: its tube containment
is exactly the one supplied by `G.scale_covers`, and the theorem below returns
that original cover together with a parent-tube provenance equality.  On the
other hand, the epsilon-extremal interface does not say that the supplied
cover came from maximal-density factoring or that it strictly merges two
distinct active fine labels.  Neither stronger assertion is made here.
-/

variable {delta tau : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {Y : Shading fine.bodyFamily}
  {active : Finset iota} {parallelLoss : Nat}
  {epsilon sigma : Real}

/-! ## The literal active subtype datum -/

/-- Restrict the source shading without altering any carrier. -/
def activeSubtypeShading
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota) :
    Shading (fine.restrictTo active).bodyFamily where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := by
    simpa [UniformTubeFamily.bodyFamily] using Y.carrier_subset i.1

@[simp]
theorem activeSubtypeShading_carrier
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota)
    (i : {i // i ∈ active}) :
    (activeSubtypeShading fine Y active).carrier i = Y.carrier i.1 :=
  rfl

/-- The actual tube datum carried by precisely the active source labels. -/
def activeSubtypeDatum
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota) :
    ActualTubeDatum delta {i // i ∈ active} where
  family := fine.restrictTo active
  shading := activeSubtypeShading fine Y active

@[simp]
theorem activeSubtypeDatum_family
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota) :
    (activeSubtypeDatum fine Y active).family = fine.restrictTo active :=
  rfl

@[simp]
theorem activeSubtypeDatum_tubes
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota)
    (i : {i // i ∈ active}) :
    (activeSubtypeDatum fine Y active).family.tubes i = fine.tubes i.1 :=
  rfl

@[simp]
theorem activeSubtypeDatum_shading_carrier
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota)
    (i : {i // i ∈ active}) :
    (activeSubtypeDatum fine Y active).shading.carrier i = Y.carrier i.1 :=
  rfl

/-- Every admissibility field is inherited from the literal active clauses
of the epsilon-extremal datum. -/
theorem activeSubtypeDatum_isAdmissible
    (G : EpsilonExtremalTubeFamily
      fine Y active parallelLoss epsilon sigma) :
    (activeSubtypeDatum fine Y active).IsAdmissible := by
  refine
    { delta_pos := G.delta_pos
      delta_le_half := G.delta_le_half
      contained_in_unit_ball := ?_
      pairwise_essentiallyDistinct := ?_ }
  · intro i
    simpa using G.contained_in_unit_ball i.1 i.2
  · intro i _hi j _hj hij
    apply G.essentially_distinct
    · exact i.2
    · exact j.2
    · exact fun hijValue => hij (Subtype.ext hijValue)

/-! ## The supplied cover and its X upper bound -/

/-- The compact occupied-parent sticky cover attached to one supplied
epsilon-extremal scale cover. -/
abbrev activeStickyCover
    (C : @TubeScaleCover delta tau iota _ fine active) :
    StickyScaleCover (fine.restrictTo active) tau :=
  compactActiveSubtypeScaleCover C

/-- At every `tau ∈ [delta,1/2]`, the epsilon-extremal supplied cover yields
an honest active sticky cover with no more active coarse labels than active
fine labels and with the literal coarse-Delta-max X upper bound.  Returning
`C` and the parent-tube equality preserves the exact geometric provenance of
every sticky parent. -/
theorem exists_activeStickyCover_with_coarseDeltaMax_XUpper
    (G : EpsilonExtremalTubeFamily
      fine Y active parallelLoss epsilon sigma)
    (hdeltaTau : delta ≤ tau)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹) :
    ∃ C : @TubeScaleCover delta tau iota _ fine active,
      (∀ U : Tube tau, (C.parallelCluster U).card ≤ parallelLoss) ∧
      (activeStickyCover C).coarseCard ≤ active.card ∧
      (∀ i : {i // i ∈ active},
        (activeStickyCover C).coarse.tubes
            ((activeStickyCover C).parent i) =
          C.tubes (C.parent i.1)) ∧
      ((activeCoarseCardScaleMass (activeStickyCover C) : NNReal) : ENNReal) ≤
        1024 * coarseDeltaMax (activeStickyCover C) := by
  obtain ⟨C, hparallel⟩ := G.scale_covers tau hdeltaTau
    (htauHalf.trans (by norm_num))
  refine ⟨C, hparallel, ?_, ?_, ?_⟩
  · exact compactActiveSubtypeScaleCover_coarseCard_le_active C
  · intro i
    exact compactActiveSubtypeScaleCover_parent_tube C i
  · exact
      activeCoarseCardScaleMass_le_1024_mul_coarseDeltaMax
        (activeSubtypeDatum fine Y active)
        (activeSubtypeDatum_isAdmissible G)
        (activeStickyCover C) htauHalf

#print axioms activeSubtypeShading_carrier
#print axioms activeSubtypeDatum_tubes
#print axioms activeSubtypeDatum_isAdmissible
#print axioms exists_activeStickyCover_with_coarseDeltaMax_XUpper

end
end Family8EpsilonExtremalActiveStickyXUpperV1

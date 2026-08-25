import FamilyStickyGrounding.FamilyStickyHierarchyPrefixDenominatorOverheadV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyEndpointNonemptyProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchySuppliedPackingJointRandomMotionV1
open FamilyStickyHierarchyEndpointPrefixBridgeV1

noncomputable section

/-!
# Automatic nonemptiness of finite-chain endpoint families

The quantitative prefix-denominator producer needs one actual endpoint
occurrence.  That occurrence is already forced by existing hierarchy and
cover data:

* a certified hierarchy step has a nonempty active coarse set and a
  surjective parent map, hence its active fine set is nonempty;
* at level zero this active fine set is exactly the refined set of the
  effective level-zero family; and
* every Sticky cover of that family maps each active fine occurrence into its
  active coarse set.

Positive hierarchy depth supplies the level-zero step.  Consequently every
finite-chain endpoint index is nonempty, and the final same-joint density
endpoint no longer needs a caller-supplied nonemptiness premise.
-/

/-! ## Nonemptiness inherited from an actual hierarchy step -/

namespace MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-- The child refined set at every certified hierarchy step is nonempty.
This is derived from the step's occupied coarse set and parent surjectivity. -/
theorem effectiveFamily_refined_nonempty_of_lt
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (hl : l < depth) :
    (H.effectiveFamily l).refinement.refined.Nonempty := by
  let P := H.effectivePartition l hl
  rw [<- P.fineIndices_eq_refined]
  exact P.fineIndices_nonempty

/-- Positive depth specializes the preceding result to the common fine
family used by every endpoint cover. -/
theorem effectiveFamily_zero_refined_nonempty
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) :
    (H.effectiveFamily 0).refinement.refined.Nonempty :=
  effectiveFamily_refined_nonempty_of_lt H 0 hdepth

end MultiscaleTubeHierarchy

/-! ## Every cover of a nonempty refined family has an active parent -/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The cover's active fine set is literally the refined source set. -/
theorem activeFine_nonempty_of_refined_nonempty
    (U : StickyScaleCover fine rho)
    (hfine : fine.refinement.refined.Nonempty) :
    U.activeFine.Nonempty := by
  rw [U.activeFine_eq_refined]
  exact hfine

/-- Mapping one actual active fine occurrence to its declared parent gives an
actual active coarse occurrence. -/
theorem activeCoarse_nonempty_of_activeFine_nonempty
    (U : StickyScaleCover fine rho) (hactive : U.activeFine.Nonempty) :
    U.activeCoarse.Nonempty := by
  obtain ⟨i, hi⟩ := hactive
  exact ⟨U.parent i, U.parent_mem i hi⟩

/-- Direct refined-source form of active-parent nonemptiness. -/
theorem activeCoarse_nonempty_of_refined_nonempty
    (U : StickyScaleCover fine rho)
    (hfine : fine.refinement.refined.Nonempty) :
    U.activeCoarse.Nonempty :=
  activeCoarse_nonempty_of_activeFine_nonempty U
    (activeFine_nonempty_of_refined_nonempty U hfine)

/-- Package an active parent as the subtype used to index the active coarse
convex family. -/
theorem activeCoarseIndex_nonempty_of_refined_nonempty
    (U : StickyScaleCover fine rho)
    (hfine : fine.refinement.refined.Nonempty) :
    Nonempty {k // k ∈ U.activeCoarse} := by
  obtain ⟨k, hk⟩ := activeCoarse_nonempty_of_refined_nonempty U hfine
  exact ⟨⟨k, hk⟩⟩

end StickyScaleCover

/-! ## All finite-chain endpoint indices are nonempty -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
    (H.effectiveFamily 0))
  (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
    (H.effectiveRadius 0) depth)

namespace Endpoint

/-- Every upper endpoint cover has an actual active coarse occurrence. -/
theorem upperEndpointCover_activeCoarse_nonempty
    (hdepth : 0 < depth) (m : Fin depth) :
    (upperEndpointCover C S m).activeCoarse.Nonempty := by
  exact StickyScaleCover.activeCoarse_nonempty_of_refined_nonempty
    (upperEndpointCover C S m)
    (MultiscaleTubeHierarchy.effectiveFamily_zero_refined_nonempty H hdepth)

/-- The exact subtype indexing the endpoint convex family is nonempty at
every interval. -/
theorem endpointIndex_nonempty
    (hdepth : 0 < depth) (m : Fin depth) :
    Nonempty (EndpointIndex H C S m) := by
  obtain ⟨k, hk⟩ := upperEndpointCover_activeCoarse_nonempty H C S hdepth m
  exact ⟨⟨k, hk⟩⟩

/-- Quantified form consumed by constructions which work at all intervals. -/
theorem all_endpointIndex_nonempty (hdepth : 0 < depth) :
    forall m : Fin depth, Nonempty (EndpointIndex H C S m) :=
  endpointIndex_nonempty H C S hdepth

end Endpoint

/-! ## No-caller final denominator and density endpoints -/

namespace FinalAssembly

variable {H C S}
  {G : FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry H}
  {P : HierarchyPackingPlan.Plan H}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
  (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
    H G P C S epsilon massLoss bodyLoss katzTaoLoss frostmanError katzTaoError)
  (I : FamilyStickyHierarchyEndpointPrefixBridgeV1.Identification
    H A.hierarchy C S)

include A

/-- The final assembly certificate itself supplies every endpoint occurrence
needed by the quantitative denominator producer. -/
theorem endpointIndex_nonempty (m : Fin depth) :
    Nonempty (EndpointIndex H C S m) :=
  Endpoint.endpointIndex_nonempty H C S A.depth_pos m

/-- The explicit cardinality denominator certificate on the final
certificate's literal supplied joint output, with no nonemptiness argument. -/
theorem sameJoint_cardinalityDenominatorOverhead (m : Fin depth) :
    FamilyStickyHierarchyPrefixDenominatorOverheadV1.BodyPreservingEmbedding.DenominatorOverhead
      (F := endpointFamily H C S m)
      (G := suppliedPrefixFamily H A.hierarchy (I.effectivePrefix.path m)
        (I.endpointEffective.layer m) (I.effectivePrefix.parent m))
      (FamilyStickyHierarchyPrefixDenominatorOverheadV1.Identification.prefixCardinalityVolumeLoss
        I m) :=
  FamilyStickyHierarchyPrefixDenominatorOverheadV1.Identification.cardinalityDenominatorOverhead
    I m (endpointIndex_nonempty A m)

/-- Final no-caller endpoint: the parent-aggregated endpoint shading retains
density in the exact supplied prefix up to `16 * card PrefixIndex`. -/
theorem parentAggregatedDensity_div_cardinalityLoss_le_sameJointSuppliedPrefixDensity
    (m : Fin depth) (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    (FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover.parentAggregatedShading
        (upperEndpointCover C S m) Y).shadingDensity /
        FamilyStickyHierarchyPrefixDenominatorOverheadV1.Identification.prefixCardinalityVolumeLoss
          I m <=
      (FamilyStickyHierarchyEndpointPrefixShadingTransportV1.Identification.suppliedPrefixShading
        I m Y).shadingDensity := by
  exact
    FamilyStickyHierarchyPrefixDenominatorOverheadV1.FinalAssembly.parentAggregatedDensity_div_cardinalityLoss_le_sameJointSuppliedPrefixDensity
      A I m (endpointIndex_nonempty A m) Y

end FinalAssembly

#print axioms MultiscaleTubeHierarchy.effectiveFamily_refined_nonempty_of_lt
#print axioms MultiscaleTubeHierarchy.effectiveFamily_zero_refined_nonempty
#print axioms StickyScaleCover.activeCoarse_nonempty_of_refined_nonempty
#print axioms StickyScaleCover.activeCoarseIndex_nonempty_of_refined_nonempty
#print axioms Endpoint.upperEndpointCover_activeCoarse_nonempty
#print axioms Endpoint.endpointIndex_nonempty
#print axioms FinalAssembly.endpointIndex_nonempty
#print axioms FinalAssembly.sameJoint_cardinalityDenominatorOverhead
#print axioms FinalAssembly.parentAggregatedDensity_div_cardinalityLoss_le_sameJointSuppliedPrefixDensity

end
end FamilyStickyHierarchyEndpointNonemptyProducerV1

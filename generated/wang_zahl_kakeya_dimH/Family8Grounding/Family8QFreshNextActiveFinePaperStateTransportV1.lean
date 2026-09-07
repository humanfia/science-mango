import Family8Grounding.Family8DoublyBufferedDef212GroundedOneStepRunV1
import Mathlib.Tactic

/-!
# Local q-fresh successor to next active-fine paper state

The literal fresh factor stored by one paper successor is indexed by the
selected q-fibre.  A next paper step exposes instead the active-fine
restriction of that datum on its actual q-fresh cover.  These atoms are not
definitionally equal: the latter has one additional subtype layer.

For the real doubly-buffered q-fresh cover, exact Definition 2.12 readiness
forces the next active-fine set to be `univ`.  This module therefore produces
the canonical index equivalence, literal tube/shading identities,
admissibility, and exact radius/card transport.  Given readiness for that
one actual restricted atom, it also constructs the aligned next paper state
and proves that replacing the full fresh atom by its active-fine view changes
neither factor product.

No atom equality, coherent-cover reindexing, successor callback, later stage,
or complete next paper step is assumed or produced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8QFreshNextActiveFinePaperStateTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8DoublyBufferedDef212GroundedOneStepRunV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorStateV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentPaperFactorTransitionV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2.ParentwiseBadParentMassAwareFactorListState
open Family8SelectedFiberDoublyBufferedPaperFactorConnectorV1
open Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2
open Family8SourceDef212BoundCrossingTransitionV2
open Family8SourceDef212BoundCrossingTransitionV2.SourceDef212CrossingIntegratedSuccessor
open Family8SourceDef212BoundCrossingTransitionV2.SourceDef212PaperStepReadiness
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta tau : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {source : UniformTubeFamily delta sourceIndex}
  {depth : Nat}
  {Csource : CoherentStickyMultiscaleCover source}
  {hdeltaTau : delta ≤ tau} {hTauOne : tau ≤ 1}
  {Ysource : Shading
    (Csource.base.cover tau hdeltaTau hTauOne).coarse.bodyFamily}
  {hDtau : (rerootedPaperSourceDatum Csource tau hdeltaTau
    hTauOne Ysource).IsAdmissible}
  {S : FiniteScaleSequence tau depth}
  {epsilon : Real} {hepsilon : 0 ≤ epsilon}
  {eta : Nat → Real} {N : Nat}
  {W : FirstParentwiseNormalizedCrossingWitness
    (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Ysource)
    hDtau (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
    S epsilon hepsilon eta N}
  {R : SourceDef212CrossingSuccessorReadiness W}
  {X : SourceDef212CrossingIntegratedSuccessor W R}
  {H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
    W X.toParentwiseCrossingIntegratedSuccessor}

/-! ## One literal next active-fine atom -/

/-- The exact active-fine datum exposed by a next paper step on the q-fresh
destination cover. -/
abbrev qFreshNextActiveSourceDatum
    (Y : DoublyBufferedQFreshCrossingDestination H) :=
  badParentActiveFineSourceDatum X.dualChild.qFibreChildDatum
    (crossingBaseCover Y.destination)

/-- The corresponding heterogeneous paper atom. -/
abbrev qFreshNextActiveSourceAtom
    (Y : DoublyBufferedQFreshCrossingDestination H) : ActualFactorDatum :=
  badParentActiveFineSourceAtom X.dualChild.qFibreChildDatum
    (crossingBaseCover Y.destination)

/-- Exact q-fresh Def212 readiness makes the next crossing cover active on
every index of the selected child datum. -/
theorem nextCrossingBaseCover_activeFine_eq_univ
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    (crossingBaseCover Y.destination).activeFine = Finset.univ := by
  rw [(crossingBaseCover Y.destination).activeFine_eq_refined]
  exact H.readiness.qFreshExact.fine_refined_eq_univ

/-- Remove the one proof-only active-fine subtype layer.  This is an
equivalence, deliberately not an equality of heterogeneous factor atoms. -/
noncomputable def qFreshNextActiveIndexEquiv
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    {i // i ∈ (crossingBaseCover Y.destination).activeFine} ≃
      {i // i ∈ X.dualChild.qFibreSelected} where
  toFun i := i.1
  invFun i := ⟨i, by
    rw [nextCrossingBaseCover_activeFine_eq_univ H Y]
    exact Finset.mem_univ i⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := rfl

/-- Tubes are literally unchanged under the canonical active-fine index
equivalence. -/
@[simp] theorem qFreshNextActiveIndexEquiv_tube
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (i : {i // i ∈ (crossingBaseCover Y.destination).activeFine}) :
    (qFreshNextActiveSourceDatum Y).family.tubes i =
      X.dualChild.qFibreChildDatum.family.tubes
        (qFreshNextActiveIndexEquiv H Y i) :=
  rfl

/-- Shading carriers are literally unchanged under the same equivalence. -/
@[simp] theorem qFreshNextActiveIndexEquiv_shadingCarrier
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (i : {i // i ∈ (crossingBaseCover Y.destination).activeFine}) :
    (qFreshNextActiveSourceDatum Y).shading.carrier i =
      X.dualChild.qFibreChildDatum.shading.carrier
        (qFreshNextActiveIndexEquiv H Y i) :=
  rfl

/-- Geometric admissibility passes automatically to the literal active-fine
restriction. -/
theorem qFreshNextActiveSourceDatum_isAdmissible
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    (qFreshNextActiveSourceDatum Y).IsAdmissible :=
  Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
    X.dualChild.qFibreChild_admissible
      (crossingBaseCover Y.destination).activeFine

/-- The proof-only restriction leaves the actual radius unchanged. -/
@[simp] theorem qFreshNextActiveSourceAtom_radius_eq_fresh
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    (qFreshNextActiveSourceAtom Y).radius =
      (ActualFactorDatum.ofDatum
        X.dualChild.qFibreChildDatum).radius :=
  by
    simp only [qFreshNextActiveSourceAtom,
      badParentActiveFineSourceAtom_radius,
      ActualFactorDatum.ofDatum_radius]

/-- Full activity makes the restricted and full child cardinalities exactly
equal. -/
theorem qFreshNextActiveSourceAtom_card_eq_fresh
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    (qFreshNextActiveSourceAtom Y).card =
      (ActualFactorDatum.ofDatum X.dualChild.qFibreChildDatum).card := by
  simp only [qFreshNextActiveSourceAtom,
    badParentActiveFineSourceAtom_card,
    ActualFactorDatum.ofDatum_card, Fintype.card_coe]
  rw [nextCrossingBaseCover_activeFine_eq_univ H Y]
  simp only [Finset.card_univ]
  exact Fintype.card_coe _

/-! ## Readiness-aligned local next state -/

/-- The unchanged prefix for the next paper step consists of the old left
factors followed by the already produced coarse child. -/
def qFreshNextSourceLeftFactors : List ActualFactorDatum :=
  R.left ++ [badParentCoarseAtom
    (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Ysource)
    (crossingBaseCover W)]

/-- Its readiness is inherited literally from the previous paper step. -/
def qFreshNextSourceLeftReadiness
    (P : SourceDef212PaperStepReadiness X) :
    PaperFactorReadinessList (qFreshNextSourceLeftFactors
      (Csource := Csource) (Ysource := Ysource) (W := W) (R := R)) :=
  PaperFactorReadinessList.append P.leftReadiness
    (.cons P.coarseAtomReadiness .nil)

/-- Build the exact next source state once readiness for the single actual
active-fine atom is supplied.  All other readiness is inherited from `P`. -/
def qFreshNextActiveSourceState
    (P : SourceDef212PaperStepReadiness X)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (nextActiveReadiness : PaperFactorAtomReadiness
      (qFreshNextActiveSourceAtom Y)) : PaperFactorState :=
  PaperFactorState.ofFactors
    (badParentSourceFactorList X.dualChild.qFibreChildDatum
      (qFreshNextSourceLeftFactors
        (Csource := Csource) (Ysource := Ysource) (W := W) (R := R))
      R.right (crossingBaseCover Y.destination))
    (PaperFactorReadinessList.append
      (qFreshNextSourceLeftReadiness P)
      (.cons nextActiveReadiness P.rightReadiness))

/-- Replacing the full fresh atom by its fully active view preserves the
literal factor-radius product. -/
theorem successor_radiusProduct_eq_nextActiveSource
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (P : SourceDef212PaperStepReadiness X)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (nextActiveReadiness : PaperFactorAtomReadiness
      (qFreshNextActiveSourceAtom Y)) :
    factorRadiusProduct
        P.toSameObjectCrossingPaperStep.paperTransition.successor.factors =
      factorRadiusProduct
        (qFreshNextActiveSourceState P Y nextActiveReadiness).factors := by
  rw [P.toSameObjectCrossingPaperStep.paperTransition.successor_factors_eq]
  simp only [qFreshNextActiveSourceState,
    PaperFactorState.ofFactors_factors, badParentSuccessorFactorList,
    badParentSourceFactorList, qFreshNextSourceLeftFactors,
    Family8ParentwiseBadParentMassAwareFactorListStateV2.ParentwiseBadParentMassAwareFactorListState.successorFactors,
    SourceDef212PaperStepReadiness.toSameObjectCrossingPaperStep,
    SameObjectCrossingPaperStep.ofReadiness,
    SourceDef212CrossingIntegratedSuccessor.toParentwiseCrossingIntegratedSuccessor,
    SourceDef212CrossingSuccessorReadiness.toParentwiseCrossingSuccessorReadiness,
    factorRadiusProduct_append, factorRadiusProduct_cons,
    factorRadiusProduct_nil, mul_one,
    badParentActiveFineSourceAtom_radius, badParentCoarseAtom_radius,
    badParentFreshChildAtom_radius]
  ac_rfl

/-- The same local replacement also preserves the literal factor-cardinality
product exactly; no loss-one hypothesis is inserted. -/
theorem successor_cardProduct_eq_nextActiveSource
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (P : SourceDef212PaperStepReadiness X)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (nextActiveReadiness : PaperFactorAtomReadiness
      (qFreshNextActiveSourceAtom Y)) :
    factorCardProduct
        P.toSameObjectCrossingPaperStep.paperTransition.successor.factors =
      factorCardProduct
        (qFreshNextActiveSourceState P Y nextActiveReadiness).factors := by
  rw [P.toSameObjectCrossingPaperStep.paperTransition.successor_factors_eq]
  simp only [qFreshNextActiveSourceState,
    PaperFactorState.ofFactors_factors, badParentSuccessorFactorList,
    badParentSourceFactorList, qFreshNextSourceLeftFactors,
    Family8ParentwiseBadParentMassAwareFactorListStateV2.ParentwiseBadParentMassAwareFactorListState.successorFactors,
    SourceDef212PaperStepReadiness.toSameObjectCrossingPaperStep,
    SameObjectCrossingPaperStep.ofReadiness,
    SourceDef212CrossingIntegratedSuccessor.toParentwiseCrossingIntegratedSuccessor,
    SourceDef212CrossingSuccessorReadiness.toParentwiseCrossingSuccessorReadiness,
    factorCardProduct, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  rw [qFreshNextActiveSourceAtom_card_eq_fresh H Y]
  simp only [badParentCoarseAtom_card, badParentFreshChildAtom_card]
  have hfresh :
      (ActualFactorDatum.ofDatum X.dualChild.qFibreChildDatum).card =
        X.dualChild.qFibreSelected.card := by
    change Fintype.card {i // i ∈ X.dualChild.qFibreSelected} =
      X.dualChild.qFibreSelected.card
    exact Fintype.card_coe _
  rw [hfresh]
  simp only [Family8ParentwiseBadParentDualChildOrchestrationCertificateV1.ParentwiseBadParentDualChildCertificate.qFibreSelected]
  ac_rfl

#print axioms nextCrossingBaseCover_activeFine_eq_univ
#print axioms qFreshNextActiveIndexEquiv
#print axioms qFreshNextActiveIndexEquiv_tube
#print axioms qFreshNextActiveIndexEquiv_shadingCarrier
#print axioms qFreshNextActiveSourceDatum_isAdmissible
#print axioms qFreshNextActiveSourceAtom_radius_eq_fresh
#print axioms qFreshNextActiveSourceAtom_card_eq_fresh
#print axioms qFreshNextActiveSourceState
#print axioms successor_radiusProduct_eq_nextActiveSource
#print axioms successor_cardProduct_eq_nextActiveSource

end
end Family8QFreshNextActiveFinePaperStateTransportV1

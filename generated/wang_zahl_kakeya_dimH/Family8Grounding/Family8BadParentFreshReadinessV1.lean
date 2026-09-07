import Family8Grounding.Family8ContractedJohnEighthProxyCarrierNestingV1
import Family8Grounding.Family8ExactDef212CompositionalParentsV1
import Family8Grounding.Family8PaperFactorStateV1

/-!
# Honest recursive readiness for one bad-parent fresh atom

The source Exact Definition 2.12 package automatically supplies coherent
ancestor preservation for every index retained by the fresh selector.  The
genuinely new geometric obligation is kept explicit: normalized
contracted-John proxy tubes must nest whenever their source tubes nest below
the selected root.  A coherent cover and an Exact Definition 2.12 package
for the actual fresh datum are likewise explicit fields.

No identity-radius cover is constructed in this file.  Once the geometric
selected/affine proxy hierarchy producer supplies these fields, the final
connector yields `PaperFactorAtomReadiness` for the literal fresh atom.
-/

open Set
open scoped ENNReal NNReal

namespace Family8BadParentFreshReadinessV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnEighthProxyCarrierNestingV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8ExactDef212CompositionalParentsV1
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8TubeJohnUnitRescalingGeometryLeOneV7
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

variable {delta tau rho : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {source : UniformTubeFamily delta sourceIndex}

/-- The literal source interval cover at the bad parent. -/
abbrev badParentSourceIntervalCover
    (C : CoherentStickyMultiscaleCover source)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1) :=
  C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne

/-- The exact fresh successor datum whose recursive readiness is recorded. -/
abbrev badParentFreshDatum
    (C : CoherentStickyMultiscaleCover source)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (Y : Shading
      (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.bodyFamily)
    (hrho : 0 < rho)
    (q : {q // q ∈ (badParentSourceIntervalCover C tau rho
      hdeltaTau hTauRho hRhoOne).activeCoarse})
    (selected : Finset {i // i ∈
      (badParentSourceIntervalCover C tau rho
        hdeltaTau hTauRho hRhoOne).fiber q.1}) :=
  badParentFreshSuccessorDatum
    (badParentSourceIntervalCover C tau rho
      hdeltaTau hTauRho hRhoOne)
    Y hrho hRhoOne q selected

/-- Package the literal fresh successor as the heterogeneous atom consumed
by `PaperFactorState`. -/
def badParentFreshAtom
    (C : CoherentStickyMultiscaleCover source)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (Y : Shading
      (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.bodyFamily)
    (hrho : 0 < rho)
    (q : {q // q ∈ (badParentSourceIntervalCover C tau rho
      hdeltaTau hTauRho hRhoOne).activeCoarse})
    (selected : Finset {i // i ∈
      (badParentSourceIntervalCover C tau rho
        hdeltaTau hTauRho hRhoOne).fiber q.1}) :
    ActualFactorDatum :=
  ActualFactorDatum.ofDatum
    (badParentFreshDatum C tau rho hdeltaTau hTauRho hRhoOne
      Y hrho q selected)

/-- The exact full carrier-nesting obligation for the common selected-root
John map.  This is stronger than image-level shading transport: it requires
the actual normalized proxy tube of every source child to lie in the actual
normalized proxy tube of its source ancestor. -/
def BadParentFreshProxyCarrierNesting
    (C : CoherentStickyMultiscaleCover source)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (hrho : 0 < rho)
    (q : {q // q ∈ (badParentSourceIntervalCover C tau rho
      hdeltaTau hTauRho hRhoOne).activeCoarse}) : Prop :=
  let I := badParentSourceIntervalCover C tau rho
    hdeltaTau hTauRho hRhoOne
  let P := I.coarse.tubes q.1
  let w := StickyScaleCover.tubeJohnWitnessLeOne I hrho hRhoOne q
  forall {childScale ancestorScale : NNReal}
      (T : Tube childScale) (U : Tube ancestorScale),
    T.carrier ⊆ U.carrier ->
    U.carrier ⊆ P.carrier ->
    IsContractedJohnEighthProxyParent P hrho w T U

/-- The source-side recursive invariant for the exact nested subtype used by
the fresh successor datum. -/
def BadParentFreshSourceAncestorPreservation
    (C : CoherentStickyMultiscaleCover source)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (q : {q // q ∈ (badParentSourceIntervalCover C tau rho
      hdeltaTau hTauRho hRhoOne).activeCoarse})
    (selected : Finset {i // i ∈
      (badParentSourceIntervalCover C tau rho
        hdeltaTau hTauRho hRhoOne).fiber q.1}) : Prop :=
  forall (sigma : NNReal) (hTauSigma : tau <= sigma)
      (hSigmaRho : sigma <= rho) (x : {j // j ∈ selected}),
    C.parent sigma rho (hdeltaTau.trans hTauSigma)
        hSigmaRho hRhoOne
        (C.parent tau sigma hdeltaTau hTauSigma
          (hSigmaRho.trans hRhoOne) x.1.1) = q.1

/-- Honest recursive readiness for the literal actual fresh atom.

`fresh_proxy_carrier_nesting`, `fresh_proxy_coherentCover`, and
`fresh_exactDef212` are deliberately supplied fields.  They are the output
expected from the selected/affine proxy hierarchy producer; this structure
does not synthesize them from an identity cover. -/
structure BadParentFreshReadiness
    (C : CoherentStickyMultiscaleCover source)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (Y : Shading
      (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.bodyFamily)
    (hrho : 0 < rho)
    (q : {q // q ∈ (badParentSourceIntervalCover C tau rho
      hdeltaTau hTauRho hRhoOne).activeCoarse})
    (selected : Finset {i // i ∈
      (badParentSourceIntervalCover C tau rho
        hdeltaTau hTauRho hRhoOne).fiber q.1}) where
  source_def212Constant : NNReal
  source_exactDef212 : ExactScaleDef212Inputs
    C.base source_def212Constant
  fresh_admissible :
    (badParentFreshDatum C tau rho hdeltaTau hTauRho hRhoOne
      Y hrho q selected).IsAdmissible
  fresh_proxy_carrier_nesting :
    BadParentFreshProxyCarrierNesting C tau rho hdeltaTau
      hTauRho hRhoOne hrho q
  fresh_proxy_coherentCover : CoherentStickyMultiscaleCover
    (badParentFreshDatum C tau rho hdeltaTau hTauRho hRhoOne
      Y hrho q selected).family
  fresh_def212Constant : NNReal
  fresh_exactDef212 : ExactScaleDef212Inputs
    fresh_proxy_coherentCover.base fresh_def212Constant

namespace BadParentFreshReadiness

variable {C : CoherentStickyMultiscaleCover source}
  {hdeltaTau : delta <= tau} {hTauRho : tau <= rho}
  {hRhoOne : rho <= 1}
  {Y : Shading
    (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).coarse.bodyFamily}
  {hrho : 0 < rho}
  {q : {q // q ∈ (badParentSourceIntervalCover C tau rho
    hdeltaTau hTauRho hRhoOne).activeCoarse}}
  {selected : Finset {i // i ∈
    (badParentSourceIntervalCover C tau rho
      hdeltaTau hTauRho hRhoOne).fiber q.1}}

/-- Source ancestor preservation is generated automatically from the source
Exact Definition 2.12 field; it is not an additional readiness hypothesis. -/
theorem source_ancestor_preservation
    (R : BadParentFreshReadiness C tau rho hdeltaTau hTauRho
      hRhoOne Y hrho q selected) :
    BadParentFreshSourceAncestorPreservation C tau rho hdeltaTau
      hTauRho hRhoOne q selected := by
  intro sigma hTauSigma hSigmaRho x
  exact
    badParentFresh_index_intermediate_source_parent_eq_of_exactScaleDef212Inputs
      C R.source_exactDef212 tau rho hdeltaTau hTauRho hRhoOne
      sigma hTauSigma hSigmaRho q selected x

/-- The record connects definitionally to readiness for the exact literal
fresh atom stored in a `PaperFactorState`. -/
def toPaperFactorAtomReadiness
    (R : BadParentFreshReadiness C tau rho hdeltaTau hTauRho
      hRhoOne Y hrho q selected) :
    PaperFactorAtomReadiness
      (badParentFreshAtom C tau rho hdeltaTau hTauRho hRhoOne
        Y hrho q selected) where
  admissible := R.fresh_admissible
  coherentCover := R.fresh_proxy_coherentCover
  def212Constant := R.fresh_def212Constant
  exactDef212 := R.fresh_exactDef212

/-- Prepend the exact fresh atom readiness to an already aligned readiness
list. -/
def consPaperFactorReadiness
    (R : BadParentFreshReadiness C tau rho hdeltaTau hTauRho
      hRhoOne Y hrho q selected)
    {tail : List ActualFactorDatum}
    (tailReadiness : PaperFactorReadinessList tail) :
    PaperFactorReadinessList
      (badParentFreshAtom C tau rho hdeltaTau hTauRho hRhoOne
        Y hrho q selected :: tail) :=
  .cons R.toPaperFactorAtomReadiness tailReadiness

/-- The singleton paper state for the actual fresh atom. -/
def toSingletonPaperFactorState
    (R : BadParentFreshReadiness C tau rho hdeltaTau hTauRho
      hRhoOne Y hrho q selected) : PaperFactorState :=
  PaperFactorState.ofFactors
    [badParentFreshAtom C tau rho hdeltaTau hTauRho hRhoOne
      Y hrho q selected]
    (.cons R.toPaperFactorAtomReadiness .nil)

@[simp]
theorem toSingletonPaperFactorState_factors
    (R : BadParentFreshReadiness C tau rho hdeltaTau hTauRho
      hRhoOne Y hrho q selected) :
    R.toSingletonPaperFactorState.factors =
      [badParentFreshAtom C tau rho hdeltaTau hTauRho hRhoOne
        Y hrho q selected] :=
  rfl

end BadParentFreshReadiness

#print axioms badParentFreshAtom
#print axioms BadParentFreshProxyCarrierNesting
#print axioms BadParentFreshSourceAncestorPreservation
#print axioms BadParentFreshReadiness
#print axioms BadParentFreshReadiness.source_ancestor_preservation
#print axioms BadParentFreshReadiness.toPaperFactorAtomReadiness
#print axioms BadParentFreshReadiness.consPaperFactorReadiness
#print axioms BadParentFreshReadiness.toSingletonPaperFactorState

end
end Family8BadParentFreshReadinessV1

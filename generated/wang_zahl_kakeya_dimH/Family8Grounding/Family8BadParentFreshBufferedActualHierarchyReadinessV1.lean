import Family8Grounding.Family8BadParentFreshReadinessV1
import Family8Grounding.Family8ContractedJohnEighthProxyAxisGapBufferPowerV1
import Family8Grounding.Family8ContractedJohnEighthProxySelectedAncestorAxisGapV1
import Mathlib.Tactic

/-!
# Buffered actual-hierarchy readiness for one bad-parent fresh atom

The selected-ancestor geometry produces containment in a genuine buffered
proxy parent, rather than in the unbuffered proxy.  This module records that
honest target and connects it to the exact fresh datum.  Source Exact
Definition 2.12 automatically keeps every selected ancestor below the same
literal `q`; the only remaining inputs are scalar buffer budgets, the actual
fresh coherent cover and its Exact Definition 2.12 package, and the equality
identifying that cover's parent with the real buffered source proxy.

No identity cover, re-picked parent, or hidden hierarchy callback occurs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8BadParentFreshBufferedActualHierarchyReadinessV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BadParentFreshReadinessV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnEighthProxyCarrierMonoV1
open Family8ContractedJohnEighthProxyCarrierNestingV1
open Family8ContractedJohnEighthProxyAxisGapBufferPowerV1
open Family8ContractedJohnEighthProxySelectedAncestorAxisGapV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8ExactDef212CompositionalParentsV1
open Family8PaperFactorStateV1
open Family8TubeJohnUnitRescalingGeometryLeOneV7
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta tau rho : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {source : UniformTubeFamily delta sourceIndex}

/-- The actual source ancestor, at scale `sigma`, of one retained fresh
index.  Its index is the original coherent parent of the same selected
`tau`-tube. -/
def badParentFreshSelectedSourceAncestorTube
    (C : CoherentStickyMultiscaleCover source)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (q : {q // q ∈ (badParentSourceIntervalCover C tau rho
      hdeltaTau hTauRho hRhoOne).activeCoarse})
    (selected : Finset {i // i ∈
      (badParentSourceIntervalCover C tau rho
        hdeltaTau hTauRho hRhoOne).fiber q.1})
    (sigma : NNReal) (hTauSigma : tau <= sigma)
    (hSigmaRho : sigma <= rho) (x : {j // j ∈ selected}) : Tube sigma :=
  let A := C.base.cover sigma (hdeltaTau.trans hTauSigma)
    (hSigmaRho.trans hRhoOne)
  A.coarse.tubes
    (C.parent tau sigma hdeltaTau hTauSigma
      (hSigmaRho.trans hRhoOne) x.1.1)

/-- The genuine buffered proxy scale attached to source scale `sigma`. -/
def badParentFreshBufferedProxyScale
    (sigma rho buffer : NNReal) : NNReal :=
  contractedJohnProxyRadius sigma rho / 8 + buffer

/-- The literal fresh radius is below every later buffered proxy scale. -/
theorem badParentFreshRadius_le_bufferedProxyScale
    {tau sigma rho : NNReal} (hTauSigma : tau <= sigma)
    (buffer : NNReal) :
    contractedJohnProxyRadius tau rho / 8 <=
      badParentFreshBufferedProxyScale sigma rho buffer := by
  calc
    contractedJohnProxyRadius tau rho / 8 <=
        contractedJohnProxyRadius sigma rho / 8 :=
      contractedJohnEighthProxyRadius_mono hTauSigma
    _ <= contractedJohnProxyRadius sigma rho / 8 + buffer :=
      le_add_right le_rfl

/-- The exact fresh datum uses the genuine normalized proxy tube of the
literal selected source index. -/
@[simp]
theorem badParentFreshDatum_family_tubes
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
        hdeltaTau hTauRho hRhoOne).fiber q.1})
    (x : {j // j ∈ selected}) :
    (badParentFreshDatum C tau rho hdeltaTau hTauRho hRhoOne
      Y hrho q selected).family.tubes x =
      contractedJohnEighthProxyTube
        ((badParentSourceIntervalCover C tau rho
          hdeltaTau hTauRho hRhoOne).coarse.tubes q.1) hrho
        (StickyScaleCover.tubeJohnWitnessLeOne
          (badParentSourceIntervalCover C tau rho
            hdeltaTau hTauRho hRhoOne) hrho hRhoOne q)
        ((C.base.cover tau hdeltaTau
          (hTauRho.trans hRhoOne)).coarse.tubes x.1.1) :=
  rfl

/-- Exact Definition 2.12 plus the ratio-power and small-scale budgets produces
the complete actual `1 / 8`-buffered step for the same selected index and same
`q`.  The axis-gap comparison is derived, not supplied as an input. -/
theorem badParentFreshSelectedOneEighthBufferedStep_of_sourceExact
    (C : CoherentStickyMultiscaleCover source)
    {sourceK : NNReal} (H : ExactScaleDef212Inputs C.base sourceK)
    {epsilon : Real} (hdeltaPos : 0 < delta) (hepsilon : 0 < epsilon)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (hrho : 0 < rho)
    (q : {q // q ∈ (badParentSourceIntervalCover C tau rho
      hdeltaTau hTauRho hRhoOne).activeCoarse})
    (selected : Finset {i // i ∈
      (badParentSourceIntervalCover C tau rho
        hdeltaTau hTauRho hRhoOne).fiber q.1})
    (sigma : NNReal) (hTauSigma : tau <= sigma)
    (hSigmaRho : sigma <= rho) (x : {j // j ∈ selected})
    (hratioPower : sigma / rho <= delta ^ (epsilon ^ 2))
    (hsmall : delta <=
      contractedJohnEighthSelectedAncestorAxisGapThreshold epsilon) :
    ContractedJohnEighthSelectedAncestorBufferedStep
      ((badParentSourceIntervalCover C tau rho
        hdeltaTau hTauRho hRhoOne).coarse.tubes q.1)
      hrho hRhoOne
      (StickyScaleCover.tubeJohnWitnessLeOne
        (badParentSourceIntervalCover C tau rho
          hdeltaTau hTauRho hRhoOne) hrho hRhoOne q)
      ((C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.tubes x.1.1)
      (badParentFreshSelectedSourceAncestorTube C tau rho hdeltaTau
        hTauRho hRhoOne q selected sigma hTauSigma hSigmaRho x)
      contractedJohnEighthSelectedAncestorOneEighthBuffer := by
  let T := C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)
  let A := C.base.cover sigma (hdeltaTau.trans hTauSigma)
    (hSigmaRho.trans hRhoOne)
  let R := C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne
  let I := badParentSourceIntervalCover C tau rho
    hdeltaTau hTauRho hRhoOne
  have hxFiber : x.1.1 ∈ I.fiber q.1 := x.1.2
  have hxData := (I.mem_fiber x.1.1 q.1).1 hxFiber
  have hxT : x.1.1 ∈ T.activeCoarse := hxData.1
  have hTU :
      (T.coarse.tubes x.1.1).carrier ⊆
        (A.coarse.tubes
          (C.parent tau sigma hdeltaTau hTauSigma
            (hSigmaRho.trans hRhoOne) x.1.1)).carrier := by
    simpa only [T, A] using
      C.carrier_subset tau sigma hdeltaTau hTauSigma
        (hSigmaRho.trans hRhoOne) x.1.1 hxT
  have hAncestorActive :
      C.parent tau sigma hdeltaTau hTauSigma
        (hSigmaRho.trans hRhoOne) x.1.1 ∈ A.activeCoarse := by
    simpa only [T, A] using
      C.parent_mem tau sigma hdeltaTau hTauSigma
        (hSigmaRho.trans hRhoOne) x.1.1 hxT
  have hSameRoot :
      C.parent sigma rho (hdeltaTau.trans hTauSigma)
          hSigmaRho hRhoOne
          (C.parent tau sigma hdeltaTau hTauSigma
            (hSigmaRho.trans hRhoOne) x.1.1) = q.1 :=
    intermediate_parent_remains_in_selected_subtree_of_exactScaleDef212Inputs
      C H tau rho hdeltaTau hTauRho hRhoOne sigma hTauSigma
        hSigmaRho x.1.1 hxT q.1 hxData.2
  have hUP :=
    C.carrier_subset sigma rho (hdeltaTau.trans hTauSigma)
      hSigmaRho hRhoOne
      (C.parent tau sigma hdeltaTau hTauSigma
        (hSigmaRho.trans hRhoOne) x.1.1) hAncestorActive
  change
    (A.coarse.tubes
      (C.parent tau sigma hdeltaTau hTauSigma
        (hSigmaRho.trans hRhoOne) x.1.1)).carrier ⊆
      (R.coarse.tubes
        (C.parent sigma rho (hdeltaTau.trans hTauSigma)
          hSigmaRho hRhoOne
          (C.parent tau sigma hdeltaTau hTauSigma
            (hSigmaRho.trans hRhoOne) x.1.1))).carrier at hUP
  rw [hSameRoot] at hUP
  exact contractedJohnEighthSelectedAncestorBufferedStep_of_source
    (R.coarse.tubes q.1) hrho hRhoOne
    (StickyScaleCover.tubeJohnWitnessLeOne I hrho hRhoOne q)
    (T.coarse.tubes x.1.1)
    (A.coarse.tubes
      (C.parent tau sigma hdeltaTau hTauSigma
        (hSigmaRho.trans hRhoOne) x.1.1))
    contractedJohnEighthSelectedAncestorOneEighthBuffer
    hTauSigma hSigmaRho hTU hUP
    (contractedJohnEighthSelectedAncestorAxisGap_le_oneEighthBuffer
      hdeltaPos hrho hepsilon hratioPower hsmall)

/-- Honest buffered recursive readiness for the exact fresh atom.  The
actual coherent cover remains object-level input, and its parent-realization
field prevents an unrelated hierarchy from being substituted. -/
structure BadParentFreshBufferedActualHierarchyReadiness
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
        hdeltaTau hTauRho hRhoOne).fiber q.1})
    (epsilon : Real) (hdeltaPos : 0 < delta)
    (hepsilon : 0 < epsilon) where
  source_def212Constant : NNReal
  source_exactDef212 : ExactScaleDef212Inputs
    C.base source_def212Constant
  fresh_admissible :
    (badParentFreshDatum C tau rho hdeltaTau hTauRho hRhoOne
      Y hrho q selected).IsAdmissible
  fresh_coherentCover : CoherentStickyMultiscaleCover
    (badParentFreshDatum C tau rho hdeltaTau hTauRho hRhoOne
      Y hrho q selected).family
  fresh_def212Constant : NNReal
  fresh_exactDef212 : ExactScaleDef212Inputs
    fresh_coherentCover.base fresh_def212Constant
  ratioPower_le : forall (sigma : NNReal)
      (_hTauSigma : tau <= sigma) (_hSigmaRho : sigma <= rho),
    sigma / rho <= delta ^ (epsilon ^ 2)
  small_delta : delta <=
    contractedJohnEighthSelectedAncestorAxisGapThreshold epsilon
  bufferedScale_le_one : forall (sigma : NNReal)
      (_hTauSigma : tau <= sigma) (_hSigmaRho : sigma <= rho),
    badParentFreshBufferedProxyScale sigma rho
      contractedJohnEighthSelectedAncestorOneEighthBuffer <= 1
  parent_realizes_buffered_source : forall (sigma : NNReal)
      (hTauSigma : tau <= sigma) (hSigmaRho : sigma <= rho)
      (x : {j // j ∈ selected}),
    let A := fresh_coherentCover.base.cover
      (badParentFreshBufferedProxyScale sigma rho
        contractedJohnEighthSelectedAncestorOneEighthBuffer)
      (badParentFreshRadius_le_bufferedProxyScale hTauSigma
        contractedJohnEighthSelectedAncestorOneEighthBuffer)
      (bufferedScale_le_one sigma hTauSigma hSigmaRho)
    A.coarse.tubes (A.parent x) =
      contractedJohnEighthProxyContainingTube
        ((badParentSourceIntervalCover C tau rho
          hdeltaTau hTauRho hRhoOne).coarse.tubes q.1) hrho
        (StickyScaleCover.tubeJohnWitnessLeOne
          (badParentSourceIntervalCover C tau rho
            hdeltaTau hTauRho hRhoOne) hrho hRhoOne q)
        (badParentFreshSelectedSourceAncestorTube C tau rho hdeltaTau
          hTauRho hRhoOne q selected sigma hTauSigma hSigmaRho x)
        contractedJohnEighthSelectedAncestorOneEighthBuffer

namespace BadParentFreshBufferedActualHierarchyReadiness

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
  {epsilon : Real} {hdeltaPos : 0 < delta} {hepsilon : 0 < epsilon}

/-- Every selected source ancestor has the complete automatically produced
buffered actual-proxy hierarchy step. -/
theorem buffered_step
    (R : BadParentFreshBufferedActualHierarchyReadiness C tau rho
      hdeltaTau hTauRho hRhoOne Y hrho q selected
      epsilon hdeltaPos hepsilon)
    (sigma : NNReal) (hTauSigma : tau <= sigma)
    (hSigmaRho : sigma <= rho) (x : {j // j ∈ selected}) :
    ContractedJohnEighthSelectedAncestorBufferedStep
      ((badParentSourceIntervalCover C tau rho
        hdeltaTau hTauRho hRhoOne).coarse.tubes q.1)
      hrho hRhoOne
      (StickyScaleCover.tubeJohnWitnessLeOne
        (badParentSourceIntervalCover C tau rho
          hdeltaTau hTauRho hRhoOne) hrho hRhoOne q)
      ((C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.tubes x.1.1)
      (badParentFreshSelectedSourceAncestorTube C tau rho hdeltaTau
        hTauRho hRhoOne q selected sigma hTauSigma hSigmaRho x)
      contractedJohnEighthSelectedAncestorOneEighthBuffer :=
  badParentFreshSelectedOneEighthBufferedStep_of_sourceExact C
    R.source_exactDef212 hdeltaPos hepsilon tau rho hdeltaTau hTauRho
    hRhoOne hrho q selected sigma hTauSigma hSigmaRho x
    (R.ratioPower_le sigma hTauSigma hSigmaRho) R.small_delta

/-- The literal fresh tube is contained in the actual coherent-cover parent
identified with its genuine buffered selected source ancestor. -/
theorem fine_subset_realized_buffered_parent
    (R : BadParentFreshBufferedActualHierarchyReadiness C tau rho
      hdeltaTau hTauRho hRhoOne Y hrho q selected
      epsilon hdeltaPos hepsilon)
    (sigma : NNReal) (hTauSigma : tau <= sigma)
    (hSigmaRho : sigma <= rho) (x : {j // j ∈ selected}) :
    let A := R.fresh_coherentCover.base.cover
      (badParentFreshBufferedProxyScale sigma rho
        contractedJohnEighthSelectedAncestorOneEighthBuffer)
      (badParentFreshRadius_le_bufferedProxyScale hTauSigma
        contractedJohnEighthSelectedAncestorOneEighthBuffer)
      (R.bufferedScale_le_one sigma hTauSigma hSigmaRho)
    ((badParentFreshDatum C tau rho hdeltaTau hTauRho hRhoOne
      Y hrho q selected).family.tubes x).carrier ⊆
        (A.coarse.tubes (A.parent x)).carrier := by
  dsimp only
  rw [badParentFreshDatum_family_tubes]
  rw [R.parent_realizes_buffered_source sigma hTauSigma hSigmaRho x]
  exact
    (R.buffered_step sigma hTauSigma hSigmaRho x).actual_proxy_subset_buffered_parent

/-- Paper-factor readiness consumes exactly admissibility, the actual
coherent cover, and its Exact Definition 2.12 package. -/
def toPaperFactorAtomReadiness
    (R : BadParentFreshBufferedActualHierarchyReadiness C tau rho
      hdeltaTau hTauRho hRhoOne Y hrho q selected
      epsilon hdeltaPos hepsilon) :
    PaperFactorAtomReadiness
      (badParentFreshAtom C tau rho hdeltaTau hTauRho hRhoOne
        Y hrho q selected) where
  admissible := R.fresh_admissible
  coherentCover := R.fresh_coherentCover
  def212Constant := R.fresh_def212Constant
  exactDef212 := R.fresh_exactDef212

end BadParentFreshBufferedActualHierarchyReadiness

#print axioms badParentFreshSelectedSourceAncestorTube
#print axioms badParentFreshBufferedProxyScale
#print axioms badParentFreshRadius_le_bufferedProxyScale
#print axioms badParentFreshDatum_family_tubes
#print axioms badParentFreshSelectedOneEighthBufferedStep_of_sourceExact
#print axioms BadParentFreshBufferedActualHierarchyReadiness
#print axioms BadParentFreshBufferedActualHierarchyReadiness.buffered_step
#print axioms
  BadParentFreshBufferedActualHierarchyReadiness.fine_subset_realized_buffered_parent
#print axioms
  BadParentFreshBufferedActualHierarchyReadiness.toPaperFactorAtomReadiness

end
end Family8BadParentFreshBufferedActualHierarchyReadinessV1

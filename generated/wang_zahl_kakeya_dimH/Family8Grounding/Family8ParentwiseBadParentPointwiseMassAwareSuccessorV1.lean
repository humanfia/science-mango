import Family8Grounding.Family8NormalizedLongIntervalPointwiseFrostmanInheritanceV1
import Family8Grounding.Family8ParentwiseBadParentMassAwareFactorListStateV2
import Mathlib.Tactic

/-!
# Same-parent pointwise mass-aware bad-factor successor

At a buffered radius `rho`, the paper's factor step uses the literal base
cover

`R = C.base.cover rho`

and one active parent `q` of that cover.  A strict source bound on this same
`q` constructs the mass-aware factor-list successor.  Independently, the
existing interval mass comparison transfers the base `q`-bound to the
literal interval cover

`I = C.intervalScaleCover tau rho`.

The theorem below performs both operations on the same dependent `q`.  It
does not take a maximum over other parents, rerun a selector, or identify the
selected `q`-fibre child with the separate active-parent child at radius
`rho / 8`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentPointwiseMassAwareSuccessorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedLongIntervalPointwiseFrostmanInheritanceV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta tau rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- A base-cover bound strictly below the stopping threshold produces the
same-`q` mass-aware successor state, while the same base bound and the
literal two-sided parent-mass comparison give the pointwise interval-child
upper bound.

`massLower` and `massUpper` belong only to the interval inheritance loss;
`stopLower` is the independent bad-factor stopping threshold. -/
theorem exists_parentwiseBadParentPointwiseMassAwareSuccessor
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (left right : List ActualFactorDatum)
    (hdelta : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho)
    (hRhoOne : rho <= 1)
    (hrho : 0 < rho)
    {baseError massLower massUpper stopLower factorC : ENNReal}
    (hmassLower0 : massLower ≠ 0)
    (hmassLowerTop : massLower ≠ ∞)
    (H : IntervalParentMassComparison C tau hdeltaTau
      (hTauRho.trans hRhoOne) massLower massUpper)
    (q : {q // q ∈
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).activeCoarse})
    (hbase : parentNormalizedFiberCFAt
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne) q <=
        baseError)
    (hbaseStrict : baseError < stopLower)
    (hstopTop : stopLower ≠ ∞)
    (huniform : IsCUniform
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne) factorC) :
    Nonempty (ParentwiseBadParentMassAwareFactorListState
      D (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne)
        left right hrho hRhoOne q stopLower factorC) /\
      parentNormalizedFiberCFAt
          (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne) q <
        stopLower /\
      parentNormalizedFiberCFAt
          (C.intervalScaleCover
            tau rho hdeltaTau hTauRho hRhoOne) q <=
        baseError * massUpper * massLower⁻¹ := by
  let R := C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne
  have hbad : parentNormalizedFiberCFAt R q < stopLower :=
    hbase.trans_lt hbaseStrict
  obtain ⟨X⟩ :=
    exists_parentwiseBadParentMassAwareFactorListState
      D R left right hdelta hdeltaHalf hrho hRhoOne
        (hdeltaTau.trans hTauRho) q hstopTop hbad huniform
  have hUpper :
      parentNormalizedFiberCFAt
          (C.intervalScaleCover
            tau rho hdeltaTau hTauRho hRhoOne) q <=
        baseError * massUpper * massLower⁻¹ :=
    selectedUpperChild_cfAt_le
      C tau rho hdeltaTau (hTauRho.trans hRhoOne)
        hTauRho hRhoOne hdelta hmassLower0 hmassLowerTop H q hbase
  exact ⟨⟨X⟩, hbad, hUpper⟩

#print axioms exists_parentwiseBadParentPointwiseMassAwareSuccessor

end
end Family8ParentwiseBadParentPointwiseMassAwareSuccessorV1

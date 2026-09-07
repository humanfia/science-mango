import Family8Grounding.Family8StickyActiveCoarseFullDatumV1
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Family8Grounding.Family8StickyScaleCoverSelectedParentCFAtDichotomyV1
import Family8Grounding.Family8StickySelectedFiberLowCFFreshRetentionProducerV2
import Mathlib.Tactic

/-!
# A callback-free factor replacement at one literal bad parent

The parentwise stopping theorem returns an actual active parent `q` whose
normalized fibre concentration is below the current barrier.  The older
structural successor forgot that parent and instead split a cover-wide
maximum.  This file keeps the literal object:

* `badParentCoarseFactor S` is the genuine geometric factorization already
  carried by the Sticky cover;
* `badParentRescaledFibreDatum ... q` is the common John-affine rescaling of
  that exact fibre; and
* `exists_badParent_freshFactorReplacement` applies the existing normalized
  fresh selector to this same datum and returns its concrete admissibility,
  Frostman, cardinality, and shading-mass conclusions.

No successor callback and no numerical surrogate for `q` occurs here.  A
later recursive driver still needs a theorem transporting the entire
multiscale hierarchy on this restricted affine child to a new coherent
Sticky cover.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ParentwiseBadParentFactorReplacementV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickyScaleCoverSelectedParentCFAtDichotomyV1.StickyScaleCover
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open Family8StickySelectedFiberLowCFScalarEnvelopeV4
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The actual coarse factor inserted at a parentwise bad scale.  Its active
fine indices, active coarse indices, parent map, and containment are copied
from the literal Sticky cover. -/
def badParentCoarseFactor (S : StickyScaleCover fine rho) :
    ConvexFactorization fine.bodyFamily S.coarse.bodyFamily :=
  Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover.toConvexFactorization S

@[simp] theorem badParentCoarseFactor_fiber
    (S : StickyScaleCover fine rho) (q : Fin S.coarseCard) :
    (badParentCoarseFactor S).index.fiber q = S.fiber q := by
  rfl

/-- The coarse factor as a literal full-shaded actual datum.  This is the
outer object paired with the selected affine child; no admissibility is
silently asserted for it. -/
def badParentCoarseDatum (S : StickyScaleCover fine rho) :=
  Family8StickyActiveCoarseFullDatumV1.activeCoarseFullDatum S

/-- The exact `q`-fibre after the repository's common contracted-John affine
map and the canonical eighth normalization used by the fresh selector. -/
def badParentRescaledFibreDatum
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse}) :=
  eighthNormalizedDatum
    (stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne q)

/-- Restrict the exact affine child to the genuine fresh selected subtype. -/
def badParentFreshSuccessorDatum
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1}) :=
  restrictActualTubeDatum
    (badParentRescaledFibreDatum S Y hrho hrhoOne q) selected

/-- A strict parentwise normalized-CF crossing gives a Frostman certificate
on that same literal fibre. -/
theorem badParent_isFrostmanIn
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (q : {q // q ∈ S.activeCoarse}) {lower : ENNReal}
    (hbad : parentNormalizedFiberCFAt S q < lower) :
    IsFrostmanIn lower (S.fiberFamily q.1) (S.activeCoarseFamily q) := by
  rcases lower_le_cfAt_or_isFrostmanIn S hdelta q lower with
    hhigh | hlow
  · exact (not_le_of_gt hbad hhigh).elim
  · exact hlow

/-- One callback-free paper-style replacement step.  The output child is
formed from the exact bad parent `q`; its coarse factor remains
`badParentCoarseFactor S`, whose selected fibre is definitionally
`S.fiber q`. -/
theorem exists_badParent_freshFactorReplacement
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (q : {q // q ∈ S.activeCoarse})
    {lower : ENNReal} (hlowerTop : lower ≠ ∞)
    (hbad : parentNormalizedFiberCFAt S q < lower) :
    exists selected : Finset {i // i ∈ S.fiber q.1},
      selected.Nonempty /\
      (badParentFreshSuccessorDatum
        S Y hrho hrhoOne q selected).IsAdmissible /\
      selectedParentLowCFFreshLoss S hrho hrhoOne q lower ≠ ∞ /\
      IsFrostmanIn
        (lower *
          (16 * selectedParentLowCFFreshLoss S hrho hrhoOne q lower))
        (activeSubtypeFamily (S.fiberFamily q.1) selected)
        (S.activeCoarseFamily q) /\
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) <=
        stickyFiberContractedJohnSourceClosedLoss
            (selectedFiberLowCFCardEnvelope S q selected lower
              (selectedParentLowCFFreshLoss S hrho hrhoOne q lower)) *
          (selected.card : ENNReal) /\
      (badParentRescaledFibreDatum
        S Y hrho hrhoOne q).shading.shadingMass <=
        stickyFiberContractedJohnSourceClosedLoss
            (selectedFiberLowCFCardEnvelope S q selected lower
              (selectedParentLowCFFreshLoss S hrho hrhoOne q lower)) *
          (badParentFreshSuccessorDatum
            S Y hrho hrhoOne q selected).shading.shadingMass := by
  have hlow : IsFrostmanIn lower
      (S.fiberFamily q.1) (S.activeCoarseFamily q) :=
    badParent_isFrostmanIn S hdelta q hbad
  simpa only [badParentFreshSuccessorDatum,
    badParentRescaledFibreDatum] using
      (exists_lowCF_fresh_selected_cardEnvelope_retention
        S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho q hlowerTop hlow)

#print axioms badParentCoarseFactor
#print axioms badParentCoarseFactor_fiber
#print axioms badParentCoarseDatum
#print axioms badParentRescaledFibreDatum
#print axioms badParentFreshSuccessorDatum
#print axioms badParent_isFrostmanIn
#print axioms exists_badParent_freshFactorReplacement

end
end Family8ParentwiseBadParentFactorReplacementV1

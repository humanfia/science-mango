import Family8Grounding.Family8CanonicalBufferedFrozenOuterBaseScalarV1
import Family8Grounding.Family8FrozenOuterThirdBaseExponentChoiceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedFrozenOuterBaseScalarV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4
open Family8FrozenOuterThirdBaseExponentChoiceV1

noncomputable section

/-!
# Canonical frozen outer base scalar at an explicit Frostman exponent

The V1 connector retains the exact exponent budget.  Here that budget is
discharged by the explicit, datum-independent exponent choice.  No scale,
base scalar, or conclusion-valued premise remains.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem canonicalBuffered_fixedConflict_baseScalar_le_explicitExponent
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    {CKT : ENNReal} {etaKT absorbEta : Real}
    (hbeta : 0 < beta) (hetaKT : 0 ≤ etaKT)
    (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 ≤ CKT)
    (hCKT : CKT ≤ (delta : ENNReal) ^ (-etaKT))
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta ≤
      frozenOuterThirdKatzTaoBaseSmallDeltaThreshold absorbEta) :
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) *
        ((128 * CKT) * volume (unitBallBody : Set Space)) ≤
      (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^
          (-frozenOuterThirdBaseFrostmanExponent
            P W.stage etaKT absorbEta)) *
        (((Sseq.tau W.m ^
          (10 * P.eta W.stage / (P.epsilon * beta)) : NNReal) : ENNReal) /
            128) := by
  have hetaF : 0 ≤
      frozenOuterThirdBaseFrostmanExponent P W.stage etaKT absorbEta :=
    (frozenOuterThirdBaseFrostmanExponent_pos
      P W.stage hbeta hetaKT habsorbEta hepsilonHalf).le
  have hscaleGain : 0 ≤
      (1 - P.epsilon) *
          frozenOuterThirdBaseFrostmanExponent P W.stage etaKT absorbEta -
        (10 * P.eta W.stage / (P.epsilon * beta)) :=
    frozenOuterThirdBaseFrostmanExponent_scaleGain_nonneg
      P W.stage hetaKT habsorbEta hepsilonHalf
  have hbudget : 2 * etaKT + absorbEta ≤
      P.epsilon *
        ((1 - P.epsilon) *
            frozenOuterThirdBaseFrostmanExponent P W.stage etaKT absorbEta -
          (10 * P.eta W.stage / (P.epsilon * beta))) :=
    frozenOuterThirdBaseFrostmanExponent_budget
      P W.stage hepsilonHalf
  exact
    Family8CanonicalBufferedFrozenOuterBaseScalarV1.Witness.canonicalBuffered_fixedConflict_baseScalar_le
      D hD Cmulti Sseq P W hetaF hCKTfinite hCKTone hCKT
        habsorbEta hsmall hscaleGain hbudget

#print axioms
  canonicalBuffered_fixedConflict_baseScalar_le_explicitExponent

end Witness
end
end Family8CanonicalBufferedFrozenOuterBaseScalarV2

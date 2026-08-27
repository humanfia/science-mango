import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41AutomaticComparisonLambdaV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1

open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41AutomaticComparisonLambdaV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1

noncomputable section

/-!
# Honest selected-counting numerics for the six-radius normalized lane

The five-radius selected-counting condition cannot be reused after C
normalization because the trace tolerance, hence lambda, has changed.
This module records the literal six-radius condition and derives exactly the
scalar fields consumed by the arbitrary-scale selected-subfamily endpoint.
-/

/-- Residual selected-counting smallness at the C-normalized lambda. -/
def ActualY1PaperFineCNormalizedSelectedCountingSmallness
    (fineDelta globalDelta tGlobal pairScale : Real) : Prop :=
  prop41TangencyScaleFactor
      (4 * (2 * actualY1PaperFineCNormalizedChoiceLambda
        fineDelta globalDelta tGlobal pairScale)) *
      actualY1PaperFineCNormalizedChoiceLocalDelta
        fineDelta globalDelta tGlobal pairScale <
    pairScale / 1200

/-- Canonical comparison enlargement at the C-normalized local scales. -/
def actualY1PaperFineCNormalizedSelectedAutomaticComparisonLambda
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  prop41AutomaticComparisonLambda
    (2 * actualY1PaperFineCNormalizedChoiceLambda
      fineDelta globalDelta tGlobal pairScale)
    (actualY1PaperFineCNormalizedChoiceLocalDelta
      fineDelta globalDelta tGlobal pairScale)
    pairScale

/-- All scalar fields needed by the arbitrary-scale counting consumer. -/
structure ActualY1PaperFineCNormalizedSelectedCountingNumerics
    (fineDelta globalDelta tGlobal A B pairScale : Real) : Prop where
  interval_strict : A < B
  delta_pos : 0 < actualY1PaperFineCNormalizedChoiceLocalDelta
    fineDelta globalDelta tGlobal pairScale
  localScale_pos : 0 < pairScale
  lambda1_ge_one : 1 <=
    2 * actualY1PaperFineCNormalizedChoiceLambda
      fineDelta globalDelta tGlobal pairScale
  interval_width : (1 / 2 : Real) <= B - A
  small_scale :
    prop41TangencyScaleFactor
        (4 * (2 * actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale)) *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale <
      pairScale / 1200
  comparison_enlarges :
    2 * (2 * actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale <=
      actualY1PaperFineCNormalizedSelectedAutomaticComparisonLambda
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale
  localization_scale :
    4 * prop41ActualPairLocalizationRadius
          (4 * (2 * actualY1PaperFineCNormalizedChoiceLambda
            fineDelta globalDelta tGlobal pairScale))
          (actualY1PaperFineCNormalizedChoiceLocalDelta
            fineDelta globalDelta tGlobal pairScale)
          pairScale <=
      Real.sqrt
        (actualY1PaperFineCNormalizedSelectedAutomaticComparisonLambda
            fineDelta globalDelta tGlobal pairScale *
          actualY1PaperFineCNormalizedChoiceLocalDelta
            fineDelta globalDelta tGlobal pairScale / pairScale)

/-- The sharp scale, normalized three-shift smallness, and the literal
normalized counting condition generate the complete scalar package. -/
theorem actualY1PaperFineCNormalizedSelectedCountingNumerics_of_pairScaleSmall
    {fineDelta globalDelta tGlobal A B pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal (B - A))
    (hthree : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      fineDelta globalDelta tGlobal pairScale)
    (hcount : ActualY1PaperFineCNormalizedSelectedCountingSmallness
      fineDelta globalDelta tGlobal pairScale) :
    ActualY1PaperFineCNormalizedSelectedCountingNumerics
      fineDelta globalDelta tGlobal A B pairScale := by
  let scales :=
    actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall
      N hthree
  have hfactor :=
    q_le_prop41TangencyScaleFactor_of_one_le scales.traceQ_one
  have hlambdaOne : 1 <=
      2 * actualY1PaperFineCNormalizedChoiceLambda
        fineDelta globalDelta tGlobal pairScale := by
    unfold actualY1PaperFineCNormalizedChoiceLambda
    nlinarith [scales.traceQ_one, hfactor]
  refine {
    interval_strict := by
      linarith [N.outerWidth_lower]
    delta_pos := scales.choice_scale.localDelta_pos
    localScale_pos := scales.choice_scale.pairScale_pos
    lambda1_ge_one := hlambdaOne
    interval_width := N.outerWidth_lower
    small_scale := by
      simpa only [ActualY1PaperFineCNormalizedSelectedCountingSmallness]
        using hcount
    comparison_enlarges := ?_
    localization_scale := ?_ }
  · exact prop41AutomaticComparisonLambda_enlarges
      hlambdaOne scales.choice_scale.localDelta_pos
        scales.choice_scale.pairScale_pos
  · exact prop41AutomaticComparisonLambda_localization
      hlambdaOne scales.choice_scale.localDelta_pos
        scales.choice_scale.pairScale_pos

#print axioms ActualY1PaperFineCNormalizedSelectedCountingSmallness
#print axioms actualY1PaperFineCNormalizedSelectedAutomaticComparisonLambda
#print axioms ActualY1PaperFineCNormalizedSelectedCountingNumerics
#print axioms actualY1PaperFineCNormalizedSelectedCountingNumerics_of_pairScaleSmall

end

end FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1

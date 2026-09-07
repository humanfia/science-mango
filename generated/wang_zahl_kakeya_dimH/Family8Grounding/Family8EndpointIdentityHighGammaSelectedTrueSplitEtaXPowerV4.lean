import Family8Grounding.Family8EndpointIdentityHighGammaAutomaticHLongGeometryAdapterV1
import Family8Grounding.Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1
import Family8Grounding.Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
import Mathlib.Tactic

/-!
# Selected split-eta high-gamma X-power seam

The selected top wrapper fixes a single source exponent `o`, its literal
Section-8 exponent `s`, the canonical quantum `q`, and the maximal shared
card exponent `card = (1 - epsilon) * thirdEta - 3 * o - 2 * q`.  Every
downstream scalar field is mechanically generated from one same-object
estimate

`activeCoarseCardScaleMass U <= delta ^ (-card)`.

This module records that unique remaining analytic seam and extends the old
mechanical raw threshold by exactly the two finite thresholds used by the
correlated base/density constructions.  It exposes no standalone CKT cap,
density gate, geometric B2 base, or third-loss field.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityHighGammaSelectedTrueSplitEtaXPowerV4

open Submission.Kakeya.ConvexGeometry
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8CanonicalGlobalOuterParameterAllocationV1
open Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityHighGammaAutomaticHLongGeometryAdapterV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
open Family8FullRefinementActualDatumV1
open Family8HighGammaParameterLadderV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8SectionEightOutputEtaV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The selected Section-8 source exponent. -/
def selectedTrueSplitSectionEta
    (P : ParameterLadder epsilon0 beta gamma) (thirdEta : Real) : Real :=
  sectionEightOutputEta P (selectedTrueSplitOutputEta P thirdEta)

/-- The one quantum used by the actual card-scale and scalar absorptions. -/
def selectedTrueSplitQuantum
    (P : ParameterLadder epsilon0 beta gamma) (thirdEta : Real) : Real :=
  canonicalGlobalOuterQuantum P (selectedTrueSplitSectionEta P thirdEta)

/-- The old high-gamma threshold supplies selector/base/radius/stage fields.
The two new factors pay the correlated fixed constant and the actual frozen
assembly loss at the selected quantum. -/
def highGammaSelectedTrueSplitEtaRawDelta0
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal) : NNReal :=
  min (highGammaAutomaticRawDelta0
      H targetEpsilon etaKT thirdEta delta0)
    (min
      (endpointCorrelatedBaseThreshold
        (selectedTrueSplitQuantum H.ladder thirdEta))
      (activeFrozenComparableLossAbsorptionThreshold
        (selectedTrueSplitQuantum H.ladder thirdEta)))

theorem highGammaSelectedTrueSplitEtaRawDelta0_pos
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT thirdEta : Real) {delta0 : NNReal}
    (hdelta0 : 0 < delta0) :
    0 < highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0 := by
  unfold highGammaSelectedTrueSplitEtaRawDelta0
  exact lt_min
    (highGammaAutomaticRawDelta0_pos H hbeta hgamma
      targetEpsilon etaKT thirdEta hdelta0)
    (lt_min (endpointCorrelatedBaseThreshold_pos _)
      (activeFrozenComparableLossAbsorptionThreshold_pos _))

theorem highGammaSelectedTrueSplitEtaRawDelta0_le_old
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal) :
    highGammaSelectedTrueSplitEtaRawDelta0
        H targetEpsilon etaKT thirdEta delta0 <=
      highGammaAutomaticRawDelta0
        H targetEpsilon etaKT thirdEta delta0 := by
  exact min_le_left _ _

theorem highGammaSelectedTrueSplitEtaRawDelta0_le_correlated
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal) :
    highGammaSelectedTrueSplitEtaRawDelta0
        H targetEpsilon etaKT thirdEta delta0 <=
      endpointCorrelatedBaseThreshold
        (selectedTrueSplitQuantum H.ladder thirdEta) := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem highGammaSelectedTrueSplitEtaRawDelta0_le_densityFrozen
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal) :
    highGammaSelectedTrueSplitEtaRawDelta0
        H targetEpsilon etaKT thirdEta delta0 <=
      activeFrozenComparableLossAbsorptionThreshold
        (selectedTrueSplitQuantum H.ladder thirdEta) := by
  exact (min_le_right _ _).trans (min_le_right _ _)

theorem highGammaSelectedTrueSplitEtaRawDelta0_le_selector
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal) :
    highGammaSelectedTrueSplitEtaRawDelta0
        H targetEpsilon etaKT thirdEta delta0 <=
      endpointIdentityFirstCrossingImpossibleThreshold H.ladder := by
  exact (highGammaSelectedTrueSplitEtaRawDelta0_le_old
    H targetEpsilon etaKT thirdEta delta0).trans
      (highGammaAutomaticRawDelta0_le_selector
        H targetEpsilon etaKT thirdEta delta0)

/-- The literal same-`U` estimate used by the correlated base, density, and
third-loss producers.  The witness is the single automatic normalized view;
no cover, parentwise witness, or assembly is reselected. -/
def selectedTrueSplitEtaXPowerAtRaw
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaRaw : delta <= highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0)
    (hFOutput : FrostmanHypotheses D
      (selectedTrueSplitOutputEta H.ladder thirdEta)) : Prop :=
  let P := H.ladder
  let q := selectedTrueSplitQuantum P thirdEta
  let cardScaleEta := selectedTrueSplitCardScaleEta P thirdEta
  let hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_selector
        H targetEpsilon etaKT thirdEta delta0)
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hgamma hselectorSmall hFOutput
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le (highGammaLadder_epsilon_le_half H hbeta hgamma)
  let U := activeFineRestrictedScaleCover U0
  (activeCoarseCardScaleMass U : ENNReal) <=
    (delta : ENNReal) ^ (-cardScaleEta)

#print axioms selectedTrueSplitSectionEta
#print axioms selectedTrueSplitQuantum
#print axioms highGammaSelectedTrueSplitEtaRawDelta0_pos
#print axioms highGammaSelectedTrueSplitEtaRawDelta0_le_old
#print axioms highGammaSelectedTrueSplitEtaRawDelta0_le_correlated
#print axioms highGammaSelectedTrueSplitEtaRawDelta0_le_densityFrozen
#print axioms highGammaSelectedTrueSplitEtaRawDelta0_le_selector
#print axioms selectedTrueSplitEtaXPowerAtRaw

end
end Family8EndpointIdentityHighGammaSelectedTrueSplitEtaXPowerV4

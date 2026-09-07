import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8NormalizedLongCoreCanonicalRawEq66GraphFrozenLocalCapV1
import Mathlib.Tactic

/-!
# Canonical graph/frozen raw Eq. (66) identity from a selected local cap

This is the local-cap successor of the canonical raw identity bridge.  The
selected graph and frozen assembly are unchanged; only the unnecessarily
global source Katz--Tao premise is replaced by the fixed-`W.m` fibre cap that
the first outer transport actually consumes.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalGraphFrozenRawEq66IdentityLocalCapBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalRawEq66GraphFrozenLocalCapV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySourceMassFactorizationRoundTripV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Select the canonical graph/frozen identity and its raw product from only
the local source-to-`tau_m` cap attached to the selected long-core node. -/
theorem exists_canonicalGraphFrozenIdentity_rawEq66_of_selectedSourceTauFibreCap
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W ≤
      (1 / 16 : NNReal))
    (fibreCF : ENNReal) (hCFfinite : fibreCF ≠ ∞)
    (hFibres :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let U := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      (activeFineRestrictedScaleCover U).IsFrostmanAtScale fibreCF)
    {etaF etaKT lossEta : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hFirstCap : SelectedSourceTauFibreCap D C S W etaKT)
    (hlossEta : 0 < lossEta)
    (hdeltaLoss : delta ≤
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let U := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let hscale : S.tau W.m ≤ canonicalBufferedRadius W :=
      tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
    let Y := (tauActiveCoarseDatum E C S W).shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
      have hmass : D.shading.shadingMass ≠ 0 := by
        have hfloor : (delta : ENNReal) ^ (2 * etaF) ≤
            D.shading.shadingMass :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
        have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
          ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
            ENNReal.coe_ne_top
        exact ne_of_gt (hpositive.trans_le hfloor)
      exact canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        E hE C S P W hepsilonHalf
          (Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
            D C S W.m hmass)
    let T := activeFineRestrictedScaleCover U
    let YR := activeFineRestrictedShading U Y
    let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
    let Psource := sourceMassCoarseTubePartition T hscale YR hsourceR
    ∃ R : SameAssemblyFullCoefficientGraphIdentity
        (activeFineRestrictedFamily U) T Psource.asConvexFactorization YR
          fibreCF,
      R.A.loss = frozenComparableLoss {i // i ∈ U.activeFine}
          (Fin U.activeCoarse.card) ∧
      D.shading.averageMultiplicity ≤
        R.collapsedPrefix (delta := delta)
            (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
              delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKT)))
            lossEta *
          R.A.frozenCoarse.averageMultiplicity := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let hscale : S.tau W.m ≤ canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  let Y := (tauActiveCoarseDatum E C S W).shading
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor : (delta : ENNReal) ^ (2 * etaF) ≤
        D.shading.shadingMass :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
    have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
        ENNReal.coe_ne_top
    exact ne_of_gt (hpositive.trans_le hfloor)
  have hsourceTau :
      (IndexedShadingRefinement.restrictTo E.shading
        (tauScaleCover E C S W).activeFine).shading.shadingMass ≠ 0 :=
    Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
      D C S W.m hmass
  let hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    canonicalBufferedTauActiveCover_restrictedMass_ne_zero
      E hE C S P W hepsilonHalf hsourceTau
  let T := activeFineRestrictedScaleCover U
  let YR := activeFineRestrictedShading U Y
  let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
  let Psource := sourceMassCoarseTubePartition T hscale YR hsourceR
  obtain ⟨A, hLoss, k, axis, label, hQ, hRaw⟩ :=
    exists_fullRefinement_normalizedLongCore_canonicalRawEq66GraphFrozen_of_selectedSourceTauFibreCap
      D hD C S P W hepsilonHalf hbufferedSixteenth fibreCF hCFfinite
        hFibres hFsource hFirstCap hlossEta hdeltaLoss
  let R : SameAssemblyFullCoefficientGraphIdentity
      (activeFineRestrictedFamily U) T Psource.asConvexFactorization YR
        fibreCF :=
    { A := A
      k := k
      axis := axis
      label := label
      graphCertificate := hQ }
  refine ⟨R, hLoss, ?_⟩
  simpa only [SameAssemblyFullCoefficientGraphIdentity.collapsedPrefix,
    SameAssemblyFullCoefficientGraphIdentity.graphLoss,
    SameAssemblyFullCoefficientGraphIdentity.graphAverage, R, E, hE, U,
    hscale, Y, hsource, T, YR, hsourceR, Psource] using hRaw

#print axioms
  exists_canonicalGraphFrozenIdentity_rawEq66_of_selectedSourceTauFibreCap

end
end Family8CanonicalGraphFrozenRawEq66IdentityLocalCapBridgeV1

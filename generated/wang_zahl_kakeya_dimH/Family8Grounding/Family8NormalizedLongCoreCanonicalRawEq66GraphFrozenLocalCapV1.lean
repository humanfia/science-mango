import Family8Grounding.Family8NormalizedLongCoreCanonicalRawEq66GraphFrozenV1
import Mathlib.Tactic

/-!
# Canonical raw Equation-(66) graph from the selected source-to-tau cap

The legacy raw graph producer asked for `KatzTaoHypotheses D etaKT` even
though it used neither the density half of that conjunction nor
non-concentration away from the one selected source-to-`tau_m` cover.  This
successor exposes exactly the finite-fibre bound consumed by the deterministic
first-outer transport, at the literal `W.m` selected by the long-core witness.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreCanonicalRawEq66GraphFrozenLocalCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8Family7CoordinateToVerticalB2SupportV1
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7FirstCrossingFullCoefficientTripleV3
open Family8Family7FullCoefficientGraphCertificateFromFibreFrostmanV3
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreFirstOuterParentTransportV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongCoreTauActiveRestrictedCoarseB2SupportV2
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySourceMassFactorizationRoundTripV1
open Family8StickyParentHullVolumeBoundV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon etaKT : Real} {eta : Nat -> Real}
  {epsilon0 beta gamma : Real}

/-- The actual local packing input read by the first outer factor: every
active parent fibre of the single source-to-`tau_m` cover selected by `W` has
the displayed natural-cardinality cap. -/
def SelectedSourceTauFibreCap
    (D : ActualTubeDatum delta index)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C N epsilon eta S)
    (etaKT : Real) : Prop :=
  let firstCap := katzTaoDoubledFiberNatCap
    delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKT))
  forall k : {k // k ∈
      (sourceTauCover (fullRefinementDatum D) C S W.m).activeCoarse},
    ((activeIndexFactorization
      (sourceTauCover (fullRefinementDatum D) C S W.m)).fiber k).card <=
        firstCap

/-- The same-assembly raw Eq. (66) producer from only the selected local
source-to-tau fibre cap.  In particular no source density lower bound and no
global Katz--Tao predicate is consumed. -/
theorem exists_fullRefinement_normalizedLongCore_canonicalRawEq66GraphFrozen_of_selectedSourceTauFibreCap
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal))
    (CF : ENNReal) (hCFfinite : CF ≠ ∞)
    (hFibres :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let U := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      (activeFineRestrictedScaleCover U).IsFrostmanAtScale CF)
    {etaF etaKT lossEta : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hFirstCap : SelectedSourceTauFibreCap D C S W etaKT)
    (hlossEta : 0 < lossEta)
    (hdeltaLoss : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let U := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let hscale : S.tau W.m <= canonicalBufferedRadius W :=
      tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
    let Y := (tauActiveCoarseDatum E C S W).shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
      have hmass : D.shading.shadingMass ≠ 0 := by
        have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
            D.shading.shadingMass :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
        have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
          ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
            ENNReal.coe_ne_top
        exact ne_of_gt (hpositive.trans_le hfloor)
      exact
        canonicalBufferedTauActiveCover_restrictedMass_ne_zero
          E hE C S P W hepsilonHalf
            (Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
              D C S W.m hmass)
    let T := activeFineRestrictedScaleCover U
    let YR := activeFineRestrictedShading U Y
    let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
    let Psource := sourceMassCoarseTubePartition T hscale YR hsourceR
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Psource.asConvexFactorization YR 1,
      A.loss = frozenComparableLoss {i // i ∈ U.activeFine}
          (Fin U.activeCoarse.card) /\
      exists k : Fin T.coarseCard, exists axis : Fin 3, exists label : Int,
        let baseLoss : ENNReal :=
          (A.loss : ENNReal) *
            (Psource.asConvexFactorization.index.coarse.card : ENNReal)
        let d : ENNReal :=
          (sourceActiveFineShading Psource.asConvexFactorization YR).shadingDensity /
            baseLoss
        let graphLoss : ENNReal :=
          ((3 * verticalGraphCBucketLoss
            (((S.tau W.m : NNReal) : Real) / 2) : Nat) : ENNReal)
        let effectiveCF : ENNReal := CF * (d⁻¹ * graphLoss)
        let firstCap : ENNReal :=
          katzTaoDoubledFiberNatCap
            delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKT))
        let graphAverage : ENNReal :=
          (firstCrossingFamilyGraphBucketShading axis label
            (activeFineRestrictedFamily U) Psource.asConvexFactorization A k).averageMultiplicity
        let collapsedPrefix : ENNReal :=
          ((firstCap * (4 * (delta : ENNReal) ^ (-lossEta))) *
            graphLoss) * graphAverage
        Nonempty
          (FirstCrossingFullCoefficientGraphCertificate
            (activeFineRestrictedFamily U) T Psource.asConvexFactorization
              YR A k axis label effectiveCF d graphLoss) /\
        D.shading.averageMultiplicity <=
          collapsedPrefix * A.frozenCoarse.averageMultiplicity := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let hscale : S.tau W.m <= canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  let Y := (tauActiveCoarseDatum E C S W).shading
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
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
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    canonicalBufferedTauActiveCover_restrictedMass_ne_zero
      E hE C S P W hepsilonHalf hsourceTau
  let T := activeFineRestrictedScaleCover U
  let YR := activeFineRestrictedShading U Y
  let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
  let Psource := sourceMassCoarseTubePartition T hscale YR hsourceR
  obtain ⟨A, hLoss, hAverage, _k0, _hFiber0, _hProduct0⟩ :=
    exists_activeIndex_frozenComparableAssembly
      U hscale Y 1 (by norm_num) hsource
  have hLossPower :
      (frozenComparableLoss {i // i ∈ U.activeFine}
        (Fin U.activeCoarse.card) : ENNReal) <=
          (delta : ENNReal) ^ (-lossEta) := by
    simpa only [U, E, hE] using
      (canonicalBufferedTauActive_frozenLoss_le_power
        E hE C S P W hepsilonHalf hlossEta hdeltaLoss)
  have hAveragePower : Y.averageMultiplicity <=
      (delta : ENNReal) ^ (-lossEta) *
        (actualRefinementShading A).averageMultiplicity := by
    rw [← canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
      E hE C S P W hepsilonHalf]
    exact hAverage.trans (mul_le_mul' hLossPower le_rfl)
  let firstCapNat : Nat := katzTaoDoubledFiberNatCap
    delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKT))
  let firstCap : ENNReal := firstCapNat
  have hFirst0 :=
    Family8IdentifiedDividingWitnessFirstOuterParentTransportV1.Witness.fullRefinement_averageMultiplicity_le_nsmul_sourceTauParent
      D C S W.m firstCapNat hFirstCap
  have hsourceTauCover : tauScaleCover E C S W =
      sourceTauCover E C S W.m := by
    unfold tauScaleCover sourceTauCover
    congr
  have hYAverage : Y.averageMultiplicity =
      (parentAggregatedShading
        (sourceTauCover E C S W.m) E.shading).averageMultiplicity := by
    dsimp only [Y, tauActiveCoarseDatum]
    rw [hsourceTauCover]
    rfl
  have hFirst : D.shading.averageMultiplicity <=
      firstCap * Y.averageMultiplicity := by
    rw [hYAverage]
    simpa only [firstCap, firstCapNat, nsmul_eq_mul] using hFirst0
  have hSourceRetention : D.shading.averageMultiplicity <=
      (firstCap * (delta : ENNReal) ^ (-lossEta)) *
        (actualRefinementShading A).averageMultiplicity := by
    calc
      D.shading.averageMultiplicity <= firstCap * Y.averageMultiplicity :=
        hFirst
      _ <= firstCap *
          ((delta : ENNReal) ^ (-lossEta) *
            (actualRefinementShading A).averageMultiplicity) :=
        mul_le_mul' le_rfl hAveragePower
      _ = (firstCap * (delta : ENNReal) ^ (-lossEta)) *
          (actualRefinementShading A).averageMultiplicity := by
        ac_rfl
  have hround : Psource.asConvexFactorization =
      toConvexFactorization T := by
    exact sourceMass_asConvexFactorization_eq_toConvexFactorization
      T hscale YR hsourceR
  have hsourceP :
      (IndexedShadingRefinement.restrictTo YR
        Psource.asConvexFactorization.index.fine).shading.shadingMass ≠ 0 := by
    rw [hround, toConvexFactorization_fine]
    exact hsourceR
  have hfull : ∀ q ∈ Psource.asConvexFactorization.index.coarse,
      IsFrostmanOn CF (activeFineRestrictedFamily U).bodyFamily
        (Psource.asConvexFactorization.index.fiber q)
        (T.coarse.tubes q).body := by
    intro q hq
    have hqT : q ∈ T.activeCoarse := by
      rw [hround] at hq
      simpa only [toConvexFactorization_coarse] using hq
    have hIn : IsFrostmanIn CF (T.fiberFamily q)
        (T.coarse.tubes q).body := by
      apply isFrostmanIn_iff_concentration_le.mpr
      exact ⟨T.fiber_carrier_subset_parent q, hFibres q hqT⟩
    have hOn : IsFrostmanOn CF (activeFineRestrictedFamily U).bodyFamily
        (T.fiber q) (T.coarse.tubes q).body :=
      (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
        (activeFineRestrictedFamily U).bodyFamily
        (T.fiber q) (T.coarse.tubes q).body).mpr hIn
    rw [hround]
    simpa only [toConvexFactorization_fiber] using hOn
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < canonicalBufferedRadius W := htau.trans_le hscale
  have hFineB2 : ∀ i,
      ((activeFineRestrictedFamily U).tubes i).carrier <=
        Metric.closedBall (0 : Space) 2 := by
    intro i
    have hparent := T.carrier_subset i (by simp only [T,
      activeFineRestrictedScaleCover_activeFine, Finset.mem_univ])
    exact hparent.trans
      (canonicalBufferedTauActiveRestrictedCoarse_carrier_subset_closedBall_two
        E hE C S W P.epsilon_pos.le hepsilonHalf hbufferedSixteenth
          (T.parent i))
  have hverticalB2 : ∀ axis : Fin 3, ∀ i ∈ T.activeFine,
      ((coordinateToVerticalFamily axis
        (activeFineRestrictedFamily U)).tubes i).carrier <=
          Metric.closedBall (0 : Space) 2 := by
    intro axis i _hi
    exact coordinateToVerticalFamily_carrier_subset_closedBall_two
      axis (activeFineRestrictedFamily U) hFineB2 i
  obtain ⟨k, hk, axis, label, hQ⟩ :=
    exists_fullCoefficientGraphCertificate_of_fibresFrostman
      (activeFineRestrictedFamily U) T Psource.asConvexFactorization
        YR A CF hCFfinite hfull htau hrho hsourceP hround hverticalB2
  dsimp only at hQ
  let baseLoss : ENNReal :=
    (A.loss : ENNReal) *
      (Psource.asConvexFactorization.index.coarse.card : ENNReal)
  let d : ENNReal :=
    (sourceActiveFineShading Psource.asConvexFactorization YR).shadingDensity /
      baseLoss
  let graphLoss : ENNReal :=
    ((3 * verticalGraphCBucketLoss
      (((S.tau W.m : NNReal) : Real) / 2) : Nat) : ENNReal)
  let effectiveCF : ENNReal := CF * (d⁻¹ * graphLoss)
  change Nonempty
    (FirstCrossingFullCoefficientGraphCertificate
      (activeFineRestrictedFamily U) T Psource.asConvexFactorization
        YR A k axis label effectiveCF d graphLoss) at hQ
  let Q := Classical.choice hQ
  let graphAverage : ENNReal :=
    (firstCrossingFamilyGraphBucketShading axis label
      (activeFineRestrictedFamily U) Psource.asConvexFactorization A k).averageMultiplicity
  let collapsedPrefix : ENNReal :=
    ((firstCap * (4 * (delta : ENNReal) ^ (-lossEta))) *
      graphLoss) * graphAverage
  have hRaw0 :=
    sourceAverage_le_fullCoefficientMiddle_mul_frozenCoarse
      (activeFineRestrictedFamily U) T Psource.asConvexFactorization
        YR A k axis label effectiveCF d graphLoss
        (firstCap * (delta : ENNReal) ^ (-lossEta))
        D.shading.averageMultiplicity Q hSourceRetention
  have hRaw : D.shading.averageMultiplicity <=
      collapsedPrefix * A.frozenCoarse.averageMultiplicity := by
    calc
      D.shading.averageMultiplicity <=
          (((firstCap * (delta : ENNReal) ^ (-lossEta)) * 4 * graphLoss) *
              graphAverage) * A.frozenCoarse.averageMultiplicity := by
        simpa only [graphAverage] using hRaw0
      _ = collapsedPrefix * A.frozenCoarse.averageMultiplicity := by
        dsimp only [collapsedPrefix]
        ac_rfl
  refine ⟨A, hLoss, k, axis, label, ?_⟩
  exact ⟨Nonempty.intro Q, hRaw⟩

#print axioms SelectedSourceTauFibreCap
#print axioms
  exists_fullRefinement_normalizedLongCore_canonicalRawEq66GraphFrozen_of_selectedSourceTauFibreCap

end
end Family8NormalizedLongCoreCanonicalRawEq66GraphFrozenLocalCapV1

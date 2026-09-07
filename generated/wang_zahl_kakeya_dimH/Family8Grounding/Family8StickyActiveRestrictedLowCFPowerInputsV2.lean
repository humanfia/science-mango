import Family8Grounding.Family8StickyShadingAwareSelectedSourcePowerBudgetsGlobalV2
import Family8Grounding.Family8StickyActiveRestrictedFiberDualCountPowerV3
import Mathlib.Tactic

/-!
# Four same-parent low-CF power inputs on an active restriction, V2

V1 omitted one namespace open and is not imported.  The shading-aware parent used for density and base is fed immediately to the
single doubled-fibre count cap.  Consequently all four scalar premises of
the fresh low-CF long-middle producer refer to one literal parent of the
same active restricted cover.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveRestrictedLowCFPowerInputsV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveRestrictedFiberDualCountPowerV3
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareSelectedSourcePowerBudgetsGlobalV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {globalDelta delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- One literal parent of the active restricted cover carries density, base,
proxy-card, and relative-count bounds simultaneously. -/
theorem exists_activeRestricted_sameParent_fourLowCFPowerInputs
    {eta p a etaF lossExp xExp baseAbsorbExp baseScaleExp : Real}
    (S0 : StickyScaleCover fine rho)
    (Y : Shading (activeFineRestrictedFamily S0).bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hAone : 1 ≤ A) (hKT : IsKatzTao A fine.bodyFamily)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hrhoOne : rho ≤ 1) (hdeltaRho : delta ≤ rho)
    (hactive : (activeFineRestrictedScaleCover S0).activeFine.Nonempty)
    (hmass : shadingMassOn Y
      (activeFineRestrictedScaleCover S0).activeFine ≠ 0)
    (hloss :
      (2 * (Nat.log 2
        (Fintype.card {i // i ∈ S0.activeFine}) + 1) : Nat) ≤
        (globalDelta : ENNReal) ^ (-lossExp))
    (hX : (activeCoarseCardScaleMass
        (activeFineRestrictedScaleCover S0) : ENNReal) ≤
      (globalDelta : ENNReal) ^ (-xExp))
    (hbaseConstant : massPopularBaseFixedConstant eta p a ≤
      (globalDelta : ENNReal) ^ (-baseAbsorbExp))
    (hqBase : ((delta : ENNReal) / (rho : ENNReal)) ≤
      (globalDelta : ENNReal) ^ baseScaleExp)
    (hbaseGain : 0 ≤ eta - (2 * p + a))
    (hbaseBudget : 2 * etaF + lossExp + xExp + baseAbsorbExp ≤
      baseScaleExp * (eta - (2 * p + a)))
    (hsourceMass : (globalDelta : ENNReal) ^ (2 * etaF) ≤
      shadingMassOn Y (activeFineRestrictedScaleCover S0).activeFine)
    {densityEtaF coverExp branchExp densityAbsorbExp densityScaleExp : Real}
    (hcover : 2 * stickyShadingAwareCoverLoss
        (activeFineRestrictedScaleCover S0) Y A ≤
      (globalDelta : ENNReal) ^ (-coverExp))
    (hbranch : 2 *
        ((shadingAwareLogPartition
          (activeFineRestrictedScaleCover S0) Y A hA0 hAtop hrho
            hdeltaRho hactive hmass).branching : ENNReal) ≤
      (globalDelta : ENNReal) ^ (-branchExp))
    (hdensityConstant : (2 * 8 * 93312 * 128 : ENNReal) ≤
      (globalDelta : ENNReal) ^ (-densityAbsorbExp))
    (hqDensity : ((delta : ENNReal) / (rho : ENNReal)) ≤
      (globalDelta : ENNReal) ^ densityScaleExp)
    (hdensityGain : 0 ≤ eta - (p + a) + 2)
    (hdensityBudget :
      2 * densityEtaF + coverExp + branchExp + densityAbsorbExp ≤
        densityScaleExp * (eta - (p + a) + 2))
    (hsourceAPower : (globalDelta : ENNReal) ^ (2 * densityEtaF) ≤ A)
    (hproxyGap : 0 ≤ eta - (p + a))
    {kappa countAbsorbExp : Real}
    (hcountExp : 0 < 2 + kappa) (hcountAbsorbExp : 0 < countAbsorbExp)
    (hAratio : A ≤
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-kappa)))
    (hsmallCount : contractedJohnProxyRadius delta rho / 8 ≤
      finiteConstantSmallDeltaThreshold
        ordinaryFiberNatCapFixedConstant countAbsorbExp) :
    let U := activeFineRestrictedScaleCover S0
    ∃ q : {q // q ∈ U.activeCoarse},
      q.1 ∈ shadingAwareSelectedParents
        U Y A hA0 hAtop hrho hactive hmass ∧
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ eta) ≤
        ((stickyFiberSourceShading U Y q.1).shadingDensity / 93312 / 128) /
          (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-(p + a))) ∧
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(2 * p + a))) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-eta)) *
          ((Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
              2 / 2)) ∧
      (Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(2 + kappa + countAbsorbExp))) ∧
      (Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) ≤
        ordinaryFiberNatCapFixedConstant *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))) := by
  dsimp only
  let U := activeFineRestrictedScaleCover S0
  obtain ⟨q, hqSelected, hdensity, hbase⟩ :=
    exists_shadingAwareSelected_sourceDensity_and_basePower
      U Y A hA0 hAtop hglobal hglobalOne hdelta hdeltaHalf hrho hrhoHalf
        hdeltaRho hactive hmass hloss hX hbaseConstant hqBase hbaseGain
        hbaseBudget hsourceMass hcover hbranch hdensityConstant hqDensity
        hdensityGain hdensityBudget hsourceAPower hproxyGap
  obtain ⟨hcard, hcount⟩ :=
    activeRestrictedFiber_fullCard_proxyPower_and_relativeCount
      S0 hdelta hdeltaHalf hrho hrhoOne hdeltaRho hAone hAtop hKT q
        hcountExp hcountAbsorbExp hAratio hsmallCount
  exact ⟨q, by simpa only [U] using hqSelected,
    by simpa only [U] using hdensity,
    by simpa only [U] using hbase,
    by simpa only [U] using hcard,
    by simpa only [U] using hcount⟩

#print axioms exists_activeRestricted_sameParent_fourLowCFPowerInputs

end
end Family8StickyActiveRestrictedLowCFPowerInputsV2

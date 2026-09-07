import Family8Grounding.Family8ContractedJohnMiddleFourGlobalPowerAbsorptionV2
import Family8Grounding.Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8StickyIdentityMassPopularNoKTFreshLongMiddleV8
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Family8Grounding.Family8StickySelectedFiberLowCFFreshCardEnvelopePowerV3

/-!
# Packaged inputs for the no-KT fresh long-middle call

This small interface keeps the dependent selected-fine cover and all four
power inputs together.  Endpoint specializations can build the package once;
the final middle theorem then performs only the generic producer call.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NoKTMiddleCallInputsV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleFourGlobalPowerAbsorptionV2
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyIdentityMassPopularNoKTFreshLongMiddleV8
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFiberLowCFFreshCardEnvelopePowerV3
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The dependent inputs consumed by the generic no-KT middle producer. -/
structure CallInputs
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (hdeltaRho : delta ≤ rho) (hcoarse : S.activeCoarse.Nonempty)
    (hM : ∀ k, k ∈ S.activeCoarse → (S.fiber k).card ≤ 1)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (boundedFiberCoarseTubePartition S hdeltaRho hcoarse 1 hM
        ).asConvexFactorization Y r)
    (frostmanEta lowerExp cardExp a cardAbsorbExp kappa : Real)
    (densityFloor lower K : ENNReal) where
  hsource :
    (IndexedShadingRefinement.restrictTo Y
      S.activeFine).shading.shadingMass ≠ 0
  hlowerTop : lower ≠ ∞
  hLowEvery :
    let T := selectedFineScaleCover S A.refinement.indices
      (assembly_indices_subset_activeFine S Y r A)
    ∀ q : {q // q ∈ T.activeCoarse},
      IsFrostmanIn lower (T.fiberFamily q.1) (T.activeCoarseFamily q)
  hdensityFloor : densityFloor ≤
    (sourceActiveFineShading
      (toConvexFactorization S) Y).shadingDensity
  hdensityBudget :
    16 * (A.loss : ENNReal) *
        (((((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (frostmanEta -
              ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a))) *
          93312) * 128) ≤ densityFloor
  hbaseBudget :
    16 * (A.loss : ENNReal) *
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(2 * (2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a))) ≤
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-frostmanEta)) *
        ((((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (2 : Nat)) / 2) * densityFloor
  hcardAndCount :
    let T := selectedFineScaleCover S A.refinement.indices
      (assembly_indices_subset_activeFine S Y r A)
    ∀ q : {q // q ∈ T.activeCoarse},
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
          (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-cardExp)) ∧
        (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
          K * (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa)))

/-- Once the packaged inputs are available, the remaining endpoint theorem is
only the generic no-KT fresh-middle invocation. -/
theorem CallInputs.exists_freshLongMiddle
    {globalDelta : NNReal}
    {frostmanBeta frostmanEpsilon frostmanEta gamma : Real}
    {lowerExp cardExp a cardAbsorbExp kappa globalEta : Real}
    {delta0 : NNReal}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon frostmanEta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho) (hcoarse : S.activeCoarse.Nonempty)
    (hM : ∀ k, k ∈ S.activeCoarse → (S.fiber k).card ≤ 1)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (boundedFiberCoarseTubePartition S hdeltaRho hcoarse 1 hM
        ).asConvexFactorization Y r)
    {densityFloor lower K : ENNReal}
    (B : CallInputs S Y r hdeltaRho hcoarse hM A
      frostmanEta lowerExp cardExp a cardAbsorbExp kappa
      densityFloor lower K)
    (hcombined : 0 < lowerExp + cardExp)
    (ha : 0 < a) (hcardAbsorbExp : 0 < cardAbsorbExp)
    (hsmallFresh : contractedJohnProxyRadius delta rho / 8 ≤
      selectedParentLowCFFreshCardEnvelopePowerThreshold a cardAbsorbExp)
    (hlowerPower : lower ≤
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
        (-lowerExp)))
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 ≤ delta0)
    (hsmallSource : contractedJohnProxyRadius delta rho / 8 ≤
      Family8StickyFiberContractedJohnSourcePowerEndpointV1.contractedJohnSourcePowerEndpointThreshold a)
    {absorbExp : Real}
    (hglobalDeltaOne : globalDelta ≤ 1)
    (hK0 : K ≠ 0) (hKTop : K ≠ ∞)
    (habsorbExp : 0 < absorbExp)
    (hratioSmall : delta / rho ≤
      contractedJohnMiddleFourActualPowerThreshold
        K frostmanEpsilon frostmanBeta gamma
          ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)
          absorbExp)
    (hratioDelta : (((delta / rho : NNReal) : ENNReal)) ≤
      (globalDelta : ENNReal) ^ (frostmanEpsilon ^ 2))
    (hnet : 0 ≤
      contractedJohnMiddleRatioGain
        frostmanEpsilon frostmanBeta gamma
          ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)
          kappa - absorbExp)
    (hbudget : 10 * globalEta ≤
      frostmanEpsilon ^ 2 *
        (contractedJohnMiddleRatioGain
          frostmanEpsilon frostmanBeta gamma
            ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)
            kappa - absorbExp))
    (hbetaTwo : frostmanBeta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - frostmanBeta) :
    ∃ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      ∃ selected : Finset {i // i ∈
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A)).fiber q.1},
        selected.Nonempty ∧
        (actualRefinementShading A).averageMultiplicity ≤
          A.frozenCoarse.averageMultiplicity *
            ((globalDelta : ENNReal) ^ (10 * globalEta) *
              sectionEightScaleCountFrostmanFactor
                delta rho selected.card gamma) := by
  exact exists_massPopular_fresh_selected_actualAverage_le_longMiddle_noKT
    hF S Y r hdelta hdeltaHalf hrho hrhoOne hdeltaRho hcoarse hM A
      B.hsource B.hlowerTop B.hLowEvery B.hdensityFloor B.hdensityBudget
      B.hbaseBudget B.hcardAndCount hcombined ha hcardAbsorbExp
      hsmallFresh hlowerPower hdelta0 hsmallSource hglobalDeltaOne hK0
      hKTop habsorbExp hratioSmall hratioDelta hnet hbudget hbetaTwo
      hgammaTwo hgap

#print axioms CallInputs.exists_freshLongMiddle

end
end Family8NoKTMiddleCallInputsV2

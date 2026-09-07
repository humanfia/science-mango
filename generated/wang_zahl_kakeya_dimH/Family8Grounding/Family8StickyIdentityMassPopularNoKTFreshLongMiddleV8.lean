import Family8Grounding.Family8IdentityMassPopularDensityQuotientV3
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8StickyIdentityMassPopularLowCFPowerInputsV11
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Family8Grounding.Family8StickySelectedFiberLowCFFreshLongMiddleProducerV1
import Mathlib.Tactic

/-!
# Same-assembly no-KT fresh long-middle producer

The mass-popular parent, frozen average factor, and fresh selected fibre are
kept on the literal same bounded assembly. Source Katz--Tao is not an input.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyIdentityMassPopularNoKTFreshLongMiddleV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleFourGlobalPowerAbsorptionV2
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8IdentityMassPopularDensityQuotientV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyIdentityMassPopularLowCFPowerInputsV11
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFiberLowCFFreshCardEnvelopePowerV3
open Family8StickySelectedFiberLowCFFreshLongMiddleProducerV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho globalDelta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual refinement average of one bounded assembly is controlled by
its own frozen coarse average and a genuine fresh Section 8 middle factor. -/
theorem exists_massPopular_fresh_selected_actualAverage_le_longMiddle_noKT
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
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0)
    {densityFloor lower K : ENNReal}
    (hlowerTop : lower ≠ ∞)
    (hLowEvery :
      let T := selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A)
      ∀ q : {q // q ∈ T.activeCoarse},
        IsFrostmanIn lower
          (T.fiberFamily q.1) (T.activeCoarseFamily q))
    (hdensityFloor : densityFloor ≤
      (sourceActiveFineShading
        (toConvexFactorization S) Y).shadingDensity)
    (hdensityBudget :
      16 * (A.loss : ENNReal) *
          (((((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
              (frostmanEta -
                ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a))) *
            93312) * 128) ≤ densityFloor)
    (hbaseBudget :
      16 * (A.loss : ENNReal) *
          (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-(2 * (2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a))) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-frostmanEta)) *
          ((((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (2 : Nat)) / 2) * densityFloor)
    (hcardAndCount :
      let T := selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A)
      ∀ q : {q // q ∈ T.activeCoarse},
        (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
              (-cardExp)) ∧
          (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
            K * (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))))
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
  let hindices := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hindices
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  let scale : ENNReal :=
    ((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal)
  let p : Real := 2 * lowerExp + 2 * cardExp + a + cardAbsorbExp
  have hscalePosNN : 0 < contractedJohnProxyRadius delta rho / 8 :=
    div_pos (contractedJohnProxyRadius_pos hdelta hrho) (by norm_num)
  have hscale0 : scale ≠ 0 := by
    dsimp only [scale]
    exact ENNReal.coe_ne_zero.mpr hscalePosNN.ne'
  have hscaleTop : scale ≠ ∞ := by
    dsimp only [scale]
    exact ENNReal.coe_ne_top
  have hcardAndCount' : ∀ q : {q // q ∈ T.activeCoarse},
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
          scale ^ (-cardExp) ∧
        (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
          K * (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))) := by
    simpa only [T, hindices, scale] using hcardAndCount
  obtain ⟨q, hproduct, hdensityCombined, hbasePower,
      hfullCard, hparentCount⟩ :=
    Family8StickyIdentityMassPopularLowCFPowerInputsV11.exists_boundedAssembly_massPopular_sameProduct_fourPowerInputs_noKT_of_density
      S Y r hdeltaRho hcoarse hM A hdelta hdeltaHalf hsource
        hdensityFloor hdensityBudget hbaseBudget hcardAndCount'
  have hLow : IsFrostmanIn lower
      (T.fiberFamily q.1) (T.activeCoarseFamily q) := by
    simpa only [T, hindices] using hLowEvery q
  have hsourceDensityPower : scale ^ frostmanEta ≤
      ((stickyFiberSourceShading T Z q.1).shadingDensity / 93312 / 128) /
        scale ^ (-(p + a)) := by
    apply rpow_le_density_div_negativePower_of_combined hscale0 hscaleTop
    simpa only [p, scale, T, Z, hindices] using hdensityCombined
  obtain ⟨selected, hselected, hmiddle⟩ :=
    exists_fresh_selected_four_mul_sourceAverage_le_longMiddle
      hF T Z hdelta hdeltaHalf hrho hrhoOne hdeltaRho q
        hlowerTop hLow hcombined ha hcardAbsorbExp hsmallFresh
        hlowerPower hfullCard K hdelta0 hsmallSource hsourceDensityPower
        hbasePower hparentCount hglobalDeltaOne hK0 hKTop habsorbExp
        hratioSmall hratioDelta hnet hbudget hbetaTwo hgammaTwo hgap
  refine ⟨q, selected, hselected, ?_⟩
  calc
    (actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (stickyFiberSourceShading T Z q.1).averageMultiplicity) := by
      simpa only [T, Z, hindices] using hproduct
    _ = A.frozenCoarse.averageMultiplicity *
        (4 * (stickyFiberSourceShading T Z q.1).averageMultiplicity) := by
      ring
    _ ≤ A.frozenCoarse.averageMultiplicity *
        ((globalDelta : ENNReal) ^ (10 * globalEta) *
          sectionEightScaleCountFrostmanFactor
            delta rho selected.card gamma) :=
      mul_le_mul' le_rfl hmiddle

#print axioms
  exists_massPopular_fresh_selected_actualAverage_le_longMiddle_noKT

end
end Family8StickyIdentityMassPopularNoKTFreshLongMiddleV8

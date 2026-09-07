import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedGlobalOuterThickPowerV3
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Family8Grounding.Family8SelectedParentGreedyBlockFiberIdentityV2
import Mathlib.Tactic

/-!
# Exact-assembly specialization of the canonical outer/thick power

The source nonvanishing premise already carried by the mass-popular
ExactAssembly branch implies nonzero mass of its literal refinement.  This
thin proof-valued adapter feeds that fact to the callback-free global
Frostman/source-Katz--Tao producer without re-elaborating its dependent
canonical-input conclusion.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalSelectedExactAssemblyGlobalOuterThickPowerV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8AllFrostmanStickyPopularParentPowerV4
open Family8CanonicalOuterThickNEnvelopePowerAlgebraV4
open Family8CanonicalSelectedRefinedFrostmanPowerAlgebraV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8PaperEq45MaxWitnessCanonicalSelectedGlobalOuterThickPowerV3
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
set_option linter.defProp false

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho sigma : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The V3 canonical certificate on exactly the final shading used by the
mass-popular ExactAssembly branch.  Its full dependent result is inferred. -/
noncomputable def canonicalExactAssemblyGlobalOuterThickPower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    {assemblyLoss : Nat}
    (assembly : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) assemblyLoss)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (h2rho : 2 * rho ≤ sigma)
    (sourceAmbient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody (maxWitnessCommonScaleEquiv rho) sourceAmbient))
    {A C : ENNReal} (hKT : S.IsKatzTaoAtScale A)
    (hglobal : IsFrostmanOn C S.activeCoarseFamily Finset.univ sourceAmbient)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    (scaleExponent katzTaoExponent cardAbsorbExponent
      globalFrostmanExponent selectionAbsorbExponent
      refinementAbsorbExponent outerAbsorbExponent beta : Real)
    (hscaleExponent : 0 ≤ scaleExponent)
    (hkatzTaoExponent : 0 ≤ katzTaoExponent)
    (hcardAbsorbExponent : 0 < cardAbsorbExponent)
    (hglobalFrostmanExponent : 0 ≤ globalFrostmanExponent)
    (hselectionAbsorbExponent : 0 < selectionAbsorbExponent)
    (hrefinementAbsorbExponent : 0 < refinementAbsorbExponent)
    (houterAbsorbExponent : 0 < outerAbsorbExponent)
    (hbeta : 0 ≤ beta)
    (hcardSmall : delta ≤
      stickyPopularParentPowerThreshold cardAbsorbExponent)
    (hselectionSmall : delta ≤
      canonicalSelectedRefinementFixedThreshold selectionAbsorbExponent)
    (hrefinementSmall : delta ≤
      canonicalSelectedRefinementFixedThreshold refinementAbsorbExponent)
    (houterSmall : delta ≤
      canonicalOuterThickFixedThreshold beta outerAbsorbExponent)
    (hscale : (delta : ENNReal) ^ scaleExponent ≤ (rho : ENNReal))
    (hA : A ≤ (delta : ENNReal) ^ (-katzTaoExponent))
    (hC : C ≤ (delta : ENNReal) ^ (-globalFrostmanExponent)) :=
  canonicalSelected_outerThickLoss_le_delta_negativePower_of_globalFrostman_sourceKT
    D hD S U P assembly.refinement.shading hrho hrhoHalf h2rho
    sourceAmbient ambientComparisonConstant ambient_is_unit_scale hKT hglobal
    (refinement_shadingMass_ne_zero assembly hsource)
    scaleExponent katzTaoExponent cardAbsorbExponent
    globalFrostmanExponent selectionAbsorbExponent
    refinementAbsorbExponent outerAbsorbExponent beta hscaleExponent
    hkatzTaoExponent hcardAbsorbExponent hglobalFrostmanExponent
    hselectionAbsorbExponent hrefinementAbsorbExponent
    houterAbsorbExponent hbeta hcardSmall hselectionSmall
    hrefinementSmall houterSmall hscale hA hC

#print axioms canonicalExactAssemblyGlobalOuterThickPower

end
end Family8PaperEq45MaxWitnessCanonicalSelectedExactAssemblyGlobalOuterThickPowerV4

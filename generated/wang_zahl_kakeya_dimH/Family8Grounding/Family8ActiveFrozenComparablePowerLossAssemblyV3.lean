import Family8Grounding.Family8ActiveFrozenComparableLogLossAbsorptionV4
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActiveFrozenComparablePowerLossAssemblyV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ComparableMultiplicityBucketsV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8SourceActiveFineActualAverageIdentityV2
open Family8NormalizedCrossingSourceTauShadingV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8ActiveFrozenComparableLogLossAbsorptionV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-!
# Frozen comparable assembly with its active logarithmic loss absorbed

This is the same literal assembly and the same retained refinement as V5.
The numerical V4 theorem is applied immediately, so downstream Section 8
composition sees an arbitrary small power loss rather than a raw pair of
finite-cardinality logarithms.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

theorem exists_activeIndex_frozenComparableAssembly_with_powerLoss
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hscale : delta ≤ rho)
    (r : Real) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo D.shading
        S.activeFine).shading.shadingMass ≠ 0)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta ≤
      activeFrozenComparableLossAbsorptionThreshold lossEta) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition
          (activeFineRestrictedScaleCover S) hscale
          (activeFineRestrictedShading S D.shading)
          (activeFineRestrictedSourceMass_ne_zero
            S D.shading hsource)).asConvexFactorization
        (activeFineRestrictedShading S D.shading) r,
      A.loss = frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) ∧
      (activeFineShading S D.shading).averageMultiplicity ≤
        (delta : ENNReal) ^ (-lossEta) *
          (actualRefinementShading A).averageMultiplicity ∧
      ∃ k : Fin S.activeCoarse.card,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
  obtain ⟨A, hloss, havg, k, hk, hproduct⟩ :=
    exists_activeIndex_frozenComparableAssembly S hscale D.shading r hr hsource
  have hlossPower :
      (frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin S.activeCoarse.card) : ENNReal) ≤
        (delta : ENNReal) ^ (-lossEta) :=
    activeFrozenComparableLoss_le_rpow D hD S hlossEta hdelta
  refine ⟨A, hloss, ?_, k, hk, hproduct⟩
  exact havg.trans (mul_le_mul' hlossPower le_rfl)

#print axioms exists_activeIndex_frozenComparableAssembly_with_powerLoss

end
end Family8ActiveFrozenComparablePowerLossAssemblyV3

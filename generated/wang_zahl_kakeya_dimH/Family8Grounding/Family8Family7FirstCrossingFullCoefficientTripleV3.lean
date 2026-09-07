import Family8Grounding.Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1

/-!
# Same-object triple estimate for the Family7 full-coefficient graph

The active source average first passes through the frozen-comparable
assembly, then its same-product factorization, and finally the literal graph
average retained by the full-coefficient certificate.  The resulting middle
average is exactly `sourceLoss * 4 * graphLoss * graphAverage`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFullCoefficientTripleV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- The exact hTriple algebra on the same assembly, coarse factor, and graph
stored in the full-coefficient certificate. -/
theorem sourceAverage_le_fullCoefficientMiddle_mul_frozenCoarse
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) {r : Real} (A : Assembly P Y r)
    (k : Fin T.coarseCard) (axis : Fin 3) (label : Int)
    (CF d graphLoss sourceLoss sourceAverage : ENNReal)
    (Q : FirstCrossingFullCoefficientGraphCertificate
      F T P Y A k axis label CF d graphLoss)
    (hsource : sourceAverage ≤
      sourceLoss * (actualRefinementShading A).averageMultiplicity) :
    sourceAverage ≤
      ((sourceLoss * 4 * graphLoss) *
          (firstCrossingFamilyGraphBucketShading
            axis label F P A k).averageMultiplicity) *
        A.frozenCoarse.averageMultiplicity := by
  calc
    sourceAverage ≤
        sourceLoss * (actualRefinementShading A).averageMultiplicity :=
      hsource
    _ ≤ sourceLoss *
        (4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity)) :=
      mul_le_mul' le_rfl Q.same_product
    _ ≤ sourceLoss *
        (4 * (A.frozenCoarse.averageMultiplicity *
          (graphLoss *
            (firstCrossingFamilyGraphBucketShading
              axis label F P A k).averageMultiplicity))) :=
      mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl Q.final_average))
    _ = ((sourceLoss * 4 * graphLoss) *
          (firstCrossingFamilyGraphBucketShading
            axis label F P A k).averageMultiplicity) *
        A.frozenCoarse.averageMultiplicity := by
      ac_rfl

#print axioms
  sourceAverage_le_fullCoefficientMiddle_mul_frozenCoarse

end
end Family8Family7FirstCrossingFullCoefficientTripleV3

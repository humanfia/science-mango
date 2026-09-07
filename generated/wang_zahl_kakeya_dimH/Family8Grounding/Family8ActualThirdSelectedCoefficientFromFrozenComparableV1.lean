import Family8Grounding.Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Mathlib.Tactic

/-!
# Selected-third coefficient from the frozen comparable base

The frozen-neighborhood assembly already bounds its literal coarse average
by twice the dyadic comparable base.  Consequently the selected-third
incidence seam needs only the scalar statement that the selected coefficient
dominates that base.  No HRow factor, Frostman constant comparison, or second
row is introduced here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActualThirdSelectedCoefficientFromFrozenComparableV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe v

variable {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
variable {a b : NNReal}

/-- The exact scalar left for the Eq. 45 / dyadic-selection layer: the
selected coefficient dominates twice the outer comparable base of the same
frozen assembly. -/
def FrozenComparableSelectedCoefficientBaseBudget
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    {scale : NNReal} {fine : UniformTubeFamily scale fineIndex}
    {G : ConvexFamily coarseIndex}
    (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily G)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (CKT selectorLoss : ENNReal) : Prop :=
  ((2 * comparableBase A.outerLabel : Nat) : ENNReal) <=
    selectorLoss * CKT

/-- The comparable-base budget produces the exact consumer-facing
actual-third incidence.  The extra unit-ball volume is harmless because its
volume is at least one in the fixed ambient normalization. -/
theorem hRowFreshActualThirdSelectedCoefficientIncidence_of_frozenComparableBase
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    {scale : NNReal} {fine : UniformTubeFamily scale fineIndex}
    {G : ConvexFamily coarseIndex}
    (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily G)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (CKT selectorLoss : ENNReal)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex -> Set Space)
    (hcell : forall p, MeasurableSet (cell p))
    (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (hBase : FrozenComparableSelectedCoefficientBaseBudget
      Y Q A CKT selectorLoss) :
    HRowFreshActualThirdSelectedCoefficientIncidence
      Y Q A CKT selectorLoss
      Drow Crow q cell hcell selectedCells hmass hactive B := by
  have hCKT :
      CKT <= CKT * volume (unitBallBody : Set Space) := by
    calc
      CKT = CKT * 1 := by rw [mul_one]
      _ <= CKT * volume (unitBallBody : Set Space) :=
        mul_le_mul' le_rfl
          Family8AllFrostmanStickyUnionProducerV1.one_le_volume_unitBallBody
  unfold HRowFreshActualThirdSelectedCoefficientIncidence
  calc
    A.frozenCoarse.averageMultiplicity <=
        ((2 * comparableBase A.outerLabel : Nat) : ENNReal) := by
      exact
        Family8FrozenComparableActualAverageMassDensityV1.Assembly.frozenCoarse_averageMultiplicity_upper
          A
    _ <= selectorLoss * CKT := hBase
    _ <= selectorLoss * (CKT * volume (unitBallBody : Set Space)) :=
      mul_le_mul' le_rfl hCKT

#print axioms FrozenComparableSelectedCoefficientBaseBudget
#print axioms
  hRowFreshActualThirdSelectedCoefficientIncidence_of_frozenComparableBase

end
end Family8ActualThirdSelectedCoefficientFromFrozenComparableV1

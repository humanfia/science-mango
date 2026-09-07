import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerProp66Eq66ComposerV1
import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2

/-!
# Same-object Prop. 6.6 row factor to the Eq. 66 collapsed prefix

This is a scalar consumer of an existing property-ready row composer.  The
composer's actual-third parameter is literally the frozen coarse average of
the supplied assembly.  One explicit outer-prefix budget then gives exactly
the hPrefix inequality required by the Eq. 66 collapsed-prefix connector.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Prop66RowActualThirdEq66PrefixBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyActiveSelectedOwnerProp66Eq66ComposerV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

universe u v w

variable {plankIndex : Type} [Fintype plankIndex] [DecidableEq plankIndex]
variable {fineIndex : Type u} [Fintype fineIndex] [DecidableEq fineIndex]
variable {coarseIndex : Type v} [Fintype coarseIndex] [DecidableEq coarseIndex]
variable {a b delta : NNReal}

/-- The minimal same-object Prop. 6.6 input for the Eq. 66 collapsed-prefix
connector.  No Katz--Tao coefficient or card-scale mass is introduced. -/
theorem collapsedPrefix_le_sectionEight_of_propertyReadyRowProp66
    {F : ConvexFamily fineIndex} {G : ConvexFamily coarseIndex}
    (Q : ConvexFactorization F G) (Y : Shading F)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (D : ShadedConvexPlankFamily plankIndex a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card plankIndex) + 1))
    {cellIndex : Type w} (cell : cellIndex -> Set Space)
    (hcell : forall p, MeasurableSet (cell p))
    (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space)
    {epsilon beta eta gamma : Real} {M : NNReal}
    {correlationLoss collapsedPrefix outerPrefix firstLoss : ENNReal}
    {middleScale : NNReal} {middleCount : Nat}
    (Z : PropertyReadyRowProp66Eq66Composer
      D C q cell hcell selectedCells hmass hactive S
        epsilon beta eta M A.frozenCoarse.averageMultiplicity correlationLoss)
    (hCollapsed :
      collapsedPrefix <=
        outerPrefix * A.frozenCoarse.averageMultiplicity)
    (hBudget :
      outerPrefix *
          propertyReadyRowProp66Factor
            D C q cell hcell selectedCells hmass hactive S
              epsilon beta M <=
        firstLoss *
          sectionEightScaleCountFrostmanFactor
            delta middleScale middleCount gamma) :
    collapsedPrefix <=
      firstLoss *
        sectionEightScaleCountFrostmanFactor
          delta middleScale middleCount gamma := by
  calc
    collapsedPrefix <=
        outerPrefix * A.frozenCoarse.averageMultiplicity :=
      hCollapsed
    _ <= outerPrefix *
        propertyReadyRowProp66Factor
          D C q cell hcell selectedCells hmass hactive S epsilon beta M :=
      mul_le_mul' le_rfl Z.actualThirdAverage_le_prop66Factor
    _ <= firstLoss *
        sectionEightScaleCountFrostmanFactor
          delta middleScale middleCount gamma :=
      hBudget

#print axioms collapsedPrefix_le_sectionEight_of_propertyReadyRowProp66

end
end Family8Prop66RowActualThirdEq66PrefixBridgeV1

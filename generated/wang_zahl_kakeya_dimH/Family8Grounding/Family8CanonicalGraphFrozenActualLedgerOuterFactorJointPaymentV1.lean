import Family8Grounding.Family8CanonicalGraphFrozenGraphPrefixActualLedgerEq66ToDSOV1
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Family8Grounding.Family8ExactAssemblySameDataFiberBridgeV1
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Mathlib.Tactic

/-!
# Joint payment for the graph-prefix / actual-frozen ledger split

The selected graph-prefix route allocates the literal frozen-coarse average
to the third factor.  Its remaining first loss is therefore a quotient of
the reverse ledger by that same average.  On a same-assembly graph identity
the average is nonzero and finite, so the quotient-facing first/middle gate
is equivalent to one joint inequality in which the actual third occurs
exactly once.

This is only a cancellation bridge.  It does not replace the joint analytic
payment by a stronger displayed-coefficient or retained-density premise.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenActualLedgerOuterFactorJointPaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenGraphPrefixActualLedgerEq66ToDSOV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ComparableMultiplicityBucketsV1
open Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The literal third allocated by a same-assembly graph identity is
nonzero. -/
theorem sameAssembly_actualFrozenThirdLedgerLoss_ne_zero
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) :
    actualFrozenThirdLedgerLoss R.A ≠ 0 := by
  unfold actualFrozenThirdLedgerLoss Shading.averageMultiplicity
  exact ENNReal.div_ne_zero.mpr
    ⟨(by
        let Z := (IndexedShadingRefinement.restrictTo
          (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
            R.A R.k) (sameAssemblyGraph R)).shading
        have hZmass : Z.shadingMass ≠ 0 := by
          simpa only [Z] using
            sameAssemblyGraphRestriction_shadingMass_ne_zero R
        have hZvolume : volume Z.shadedUnion ≠ 0 :=
          volume_shadedUnion_ne_zero_of_shadingMass_ne_zero Z hZmass
        have hZsubsetFinal : Z.shadedUnion ⊆
            (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
              R.A R.k).shadedUnion := by
          simpa only [Z] using
            (IndexedShadingRefinement.restrictTo
              (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
                R.A R.k)
              (sameAssemblyGraph R)).shadedUnion_subset
        have hFinalSubsetRefinement :
            (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
              R.A R.k).shadedUnion ⊆
              R.A.refinement.shading.shadedUnion := by
          simpa only
            [Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading,
              Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly.fiberShading]
            using
            (IndexedShadingRefinement.restrictTo
              R.A.refinement.shading
              (P.index.fiber R.k)).shadedUnion_subset
        have hZsubsetFrozen : Z.shadedUnion ⊆
            R.A.frozenCoarse.shadedUnion :=
          hZsubsetFinal.trans
            (hFinalSubsetRefinement.trans
              R.A.shadedUnion_subset_frozenCoarse)
        have hFrozenVolume : volume R.A.frozenCoarse.shadedUnion ≠ 0 := by
          intro hzero
          apply hZvolume
          have hle : volume Z.shadedUnion ≤
              volume R.A.frozenCoarse.shadedUnion :=
            measure_mono hZsubsetFrozen
          exact le_antisymm (by simpa only [hzero] using hle) bot_le
        intro hzero
        apply hFrozenVolume
        have hle :=
          Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly.volume_shadedUnion_le_shadingMass
            R.A.frozenCoarse
        exact le_antisymm (by simpa only [hzero] using hle) bot_le),
      volume_shadedUnion_ne_top R.A.frozenCoarse⟩

/-- The literal third allocated by a same-assembly graph identity is
finite. -/
theorem sameAssembly_actualFrozenThirdLedgerLoss_ne_top
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) :
    actualFrozenThirdLedgerLoss R.A ≠ ∞ := by
  intro htop
  have hupper := frozenCoarse_averageMultiplicity_upper R.A
  have htop' : R.A.frozenCoarse.averageMultiplicity = (⊤ : ENNReal) := by
    simpa only [actualFrozenThirdLedgerLoss] using htop
  rw [htop'] at hupper
  exact ENNReal.natCast_ne_top _ (top_unique hupper)

/-- On the literal same assembly, paying the residual quotient is
equivalent to paying the first/middle factor jointly with the actual third.
The latter form exposes the exact scalar inequality that an exponent ledger
must produce and prevents a second use of the frozen average. -/
theorem outerFactor_le_residual_iff_jointActualThird
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (outerFactor middleFactor : ENNReal) :
    outerFactor ≤ residualFirstLedgerLoss ledger R.A * middleFactor ↔
      outerFactor * actualFrozenThirdLedgerLoss R.A ≤
        cumulativeReverseLoss ledger * middleFactor := by
  have hthird0 := sameAssembly_actualFrozenThirdLedgerLoss_ne_zero R
  have hthirdTop := sameAssembly_actualFrozenThirdLedgerLoss_ne_top R
  constructor
  · intro h
    calc
      outerFactor * actualFrozenThirdLedgerLoss R.A ≤
          (residualFirstLedgerLoss ledger R.A * middleFactor) *
            actualFrozenThirdLedgerLoss R.A :=
        mul_le_mul' h le_rfl
      _ = (residualFirstLedgerLoss ledger R.A *
            actualFrozenThirdLedgerLoss R.A) * middleFactor := by
        ac_rfl
      _ ≤ cumulativeReverseLoss ledger * middleFactor :=
        mul_le_mul'
          (residualFirst_mul_actualFrozenThird_le_reverse ledger R.A) le_rfl
  · intro h
    have hcancel :
        (residualFirstLedgerLoss ledger R.A * middleFactor) *
            actualFrozenThirdLedgerLoss R.A =
          cumulativeReverseLoss ledger * middleFactor := by
      rw [residualFirstLedgerLoss]
      calc
        ((cumulativeReverseLoss ledger /
              actualFrozenThirdLedgerLoss R.A) * middleFactor) *
            actualFrozenThirdLedgerLoss R.A =
          ((cumulativeReverseLoss ledger /
              actualFrozenThirdLedgerLoss R.A) *
            actualFrozenThirdLedgerLoss R.A) * middleFactor := by
              ac_rfl
        _ = cumulativeReverseLoss ledger * middleFactor := by
          rw [ENNReal.div_mul_cancel hthird0 hthirdTop]
    apply (ENNReal.mul_le_mul_iff_right hthird0 hthirdTop).mp
    calc
      actualFrozenThirdLedgerLoss R.A * outerFactor =
          outerFactor * actualFrozenThirdLedgerLoss R.A := by
        ac_rfl
      _ ≤ cumulativeReverseLoss ledger * middleFactor := h
      _ = actualFrozenThirdLedgerLoss R.A *
          (residualFirstLedgerLoss ledger R.A * middleFactor) := by
        rw [← hcancel]
        ac_rfl

/-- Exact specialization of the joint cancellation to the sole
first/middle premise consumed by the graph-prefix DSO connector. -/
theorem sameGraphEq66OuterPrefix_mul_rowFactor_le_residual_of_jointActualThird
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    {delta : NNReal} (firstCap : ENNReal) (lossEta : Real)
    (rowFactor middleFactor : ENNReal)
    (hJoint :
      (sameGraphEq66OuterPrefix (delta := delta) R firstCap lossEta *
          rowFactor) * actualFrozenThirdLedgerLoss R.A ≤
        cumulativeReverseLoss ledger * middleFactor) :
    sameGraphEq66OuterPrefix (delta := delta) R firstCap lossEta *
        rowFactor ≤
      residualFirstLedgerLoss ledger R.A * middleFactor := by
  exact (outerFactor_le_residual_iff_jointActualThird ledger R
    (sameGraphEq66OuterPrefix (delta := delta) R firstCap lossEta * rowFactor)
    middleFactor).2 hJoint

#print axioms sameAssembly_actualFrozenThirdLedgerLoss_ne_zero
#print axioms sameAssembly_actualFrozenThirdLedgerLoss_ne_top
#print axioms outerFactor_le_residual_iff_jointActualThird
#print axioms
  sameGraphEq66OuterPrefix_mul_rowFactor_le_residual_of_jointActualThird

end
end Family8CanonicalGraphFrozenActualLedgerOuterFactorJointPaymentV1

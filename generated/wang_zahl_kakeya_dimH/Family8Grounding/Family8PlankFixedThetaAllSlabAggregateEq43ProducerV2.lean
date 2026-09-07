import Family8Grounding.Family8PlankFixedThetaAllSlabAssemblyV1
import Family8Grounding.Family8AllSlabRowPowerAlgebraV1
import Mathlib.Tactic

/-!
# Aggregate row-dependent Eq. (43) producer for all fixed-theta slabs

This is the weak all-row form of the Eq. (43)/Family 7 cancellation.  The
restriction loss is explicit, and the Family 7 base may vary from row to
row.  No row is declared good merely because it belongs to the slab
catalogue.  Instead, the one genuinely global input is a lower bound for the
row-base-weighted mass sum.

The older common-base certificate remains useful as a specialization.  This
module does not depend on that stronger conclusion: it sums the exact
row-dependent inequalities directly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankFixedThetaAllSlabAggregateEq43ProducerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6AffineConvexVolumeCoreV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankFixedThetaAllSlabRowsV1
open Family8PlankFixedThetaAllSlabAssemblyV1
open Family8AllSlabRowPowerAlgebraV1

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- Honest raw certificate for the all-row Eq. (43)/Family 7 estimate.

For `G` the global thick-owner family mass, `m r` the actual mass of row
`r`, and `w r` its inverse affine Jacobian, the two local inputs are

`rowCF r <= restrictionLoss * sourceCF * w r * (G / m r)`

and the normalized Family 7 union lower with the row-dependent coefficient
`rowBase r`.  The last field is the only good-row/popularity input: it says
that those varying bases retain `aggregateBase` on average with respect to
the actual row masses.

Neither `restrictionLoss` nor `sourceCF` is required to be nonzero.  Only
their finiteness is used to distribute the negative real power. -/
structure FixedThetaAllSlabRawAggregateEq43Certificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space)
    (restrictionLoss sourceCF : ENNReal) (beta : Real) where
  rowCF : rowIndex -> ENNReal
  rowBase : rowIndex -> ENNReal
  aggregateBase : ENNReal
  restrictionLoss_ne_top : restrictionLoss ≠ ⊤
  sourceCF_ne_top : sourceCF ≠ ⊤
  globalMass_ne_zero :
    familyVolume (heavyRetainedOwnerThickenedFamily D C q) ≠ 0
  rowMass_ne_zero : forall r,
    familyVolume (R.rowFamily r) ≠ 0
  beta_nonnegative : 0 <= beta
  beta_le_two : beta <= 2
  aggregate_base_mass_floor :
    aggregateBase *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) <=
      ∑ r : rowIndex, rowBase r * familyVolume (R.rowFamily r)
  eq43_rowCF_le : forall r,
    rowCF r <=
      restrictionLoss * sourceCF *
        inverseAffineJacobianRowWeight normalize r *
          (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
            familyVolume (R.rowFamily r))
  family7_row_union_lower : forall r,
    rowBase r * rowCF r ^ (-(1 - beta / 2)) *
        (familyVolume (R.rowFamily r) /
          inverseAffineJacobianRowWeight normalize r) ^ (beta / 2) <=
      affineNormalizedRowUnion R normalize r

/-- Exact cancellation on one row, now with both the explicit restriction
loss and the row-dependent Family 7 base. -/
theorem FixedThetaAllSlabRawAggregateEq43Certificate.weighted_row_lower
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    {restrictionLoss sourceCF : ENNReal} {beta : Real}
    (H : FixedThetaAllSlabRawAggregateEq43Certificate
      R normalize restrictionLoss sourceCF beta)
    (r : rowIndex) :
    H.rowBase r *
        ((restrictionLoss * sourceCF) ^ (-(1 - beta / 2)) *
          familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
            (-(1 - beta / 2)) *
          familyVolume (R.rowFamily r)) <=
      inverseAffineJacobianRowWeight normalize r *
        affineNormalizedRowUnion R normalize r := by
  let globalMass : ENNReal :=
    familyVolume (heavyRetainedOwnerThickenedFamily D C q)
  let rowMass : ENNReal := familyVolume (R.rowFamily r)
  let rowWeight : ENNReal := inverseAffineJacobianRowWeight normalize r
  have hEffectiveTop : restrictionLoss * sourceCF ≠ ⊤ :=
    ENNReal.mul_ne_top H.restrictionLoss_ne_top H.sourceCF_ne_top
  have hGlobalTop : globalMass ≠ ⊤ := by
    exact familyVolume_ne_top
      (heavyRetainedOwnerThickenedFamily D C q)
  have hRowTop : rowMass ≠ ⊤ := by
    exact familyVolume_ne_top (R.rowFamily r)
  have hWeight0 : rowWeight ≠ 0 := by
    simp [rowWeight, inverseAffineJacobianRowWeight,
      affineJacobian_ne_top]
  have hWeightTop : rowWeight ≠ ⊤ := by
    simp [rowWeight, inverseAffineJacobianRowWeight,
      (affineJacobian_pos (normalize r)).ne']
  have hEq43 :
      H.rowCF r <=
        (restrictionLoss * sourceCF) * rowWeight * globalMass / rowMass := by
    simpa only [globalMass, rowMass, rowWeight, mul_div_assoc, mul_assoc]
      using H.eq43_rowCF_le r
  have hFamily7 :
      H.rowBase r * H.rowCF r ^ (-(1 - beta / 2)) *
          (rowMass / rowWeight) ^ (beta / 2) <=
        affineNormalizedRowUnion R normalize r := by
    simpa only [rowMass, rowWeight] using H.family7_row_union_lower r
  have hWeighted := allSlab_weighted_rowLower
    (restrictionLoss * sourceCF) globalMass rowMass rowWeight
      (H.rowCF r) (H.rowBase r)
      (affineNormalizedRowUnion R normalize r) beta
      hEffectiveTop hGlobalTop
      (H.rowMass_ne_zero r) hRowTop
      hWeight0 hWeightTop
      H.beta_nonnegative H.beta_le_two hEq43 hFamily7
  simpa only [globalMass, rowMass, mul_assoc] using hWeighted

/-- Summing the row inequalities uses only the aggregate base-mass floor.
This is the precise replacement for an unsupported uniform lower bound on
every slab row. -/
theorem FixedThetaAllSlabRawAggregateEq43Certificate.aggregate_negativePower_le_weightedRows
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    {restrictionLoss sourceCF : ENNReal} {beta : Real}
    (H : FixedThetaAllSlabRawAggregateEq43Certificate
      R normalize restrictionLoss sourceCF beta) :
    H.aggregateBase *
        (restrictionLoss * sourceCF) ^ (-(1 - beta / 2)) *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
          (-(1 - beta / 2)) *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) <=
      ∑ r : rowIndex,
        inverseAffineJacobianRowWeight normalize r *
          affineNormalizedRowUnion R normalize r := by
  let common : ENNReal :=
    (restrictionLoss * sourceCF) ^ (-(1 - beta / 2)) *
      familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
        (-(1 - beta / 2))
  calc
    H.aggregateBase *
          (restrictionLoss * sourceCF) ^ (-(1 - beta / 2)) *
          familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
            (-(1 - beta / 2)) *
          familyVolume (heavyRetainedOwnerThickenedFamily D C q) =
        common *
          (H.aggregateBase *
            familyVolume (heavyRetainedOwnerThickenedFamily D C q)) := by
      simp only [common]
      ac_rfl
    _ <= common *
        (∑ r : rowIndex, H.rowBase r * familyVolume (R.rowFamily r)) :=
      mul_le_mul' le_rfl H.aggregate_base_mass_floor
    _ = ∑ r : rowIndex,
        H.rowBase r *
          ((restrictionLoss * sourceCF) ^ (-(1 - beta / 2)) *
            familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
              (-(1 - beta / 2)) *
            familyVolume (R.rowFamily r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [common]
      ac_rfl
    _ <= ∑ r : rowIndex,
        inverseAffineJacobianRowWeight normalize r *
          affineNormalizedRowUnion R normalize r :=
      Finset.sum_le_sum fun r _hr => H.weighted_row_lower r

/-- Final aggregate lower bound.  The explicit restriction loss is paid
once through `(restrictionLoss * sourceCF)^(-p)`, and the exact global row
mass sum leaves the expected `G^(beta/2)` factor. -/
theorem FixedThetaAllSlabRawAggregateEq43Certificate.aggregateBase_halfPower_le_weightedRows
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    {restrictionLoss sourceCF : ENNReal} {beta : Real}
    (H : FixedThetaAllSlabRawAggregateEq43Certificate
      R normalize restrictionLoss sourceCF beta) :
    H.aggregateBase *
        (restrictionLoss * sourceCF) ^ (-(1 - beta / 2)) *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
          (beta / 2) <=
      ∑ r : rowIndex,
        inverseAffineJacobianRowWeight normalize r *
          affineNormalizedRowUnion R normalize r := by
  calc
    H.aggregateBase *
          (restrictionLoss * sourceCF) ^ (-(1 - beta / 2)) *
          familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
            (beta / 2) =
        H.aggregateBase *
          (restrictionLoss * sourceCF) ^ (-(1 - beta / 2)) *
          familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
            (-(1 - beta / 2)) *
          familyVolume (heavyRetainedOwnerThickenedFamily D C q) := by
      exact (allSlab_commonCoefficient_globalMass_identity
        (restrictionLoss * sourceCF)
        (familyVolume (heavyRetainedOwnerThickenedFamily D C q))
        H.aggregateBase beta H.globalMass_ne_zero
        (familyVolume_ne_top
          (heavyRetainedOwnerThickenedFamily D C q))).symm
    _ <= ∑ r : rowIndex,
        inverseAffineJacobianRowWeight normalize r *
          affineNormalizedRowUnion R normalize r :=
      H.aggregate_negativePower_le_weightedRows

#print axioms FixedThetaAllSlabRawAggregateEq43Certificate.weighted_row_lower
#print axioms
  FixedThetaAllSlabRawAggregateEq43Certificate.aggregate_negativePower_le_weightedRows
#print axioms
  FixedThetaAllSlabRawAggregateEq43Certificate.aggregateBase_halfPower_le_weightedRows

end
end Family8PlankFixedThetaAllSlabAggregateEq43ProducerV2

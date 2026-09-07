import Family8Grounding.Family8PlankFixedThetaAllSlabAssemblyV1
import Family8Grounding.Family8AllSlabRowPowerAlgebraV1
import Mathlib.Tactic

/-!
# Row-dependent Eq. (43) producer for the fixed-theta all-slab sum

This file supplies the missing algebraic bridge from the literal rowwise
Eq. (43) and Family 7 estimates to the mass-weighted interface used by the
all-slab assembly.  The restriction loss is allowed to depend on the actual
row mass: no uniform lower bound or comparability between different rows is
assumed.

The reconstruction weight and normalized row union are the canonical ones
coming from a chosen affine equivalence for each row.  Their Jacobian factors
then cancel exactly in the scalar row-power lemma.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankFixedThetaAllSlabMassWeightedEq43ProducerV1

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

/-- Raw row-dependent analytic input for the all-slab Eq. (43) argument.

For a row of mass `m`, Eq. (43) is allowed the full restriction loss
`globalMass / m`.  Family 7 is then applied to that row with its own Frostman
constant and normalized row volume `m / rowWeight`.  The only cancellability
assumptions retained here are positivity of the relevant masses and
finiteness of the source Frostman constant.  Finiteness of family
volumes and of the canonical inverse-Jacobian row weights is automatic. -/
structure FixedThetaAllSlabRawRowDependentEq43Certificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space)
    (sourceCF rowBase : ENNReal) (beta : Real) where
  rowCF : rowIndex -> ENNReal
  sourceCF_ne_top : sourceCF ≠ ⊤
  globalMass_ne_zero :
    familyVolume (heavyRetainedOwnerThickenedFamily D C q) ≠ 0
  rowMass_ne_zero : forall r,
    familyVolume (R.rowFamily r) ≠ 0
  beta_nonnegative : 0 <= beta
  beta_le_two : beta <= 2
  eq43_rowCF_le : forall r,
    rowCF r <=
      sourceCF * inverseAffineJacobianRowWeight normalize r *
        (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
          familyVolume (R.rowFamily r))
  family7_row_union_lower : forall r,
    rowBase * rowCF r ^ (-(1 - beta / 2)) *
        (familyVolume (R.rowFamily r) /
          inverseAffineJacobianRowWeight normalize r) ^ (beta / 2) <=
      affineNormalizedRowUnion R normalize r

/-- The raw row-dependent Eq. (43) and Family 7 inputs produce precisely the
mass-weighted certificate consumed by the global all-slab assembly.

The output coefficient is independent of the row.  All dependence on the
actual row mass is linear on the left, so exact sigma-summation recovers the
global thick-owner family mass. -/
def FixedThetaAllSlabRawRowDependentEq43Certificate.toMassWeightedEq43Certificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    {sourceCF rowBase : ENNReal} {beta : Real}
    (H : FixedThetaAllSlabRawRowDependentEq43Certificate
      R normalize sourceCF rowBase beta) :
    FixedThetaAllSlabRowMassWeightedEq43Certificate R
      (rowBase * sourceCF ^ (-(1 - beta / 2)) *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
          (-(1 - beta / 2))) := by
  let globalMass : ENNReal :=
    familyVolume (heavyRetainedOwnerThickenedFamily D C q)
  refine
    { rowWeight := inverseAffineJacobianRowWeight normalize
      normalizedRowUnion := affineNormalizedRowUnion R normalize
      row_mass_lower := ?_ }
  intro r
  let rowMass : ENNReal := familyVolume (R.rowFamily r)
  let rowWeight : ENNReal := inverseAffineJacobianRowWeight normalize r
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
      H.rowCF r <= sourceCF * rowWeight * globalMass / rowMass := by
    simpa only [globalMass, rowMass, rowWeight, mul_div_assoc] using
      H.eq43_rowCF_le r
  have hFamily7 :
      rowBase * H.rowCF r ^ (-(1 - beta / 2)) *
          (rowMass / rowWeight) ^ (beta / 2) <=
        affineNormalizedRowUnion R normalize r := by
    simpa only [rowMass, rowWeight] using H.family7_row_union_lower r
  have hWeighted := allSlab_weighted_rowLower
    sourceCF globalMass rowMass rowWeight (H.rowCF r) rowBase
      (affineNormalizedRowUnion R normalize r) beta
      H.sourceCF_ne_top hGlobalTop
      (H.rowMass_ne_zero r) hRowTop
      hWeight0 hWeightTop
      H.beta_nonnegative H.beta_le_two hEq43 hFamily7
  simpa only [globalMass, rowMass, mul_assoc] using hWeighted

/-- After the exact row-mass partition is summed, the remaining global-mass
factor has exponent `beta / 2`.  This is the advertised final local core,
with no residual row mass or affine-Jacobian weight. -/
theorem allSlab_massWeightedLocalCore_eq_halfPower
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    (sourceCF rowBase : ENNReal) (beta : Real)
    (hGlobal0 :
      familyVolume (heavyRetainedOwnerThickenedFamily D C q) ≠ 0) :
    rowBase * sourceCF ^ (-(1 - beta / 2)) *
          familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
            (-(1 - beta / 2)) *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) =
      rowBase * sourceCF ^ (-(1 - beta / 2)) *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
          (beta / 2) := by
  exact allSlab_commonCoefficient_globalMass_identity
    sourceCF (familyVolume (heavyRetainedOwnerThickenedFamily D C q))
      rowBase beta hGlobal0
      (familyVolume_ne_top
        (heavyRetainedOwnerThickenedFamily D C q))

/-- Direct summed consequence in the final `beta / 2` form. -/
theorem FixedThetaAllSlabRawRowDependentEq43Certificate.halfPower_le_weightedRows
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    {sourceCF rowBase : ENNReal} {beta : Real}
    (H : FixedThetaAllSlabRawRowDependentEq43Certificate
      R normalize sourceCF rowBase beta) :
    rowBase * sourceCF ^ (-(1 - beta / 2)) *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) ^
          (beta / 2) <=
      ∑ r : rowIndex,
        inverseAffineJacobianRowWeight normalize r *
          affineNormalizedRowUnion R normalize r := by
  let M := H.toMassWeightedEq43Certificate
  have hAggregate := M.aggregate_rows_lower
  rw [allSlab_massWeightedLocalCore_eq_halfPower
    sourceCF rowBase beta H.globalMass_ne_zero] at hAggregate
  simpa only [M,
    FixedThetaAllSlabRawRowDependentEq43Certificate.toMassWeightedEq43Certificate]
    using hAggregate

#print axioms FixedThetaAllSlabRawRowDependentEq43Certificate.toMassWeightedEq43Certificate
#print axioms allSlab_massWeightedLocalCore_eq_halfPower
#print axioms FixedThetaAllSlabRawRowDependentEq43Certificate.halfPower_le_weightedRows

end
end Family8PlankFixedThetaAllSlabMassWeightedEq43ProducerV1

import Family8Grounding.Family8PlankFixedThetaAllSlabRowsV1
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
import Mathlib.Tactic

/-!
# Fixed-theta all-slab Jacobian and overlap assembly

This file discharges the shorter, global half of the all-slab cancellation
certificate.  Each physical row shaded union is regarded as one measurable
shading carrier inside its catalogue slab.  Consequently a pointwise bound
on the number of row unions through a point integrates, by the existing
`Shading.pointMultiplicity` lemma, to the required bound for the sum of row
union volumes.

The only geometric input to this half is then the rowwise affine-Jacobian
comparison between the normalized row volume and its physical row union.
The Eq. (43) Frostman/Family 7 lower estimate is kept in a separate structure
and is not assumed by the global assembly certificate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankFixedThetaAllSlabAssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6AffineConvexVolumeCoreV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankFixedThetaAllSlabRowsV1

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- Regard the union in each fixed-theta slab row as one shading carrier.

The ambient body for row `r` is its catalogue slab.  This packaging loses no
set-theoretic information; it exists only so that the repository's generic
finite-shading point-multiplicity integration theorem applies verbatim. -/
def rowUnionShading
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant) :
    Shading R.slab where
  carrier r := (R.rowShading r).shadedUnion
  measurable_carrier r := (R.rowShading r).shadedUnion_measurableSet
  carrier_subset r := by
    intro x hx
    obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
    exact R.rowFamily_subset_slab r s
      ((R.rowShading r).carrier_subset s hxs)

@[simp] theorem rowUnionShading_carrier
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) :
    (rowUnionShading R).carrier r = (R.rowShading r).shadedUnion := rfl

/-- The row-union shading has exactly the global thick-owner shaded union. -/
theorem rowUnionShading_shadedUnion_eq_globalCoarse
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant) :
    (rowUnionShading R).shadedUnion =
      (heavyRetainedOwnerThickenedShading D C q).shadedUnion := by
  simpa only [Shading.shadedUnion,
    rowUnionShading_carrier] using
    R.iUnion_rowShadedUnion_eq_globalCoarse

/-- The mass of the row-union shading is literally the sum of physical row
union volumes. -/
theorem rowUnionShading_shadingMass
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant) :
    (rowUnionShading R).shadingMass =
      ∑ r : rowIndex, volume ((R.rowShading r).shadedUnion) := rfl

/-- The normalized union scalar obtained by sending one physical row union
through a chosen affine equivalence. -/
def affineNormalizedRowUnion
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space)
    (r : rowIndex) : ENNReal :=
  volume (normalize r '' (R.rowShading r).shadedUnion)

/-- Physical reconstruction weight for a chosen affine normalization. -/
def inverseAffineJacobianRowWeight
    {rowIndex : Type v}
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space)
    (r : rowIndex) : ENNReal :=
  (affineJacobian (normalize r))⁻¹

/-- The inverse Jacobian cancels the normalized row-union volume exactly.
Thus no Jacobian inequality has to be postulated once the actual affine map
and the literal image union are used. -/
theorem inverseAffineJacobian_mul_affineNormalizedRowUnion
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space)
    (r : rowIndex) :
    inverseAffineJacobianRowWeight normalize r *
        affineNormalizedRowUnion R normalize r =
      volume ((R.rowShading r).shadedUnion) := by
  rw [inverseAffineJacobianRowWeight, affineNormalizedRowUnion,
    volume_image_affineEquiv]
  exact ENNReal.inv_mul_cancel_left
    (affineJacobian_pos (normalize r)).ne'
    (affineJacobian_ne_top (normalize r))

/-- A bounded number of physical slab-row unions through each point bounds
the sum of row union volumes by that multiplicity times the global union.

This is the bounded-overlap part of Lemma 6.13, derived rather than stored as
an aggregate measure inequality. -/
theorem sum_rowShadedUnion_volume_le_of_pointMultiplicity
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (overlapCap : Nat)
    (hOverlap : forall x,
      (rowUnionShading R).pointMultiplicity x <= overlapCap) :
    (∑ r : rowIndex, volume ((R.rowShading r).shadedUnion)) <=
      (overlapCap : ENNReal) *
        volume ((heavyRetainedOwnerThickenedShading D C q).shadedUnion) := by
  have hmass :=
    ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
      (rowUnionShading R) overlapCap hOverlap
  rw [rowUnionShading_shadingMass R,
    rowUnionShading_shadedUnion_eq_globalCoarse R] at hmass
  simpa only [nsmul_eq_mul] using hmass

/-- The remaining local analytic half: Eq. (43), the normalized Family 7
row estimates, and their finite summation.  No Jacobian or overlap premise is
stored here. -/
structure FixedThetaAllSlabEq43RowsLowerCertificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (_R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (localCore : ENNReal) where
  rowWeight : rowIndex -> ENNReal
  normalizedRowUnion : rowIndex -> ENNReal
  totalWeight : ENNReal
  totalWeight_ne_zero : totalWeight ≠ 0
  totalWeight_ne_top : totalWeight ≠ ⊤
  weight_sum : (∑ r : rowIndex, rowWeight r) = totalWeight
  eq43_family7_rows_lower :
    totalWeight * (localCore / totalWeight) <=
      ∑ r : rowIndex, rowWeight r * normalizedRowUnion r

/-- Mass-weighted, row-dependent form of the Eq. (43)/Family 7 output.

The row lower bound is linear in the *actual* row family volume.  This is
strictly weaker than imposing one common lower bound on every row, and is the
form produced after the factors `globalMass / rowMass` and the inverse
Jacobian cancel with the two Family 7 volume powers. -/
structure FixedThetaAllSlabRowMassWeightedEq43Certificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (localCoefficient : ENNReal) where
  rowWeight : rowIndex -> ENNReal
  normalizedRowUnion : rowIndex -> ENNReal
  row_mass_lower : forall r,
    localCoefficient * familyVolume (R.rowFamily r) <=
      rowWeight r * normalizedRowUnion r

/-- Exact summation of the row-dependent lower bounds: the sigma mass
partition turns their row-mass factor back into the global thick-owner mass.
-/
theorem FixedThetaAllSlabRowMassWeightedEq43Certificate.aggregate_rows_lower
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {localCoefficient : ENNReal}
    (H : FixedThetaAllSlabRowMassWeightedEq43Certificate
      R localCoefficient) :
    localCoefficient *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) <=
      ∑ r : rowIndex, H.rowWeight r * H.normalizedRowUnion r := by
  calc
    localCoefficient *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) =
        localCoefficient *
          (∑ r : rowIndex, familyVolume (R.rowFamily r)) := by
      rw [R.familyVolume_eq_sum_rowFamily_familyVolume]
    _ = ∑ r : rowIndex,
        localCoefficient * familyVolume (R.rowFamily r) := by
      rw [Finset.mul_sum]
    _ <= ∑ r : rowIndex,
        H.rowWeight r * H.normalizedRowUnion r :=
      Finset.sum_le_sum fun r _hr => H.row_mass_lower r

/-- Convert the honest mass-weighted row output to the aggregate Eq. (43)
interface.  The only extra conditions are that the sum of reconstruction
weights is cancellable; no row-comparability or uniform row lower bound is
introduced. -/
def FixedThetaAllSlabRowMassWeightedEq43Certificate.toRowsLowerCertificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {localCoefficient : ENNReal}
    (H : FixedThetaAllSlabRowMassWeightedEq43Certificate
      R localCoefficient)
    (hweight0 : (∑ r : rowIndex, H.rowWeight r) ≠ 0)
    (hweightTop : (∑ r : rowIndex, H.rowWeight r) ≠ ⊤) :
    FixedThetaAllSlabEq43RowsLowerCertificate R
      (localCoefficient *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q)) where
  rowWeight := H.rowWeight
  normalizedRowUnion := H.normalizedRowUnion
  totalWeight := ∑ r : rowIndex, H.rowWeight r
  totalWeight_ne_zero := hweight0
  totalWeight_ne_top := hweightTop
  weight_sum := rfl
  eq43_family7_rows_lower := by
    rw [ENNReal.mul_div_cancel hweight0 hweightTop]
    exact H.aggregate_rows_lower

/-- Weak geometric certificate for the global half.

`row_jacobian_le` is the per-row change-of-variables comparison.  The second
field is only a pointwise finite-overlap cap for the physical row unions; the
aggregate assembly inequality is a theorem below. -/
structure FixedThetaAllSlabJacobianOverlapCertificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (rowWeight normalizedRowUnion : rowIndex -> ENNReal)
    (jacobianLoss : ENNReal) (overlapCap : Nat) where
  row_jacobian_le : forall r,
    rowWeight r * normalizedRowUnion r <=
      jacobianLoss * volume ((R.rowShading r).shadedUnion)
  row_pointMultiplicity_le : forall x,
    (rowUnionShading R).pointMultiplicity x <= overlapCap

/-- A chosen affine equivalence for every row produces the Jacobian part of
the global certificate with loss exactly one.  Only bounded overlap of the
physical row unions remains as an input. -/
theorem affineNormalizationJacobianOverlapCertificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space)
    (overlapCap : Nat)
    (hOverlap : forall x,
      (rowUnionShading R).pointMultiplicity x <= overlapCap) :
    FixedThetaAllSlabJacobianOverlapCertificate R
      (inverseAffineJacobianRowWeight normalize)
      (affineNormalizedRowUnion R normalize) 1 overlapCap where
  row_jacobian_le r := by
    rw [one_mul]
    exact (inverseAffineJacobian_mul_affineNormalizedRowUnion
      R normalize r).le
  row_pointMultiplicity_le := hOverlap

/-- The Jacobian comparison and pointwise row-overlap cap imply the exact
aggregate upper inequality needed by all-slab cancellation. -/
theorem FixedThetaAllSlabJacobianOverlapCertificate.weighted_rows_le_global
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {rowWeight normalizedRowUnion : rowIndex -> ENNReal}
    {jacobianLoss : ENNReal} {overlapCap : Nat}
    (J : FixedThetaAllSlabJacobianOverlapCertificate R
      rowWeight normalizedRowUnion jacobianLoss overlapCap) :
    (∑ r : rowIndex, rowWeight r * normalizedRowUnion r) <=
      (jacobianLoss * (overlapCap : ENNReal)) *
        volume ((heavyRetainedOwnerThickenedShading D C q).shadedUnion) := by
  calc
    (∑ r : rowIndex, rowWeight r * normalizedRowUnion r) <=
        ∑ r : rowIndex,
          jacobianLoss * volume ((R.rowShading r).shadedUnion) :=
      Finset.sum_le_sum fun r _hr => J.row_jacobian_le r
    _ = jacobianLoss *
        (∑ r : rowIndex, volume ((R.rowShading r).shadedUnion)) := by
      rw [Finset.mul_sum]
    _ <= jacobianLoss *
        ((overlapCap : ENNReal) *
          volume ((heavyRetainedOwnerThickenedShading D C q).shadedUnion)) :=
      mul_le_mul' le_rfl
        (sum_rowShadedUnion_volume_le_of_pointMultiplicity R
          overlapCap J.row_pointMultiplicity_le)
    _ = (jacobianLoss * (overlapCap : ENNReal)) *
        volume ((heavyRetainedOwnerThickenedShading D C q).shadedUnion) := by
      rw [mul_assoc]

/-- Combine the isolated Eq. (43)/Family 7 lower certificate with the now
proved Jacobian-overlap assembly half. -/
def FixedThetaAllSlabEq43RowsLowerCertificate.toAssemblyObligation
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {localCore jacobianLoss : ENNReal} {overlapCap : Nat}
    (H : FixedThetaAllSlabEq43RowsLowerCertificate R localCore)
    (J : FixedThetaAllSlabJacobianOverlapCertificate R
      H.rowWeight H.normalizedRowUnion jacobianLoss overlapCap) :
    FixedThetaAllSlabEq43AssemblyObligation R localCore
      (jacobianLoss * (overlapCap : ENNReal)) where
  rowWeight := H.rowWeight
  normalizedRowUnion := H.normalizedRowUnion
  totalWeight := H.totalWeight
  totalWeight_ne_zero := H.totalWeight_ne_zero
  totalWeight_ne_top := H.totalWeight_ne_top
  weight_sum := H.weight_sum
  eq43_family7_rows_lower := H.eq43_family7_rows_lower
  jacobian_rows_le_global := J.weighted_rows_le_global

/-- End-to-end cancellation once only the Eq. (43) lower certificate and the
weak concrete global geometry certificate have been supplied. -/
theorem FixedThetaAllSlabEq43RowsLowerCertificate.localCore_le_globalCoarse
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {localCore jacobianLoss : ENNReal} {overlapCap : Nat}
    (H : FixedThetaAllSlabEq43RowsLowerCertificate R localCore)
    (J : FixedThetaAllSlabJacobianOverlapCertificate R
      H.rowWeight H.normalizedRowUnion jacobianLoss overlapCap) :
    localCore <= (jacobianLoss * (overlapCap : ENNReal)) *
      volume ((heavyRetainedOwnerThickenedShading D C q).shadedUnion) :=
  (H.toAssemblyObligation J).localCore_le_globalCoarse

#print axioms rowUnionShading_shadedUnion_eq_globalCoarse
#print axioms rowUnionShading_shadingMass
#print axioms inverseAffineJacobian_mul_affineNormalizedRowUnion
#print axioms sum_rowShadedUnion_volume_le_of_pointMultiplicity
#print axioms FixedThetaAllSlabRowMassWeightedEq43Certificate.aggregate_rows_lower
#print axioms FixedThetaAllSlabRowMassWeightedEq43Certificate.toRowsLowerCertificate
#print axioms affineNormalizationJacobianOverlapCertificate
#print axioms FixedThetaAllSlabJacobianOverlapCertificate.weighted_rows_le_global
#print axioms FixedThetaAllSlabEq43RowsLowerCertificate.toAssemblyObligation
#print axioms FixedThetaAllSlabEq43RowsLowerCertificate.localCore_le_globalCoarse

end
end Family8PlankFixedThetaAllSlabAssemblyV1

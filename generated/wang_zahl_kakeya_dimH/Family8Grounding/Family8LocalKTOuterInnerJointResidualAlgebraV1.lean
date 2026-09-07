import Family8Grounding.Family8Prop66ASectionEightCollapsedAlgebraV1
import Family8Grounding.Family8SelectedParentAdaptiveInnerSourceReserveV1
import Mathlib.Tactic

/-!
# The exact joint residual for a local Katz--Tao coefficient

If the local adaptive cap is built from `KT`, the Proposition 6.6(A) inner
factor retains `KT^(1-gamma/2)`, while the Cordoba estimate is linear in
`KT`.  The exact uncancelled factor is therefore `KT^(gamma/2)`.  This file
records that loss without replacing it by a global delta-power envelope.

It also records the precise inverse density which an outer coefficient would
need in order to cancel this residual: `KT^(-gamma/(2-gamma))`.  After the
outer exponent `1-gamma/2` is applied, this becomes `KT^(-gamma/2)`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8LocalKTOuterInnerJointResidualAlgebraV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66ASectionEightCollapsedAlgebraV1
open Family8SelectedParentAdaptiveInnerSourceReserveV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-- Pure exact ledger: after an inner reserve has retained
`KT^(1-gamma/2)`, the weakest remaining comparison for a linear `KT` factor
contains exactly `KT^(gamma/2)`. -/
theorem linearKT_mul_fixed_le_sourcePower_mul_inner_of_jointResidual
    {KT fixed sourcePower scaleReserve inner : ENNReal} {gamma : Real}
    (hKT0 : KT ≠ 0) (hKTTop : KT ≠ ∞)
    (hinnerReserve :
      scaleReserve * KT ^ (1 - gamma / 2) <= inner)
    (hjointResidual :
      KT ^ (gamma / 2) * fixed <= sourcePower * scaleReserve) :
    KT * fixed <= sourcePower * inner := by
  have hsplit :
      KT = KT ^ (gamma / 2) * KT ^ (1 - gamma / 2) := by
    calc
      KT = KT ^ (1 : Real) := by rw [ENNReal.rpow_one]
      _ = KT ^ ((gamma / 2) + (1 - gamma / 2)) := by
        congr 1
        ring
      _ = KT ^ (gamma / 2) * KT ^ (1 - gamma / 2) :=
        ENNReal.rpow_add (gamma / 2) (1 - gamma / 2) hKT0 hKTTop
  calc
    KT * fixed =
        (KT ^ (gamma / 2) * KT ^ (1 - gamma / 2)) * fixed :=
      congrArg (fun x : ENNReal => x * fixed) hsplit
    _ = (KT ^ (gamma / 2) * fixed) * KT ^ (1 - gamma / 2) := by
      ac_rfl
    _ <= (sourcePower * scaleReserve) * KT ^ (1 - gamma / 2) :=
      mul_le_mul' hjointResidual le_rfl
    _ = sourcePower *
        (scaleReserve * KT ^ (1 - gamma / 2)) := by ac_rfl
    _ <= sourcePower * inner := mul_le_mul' le_rfl hinnerReserve

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Same-object specialization to the actual selected bucket.  Unlike a
global power envelope, the premise retains the exact local `KT^(gamma/2)`
and the exact scale/aspect reserve, so an outer density argument may cancel
them jointly. -/
theorem selectedParent_linearKT_mul_fixed_le_sourcePower_mul_adaptiveInner_of_jointResidual
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : SelectedBucketOccupied S hrho P k r hr label)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsmallPacking : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label / 8 <= (1 / 100 : NNReal))
    (KT : ENNReal) (hKT0 : KT ≠ 0) (hKTTop : KT ≠ ∞)
    (fixed sourcePower : ENNReal) (innerEpsilon gamma : Real)
    (hgammaTwo : gamma <= 2)
    (hjointResidual :
      KT ^ (gamma / 2) * fixed <=
        sourcePower *
          ((rho : ENNReal) ^ (-innerEpsilon / 2) *
            ((bucketShortB label : ENNReal) /
              (bucketShortA label : ENNReal)) *
            (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
              (2 - 3 * gamma)))) :
    KT * fixed <=
      sourcePower *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          (centeredAdaptiveActualBucketFullFiberNatCap
            S hrho P k r hr label KT) innerEpsilon gamma := by
  let R : ENNReal :=
    (rho : ENNReal) ^ (-innerEpsilon / 2) *
      ((bucketShortB label : ENNReal) /
        (bucketShortA label : ENNReal)) *
      (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * gamma))
  let inner : ENNReal := proposition66AInnerFactor rho
    (bucketShortA label) (bucketShortB label)
    (centeredAdaptiveActualBucketFullFiberNatCap
      S hrho P k r hr label KT) innerEpsilon gamma
  have hinnerReserve : R * KT ^ (1 - gamma / 2) <= inner := by
    simpa only [R, inner] using
      selectedParent_sourceScaleReserve_le_adaptiveActualInnerFactor
        S hrho P k r hr label hoccupied hdelta hdeltaHalf hsmallPacking
          KT hKTTop innerEpsilon gamma hgammaTwo
  exact linearKT_mul_fixed_le_sourcePower_mul_inner_of_jointResidual
    hKT0 hKTTop hinnerReserve (by
      simpa only [R] using hjointResidual)

/-- Multiplying the collapsed Section-8 coefficient by the unavoidable
linear-KT residual exposes the sole density combination
`KT^(gamma/2) * CF^(1-gamma/2)`. -/
theorem linearKTResidual_mul_sectionEightCoefficient_eq
    (delta a b : NNReal) (KT CF : ENNReal) (epsilon gamma : Real) :
    KT ^ (gamma / 2) *
        proposition66ASectionEightCoefficient delta a b CF epsilon gamma =
      (delta : ENNReal) ^ (-epsilon) *
        (KT ^ (gamma / 2) * CF ^ (1 - gamma / 2)) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * gamma / 2) := by
  unfold proposition66ASectionEightCoefficient
  ac_rfl

/-- Consumer-weak form of the same identity.  This is the smallest outer
density interface capable of paying the local linear-KT residual without
separately upper-bounding `KT`. -/
theorem linearKTResidual_mul_sectionEightCoefficient_le_of_jointDensity
    (delta a b : NNReal) (KT CF densityLoss : ENNReal)
    (epsilon gamma : Real)
    (hjointDensity :
      KT ^ (gamma / 2) * CF ^ (1 - gamma / 2) <= densityLoss) :
    KT ^ (gamma / 2) *
        proposition66ASectionEightCoefficient delta a b CF epsilon gamma <=
      (delta : ENNReal) ^ (-epsilon) * densityLoss *
        ((a : ENNReal) / (b : ENNReal)) ^ (3 * gamma / 2) := by
  rw [linearKTResidual_mul_sectionEightCoefficient_eq]
  exact mul_le_mul' (mul_le_mul' le_rfl hjointDensity) le_rfl

/-- Exact exponent calculation for the inverse density required in the
outer Frostman coefficient. -/
theorem linearKTResidual_mul_exactOuterInverse_eq_one
    {KT : ENNReal} {gamma : Real}
    (hKT0 : KT ≠ 0) (hKTTop : KT ≠ ∞) (hgammaTwo : gamma < 2) :
    KT ^ (gamma / 2) *
        (KT ^ (-gamma / (2 - gamma))) ^ (1 - gamma / 2) = 1 := by
  have hden : 2 - gamma ≠ 0 := by linarith
  have hexp :
      (-gamma / (2 - gamma)) * (1 - gamma / 2) = -gamma / 2 := by
    field_simp [hden]
  calc
    KT ^ (gamma / 2) *
        (KT ^ (-gamma / (2 - gamma))) ^ (1 - gamma / 2) =
      KT ^ (gamma / 2) *
        KT ^ ((-gamma / (2 - gamma)) * (1 - gamma / 2)) := by
          rw [ENNReal.rpow_mul]
    _ = KT ^ (gamma / 2) * KT ^ (-gamma / 2) := by rw [hexp]
    _ = KT ^ ((gamma / 2) + (-gamma / 2)) :=
      (ENNReal.rpow_add (gamma / 2) (-gamma / 2) hKT0 hKTTop).symm
    _ = KT ^ (0 : Real) := by
      congr 1
      ring
    _ = 1 := ENNReal.rpow_zero

/-- If the outer coefficient really contains the preceding inverse density,
then the joint residual cancels losslessly, leaving only the density-free
outer coefficient. -/
theorem linearKTResidual_mul_outerInverseCoefficient_rpow_eq
    {KT outerCF : ENNReal} {gamma : Real}
    (hKT0 : KT ≠ 0) (hKTTop : KT ≠ ∞) (hgammaTwo : gamma < 2) :
    KT ^ (gamma / 2) *
        (outerCF * KT ^ (-gamma / (2 - gamma))) ^
          (1 - gamma / 2) =
      outerCF ^ (1 - gamma / 2) := by
  have hp : 0 <= 1 - gamma / 2 := by linarith
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
  calc
    KT ^ (gamma / 2) *
        (outerCF ^ (1 - gamma / 2) *
          (KT ^ (-gamma / (2 - gamma))) ^ (1 - gamma / 2)) =
      outerCF ^ (1 - gamma / 2) *
        (KT ^ (gamma / 2) *
          (KT ^ (-gamma / (2 - gamma))) ^ (1 - gamma / 2)) := by
            ac_rfl
    _ = outerCF ^ (1 - gamma / 2) := by
      rw [linearKTResidual_mul_exactOuterInverse_eq_one
        hKT0 hKTTop hgammaTwo, mul_one]

#print axioms
  linearKT_mul_fixed_le_sourcePower_mul_inner_of_jointResidual
#print axioms
  selectedParent_linearKT_mul_fixed_le_sourcePower_mul_adaptiveInner_of_jointResidual
#print axioms linearKTResidual_mul_sectionEightCoefficient_eq
#print axioms
  linearKTResidual_mul_sectionEightCoefficient_le_of_jointDensity
#print axioms linearKTResidual_mul_exactOuterInverse_eq_one
#print axioms linearKTResidual_mul_outerInverseCoefficient_rpow_eq

end
end Family8LocalKTOuterInnerJointResidualAlgebraV1

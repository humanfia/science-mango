import Family8Grounding.Family8PlankRetainedOwnerFullBallNormalizationV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerFullBallPowerAbsorptionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerCubeWeightDenseBallV1
open Family8PlankRetainedOwnerDensityCardCrossV1
open Family8PlankRetainedOwnerFullBallNormalizationV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Small-scale absorption for the retained-owner full-ball estimate

The geometric normalization leaves the finite coefficient
`54000 * comparisonConstant^3 * loss`.  This module gives its explicit
small-radius threshold and replaces the coefficient by one negative power of
`rho`.  The threshold deliberately records all of its data dependence; no
uniformity in a variable plank-comparison constant or retention loss is
claimed here.
-/

def retainedOwnerFullBallCoefficient
    (D : ShadedConvexPlankFamily iota a b) (loss : ENNReal) : ENNReal :=
  54000 * (D.comparisonConstant : ENNReal) ^ 3 * loss

def retainedOwnerFullBallPowerThreshold
    (D : ShadedConvexPlankFamily iota a b) (loss : ENNReal)
    (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (retainedOwnerFullBallCoefficient D loss) absorbExponent

theorem retainedOwnerFullBallPowerThreshold_pos
    (D : ShadedConvexPlankFamily iota a b) (loss : ENNReal)
    (absorbExponent : Real) :
    0 < retainedOwnerFullBallPowerThreshold D loss absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem retainedOwnerFullBallCoefficient_ne_top
    (D : ShadedConvexPlankFamily iota a b) {loss : ENNReal}
    (hloss : loss ≠ ∞) :
    retainedOwnerFullBallCoefficient D loss ≠ ∞ := by
  unfold retainedOwnerFullBallCoefficient
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · norm_num
    · exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  · exact hloss

theorem retainedOwnerFullBallCoefficient_le_rho_negativePower
    (D : ShadedConvexPlankFamily iota a b) {loss : ENNReal}
    {rho : NNReal} {absorbExponent : Real}
    (hloss : loss ≠ ∞) (hrho : 0 < rho)
    (habsorb : 0 < absorbExponent)
    (hsmall : rho ≤
      retainedOwnerFullBallPowerThreshold D loss absorbExponent) :
    retainedOwnerFullBallCoefficient D loss ≤
      (rho : ENNReal) ^ (-absorbExponent) := by
  exact finiteConstant_le_delta_negativePower
    (retainedOwnerFullBallCoefficient_ne_top D hloss)
      habsorb hrho hsmall

theorem fullBall_le_rho_negativePower_mul_localMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (rho : NNReal) (density loss localMass : ENNReal)
    (hloss : loss ≠ ∞) {absorbExponent : Real}
    (hrho : 0 < rho) (habsorb : 0 < absorbExponent)
    (hsmall : rho ≤
      retainedOwnerFullBallPowerThreshold D loss absorbExponent)
    (hlocal : density * plankCertifiedLowerVolume D *
        volume (Metric.ball (0 : Space)
          ((((rho / 2) / 3 : NNReal)) : Real)) ≤
      250 * loss * localMass) :
    density * ((a : ENNReal) * (b : ENNReal)) *
        volume (Metric.ball (0 : Space) (rho : Real)) ≤
      (rho : ENNReal) ^ (-absorbExponent) * localMass := by
  have hfull := density_mul_crossSection_mul_ballVolume_le_of_packingBall
    D C q hmass rho density loss localMass hlocal
  have hcoefficient :=
    retainedOwnerFullBallCoefficient_le_rho_negativePower
      D hloss hrho habsorb hsmall
  calc
    _ ≤ retainedOwnerFullBallCoefficient D loss * localMass := by
      simpa only [retainedOwnerFullBallCoefficient, mul_assoc] using hfull
    _ ≤ (rho : ENNReal) ^ (-absorbExponent) * localMass := by
      gcongr

#print axioms retainedOwnerFullBallPowerThreshold_pos
#print axioms retainedOwnerFullBallCoefficient_ne_top
#print axioms retainedOwnerFullBallCoefficient_le_rho_negativePower
#print axioms fullBall_le_rho_negativePower_mul_localMass

end
end Family8PlankRetainedOwnerFullBallPowerAbsorptionV1

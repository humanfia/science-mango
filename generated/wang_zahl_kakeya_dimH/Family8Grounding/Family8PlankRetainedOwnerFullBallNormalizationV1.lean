import Family8Grounding.Family8PlankRetainedOwnerLocalDenseBallEndpointV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerFullBallNormalizationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerCubeWeightDenseBallV1
open Family8PlankRetainedOwnerDensityCardCrossV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Full-ball normalization for the retained-owner local density estimate

The packing ball in the CubeWeight output has radius `rho / 6`.  In three
dimensions its volume is exactly `1 / 216` of the radius-`rho` ball.  The
second theorem combines this identity with the certified plank volume and
keeps the comparison-constant loss explicit.
-/

theorem ballVolume_eq_twoHundredSixteen_mul_packingBallVolume (rho : NNReal) :
    volume (Metric.ball (0 : Space) (rho : Real)) =
      216 • volume (Metric.ball (0 : Space)
        ((((rho / 2) / 3 : NNReal)) : Real)) := by
  simp only [EuclideanSpace.volume_ball_fin_three, nsmul_eq_mul]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  rw [ENNReal.toReal_ofReal
    (by positivity : 0 ≤ ((((rho / 2) / 3 : NNReal)) : Real))]
  norm_num [NNReal.coe_div]
  ring

theorem density_mul_crossSection_mul_ballVolume_le_of_packingBall
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (rho : NNReal) (density loss localMass : ENNReal)
    (hlocal : density * plankCertifiedLowerVolume D *
        volume (Metric.ball (0 : Space)
          ((((rho / 2) / 3 : NNReal)) : Real)) ≤
      250 * loss * localMass) :
    density * ((a : ENNReal) * (b : ENNReal)) *
        volume (Metric.ball (0 : Space) (rho : Real)) ≤
      54000 * (D.comparisonConstant : ENNReal) ^ 3 *
        loss * localMass := by
  let j := Classical.choice
    (retainedOwnerIndex_nonempty_of_shadingMass_ne_zero D C q hmass)
  have hcomparison : 1 ≤ D.comparisonConstant :=
    (D.all_isPlank j.1).2.2.2.1
  have hC0 : D.comparisonConstant ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le hcomparison)
  have hcancelNN :
      D.comparisonConstant ^ 3 * (D.comparisonConstant⁻¹) ^ 3 = 1 := by
    rw [← mul_pow]
    simp [hC0]
  have hcancel :
      (D.comparisonConstant : ENNReal) ^ 3 *
          (((D.comparisonConstant)⁻¹ : NNReal) : ENNReal) ^ 3 = 1 := by
    exact_mod_cast hcancelNN
  rw [ballVolume_eq_twoHundredSixteen_mul_packingBallVolume]
  simp only [nsmul_eq_mul]
  calc
    density * ((a : ENNReal) * (b : ENNReal)) *
        (216 * volume (Metric.ball (0 : Space)
          ((((rho / 2) / 3 : NNReal)) : Real))) =
      (216 * (D.comparisonConstant : ENNReal) ^ 3) *
        (density * plankCertifiedLowerVolume D *
          volume (Metric.ball (0 : Space)
            ((((rho / 2) / 3 : NNReal)) : Real))) := by
      unfold plankCertifiedLowerVolume
      calc
        _ = 216 * 1 * (density * ((a : ENNReal) * (b : ENNReal)) *
            volume (Metric.ball (0 : Space)
              ((((rho / 2) / 3 : NNReal)) : Real))) := by ring
        _ = 216 *
            ((D.comparisonConstant : ENNReal) ^ 3 *
              (((D.comparisonConstant)⁻¹ : NNReal) : ENNReal) ^ 3) *
            (density * ((a : ENNReal) * (b : ENNReal)) *
              volume (Metric.ball (0 : Space)
                ((((rho / 2) / 3 : NNReal)) : Real))) := by rw [hcancel]
        _ = _ := by ring
    _ ≤ (216 * (D.comparisonConstant : ENNReal) ^ 3) *
        (250 * loss * localMass) := by gcongr
    _ = 54000 * (D.comparisonConstant : ENNReal) ^ 3 *
        loss * localMass := by ring

#print axioms ballVolume_eq_twoHundredSixteen_mul_packingBallVolume
#print axioms density_mul_crossSection_mul_ballVolume_le_of_packingBall

end
end Family8PlankRetainedOwnerFullBallNormalizationV1

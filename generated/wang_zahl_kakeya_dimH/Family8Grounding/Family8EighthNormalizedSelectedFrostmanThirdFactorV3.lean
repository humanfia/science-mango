import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV4
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8EighthNormalizedSelectedFrostmanThirdFactorV3

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# Eighth-normalized selected Frostman RHS as the third scale factor

The B2 normalization used by the canonical frozen outer argument produces
actual tubes at radius `rho / 8`, whereas the paper's third scale factor is
written from `rho` to one.  The exact missing factor is the one-tube factor
from `rho / 8` to `rho`; the epsilon and actual-volume costs remain explicit.

V1 and V2 were namespace/API drafts and are intentionally not imported.
-/

/-- The literal finite loss in converting a selected actual Frostman RHS at
`rho / 8` into the official scale-count factor from `rho` to one. -/
def eighthSelectedThirdFactorLoss
    (rho : NNReal) (loss : ENNReal) (epsilon gamma : Real) : ENNReal :=
  ((loss * (((rho / 8 : NNReal) : ENNReal) ^ (-epsilon))) *
      (8 : ENNReal) ^ (1 - gamma / 2)) *
    sectionEightScaleCountFrostmanFactor (rho / 8) rho 1 gamma

/-- A selected subtype of any actual datum at scale `rho / 8` contributes at
most the explicit eighth-normalization loss times the official third factor
with the full source count.  Selection does not require an exact-cardinality
assumption: restriction only decreases actual family volume. -/
theorem loss_mul_selectedRHS_le_eighthLoss_mul_thirdFactor
    {rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum (rho / 8) iota)
    (selected : Finset iota)
    {loss : ENNReal} {epsilon gamma : Real}
    (hrhoPos : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hgammaTwo : gamma <= 2) :
    loss * frostmanMultiplicityRHS (rho / 8)
        (restrictActualTubeDatum D selected).actualFamilyVolume epsilon gamma <=
      eighthSelectedThirdFactorLoss rho loss epsilon gamma *
        sectionEightScaleCountFrostmanFactor
          rho 1 (Fintype.card iota) gamma := by
  have hsmallPos : 0 < rho / 8 := div_pos hrhoPos (by norm_num)
  have hsmallHalf : rho / 8 <= (2 : NNReal)⁻¹ := by
    calc
      rho / 8 <= rho := div_le_self rho.2 (by norm_num)
      _ <= (2 : NNReal)⁻¹ := hrhoHalf
  have hselectedVolume :
      (restrictActualTubeDatum D selected).actualFamilyVolume <=
        1 * D.actualFamilyVolume := by
    simpa using restrictActualTubeDatum_actualFamilyVolume_le D selected
  have hselectedRHS :
      frostmanMultiplicityRHS (rho / 8)
          (restrictActualTubeDatum D selected).actualFamilyVolume epsilon gamma <=
        frostmanMultiplicityRHS (rho / 8)
          D.actualFamilyVolume epsilon gamma := by
    have h := frostmanMultiplicityRHS_le_of_volume_le_factor_mul
      (delta := rho / 8) (epsilon := epsilon) (gamma := gamma)
      hgammaTwo hselectedVolume
    simpa using h
  have hactualCard :
      frostmanMultiplicityRHS (rho / 8)
          D.actualFamilyVolume epsilon gamma <=
        frostmanMultiplicityRHS (rho / 8)
            (proposition66ACardScaleVolume
              (rho / 8) (Fintype.card iota)) epsilon gamma *
          (8 : ENNReal) ^ (1 - gamma / 2) :=
    frostmanMultiplicityRHS_actual_le_cardScale_mul_eight_rpow
      D hsmallHalf hgammaTwo
  have hepsilonSeparate :
      frostmanMultiplicityRHS (rho / 8)
          (proposition66ACardScaleVolume
            (rho / 8) (Fintype.card iota)) epsilon gamma =
        (((rho / 8 : NNReal) : ENNReal) ^ (-epsilon)) *
          frostmanMultiplicityRHS (rho / 8)
            (proposition66ACardScaleVolume
              (rho / 8) (Fintype.card iota)) 0 gamma := by
    simp [frostmanMultiplicityRHS]
    ac_rfl
  have hfactorSplit :
      sectionEightScaleCountFrostmanFactor
          (rho / 8) 1 (Fintype.card iota) gamma =
        sectionEightScaleCountFrostmanFactor (rho / 8) rho 1 gamma *
          sectionEightScaleCountFrostmanFactor
            rho 1 (Fintype.card iota) gamma := by
    simpa using (sectionEightScaleCountFrostmanFactor_mul
      (fine := rho / 8) (middle := rho) (coarse := 1)
      (firstCount := 1) (secondCount := Fintype.card iota)
      hsmallPos hrhoPos (by norm_num) hgammaTwo).symm
  calc
    loss * frostmanMultiplicityRHS (rho / 8)
        (restrictActualTubeDatum D selected).actualFamilyVolume epsilon gamma <=
      loss * frostmanMultiplicityRHS (rho / 8)
        D.actualFamilyVolume epsilon gamma :=
      mul_le_mul' le_rfl hselectedRHS
    _ <= loss *
        (frostmanMultiplicityRHS (rho / 8)
            (proposition66ACardScaleVolume
              (rho / 8) (Fintype.card iota)) epsilon gamma *
          (8 : ENNReal) ^ (1 - gamma / 2)) :=
      mul_le_mul' le_rfl hactualCard
    _ = eighthSelectedThirdFactorLoss rho loss epsilon gamma *
        sectionEightScaleCountFrostmanFactor
          rho 1 (Fintype.card iota) gamma := by
      rw [hepsilonSeparate,
        <- sectionEightScaleCountFrostmanFactor_to_one_eq_rhs_zero,
        hfactorSplit]
      unfold eighthSelectedThirdFactorLoss
      ac_rfl

#print axioms eighthSelectedThirdFactorLoss
#print axioms loss_mul_selectedRHS_le_eighthLoss_mul_thirdFactor

end

end Family8EighthNormalizedSelectedFrostmanThirdFactorV3

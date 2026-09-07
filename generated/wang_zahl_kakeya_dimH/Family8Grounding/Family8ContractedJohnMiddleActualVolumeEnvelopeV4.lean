import Family8Grounding.Family8ContractedJohnMiddleActualVolumeEnvelopeV3
import Mathlib.Tactic

/-!
# Actual-volume envelope from explicit scale bounds, V4

The tube-volume comparison used by the middle factor needs only positivity
and the half-scale bound.  It does not use pairwise essential distinctness.
This successor exposes that minimal interface so it can consume the selected
datum returned by the mass-popular endpoint without replaying its hidden
greedy admissibility witness.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ContractedJohnMiddleActualVolumeEnvelopeV4

open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-- Minimal-scale version of the actual-volume envelope. -/
theorem loss_mul_actualRHS_le_fixed_mul_ratioGain_mul_sectionEight_of_scale
    {fine coarse scale : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum scale iota)
    {loss K : ENNReal} {epsilon beta gamma lossExp kappa : Real}
    (hfine : 0 < fine) (hcoarse : 0 < coarse)
    (hscale : 0 < scale) (hscaleHalf : scale <= (2 : NNReal)⁻¹)
    (hbetaTwo : beta <= 2) (hgammaTwo : gamma <= 2)
    (hgap : 0 <= gamma - beta)
    (hscaleEq : (scale : ENNReal) =
      (3 / 64 : ENNReal) *
        ((fine : ENNReal) / (coarse : ENNReal)))
    (hloss : loss <= (scale : ENNReal) ^ (-lossExp))
    (hcountPos : 0 < Fintype.card iota)
    (hcount : (Fintype.card iota : ENNReal) <=
      K * (((fine : ENNReal) / (coarse : ENNReal)) ^
        (-(2 + kappa)))) :
    loss * frostmanMultiplicityRHS
        scale D.actualFamilyVolume epsilon beta <=
      contractedJohnMiddleActualFixedCoefficient
          K epsilon beta gamma lossExp *
        (((fine : ENNReal) / (coarse : ENNReal)) ^
          contractedJohnMiddleRatioGain
            epsilon beta gamma lossExp kappa) *
        sectionEightScaleCountFrostmanFactor
          fine coarse (Fintype.card iota) gamma := by
  have hcard :=
    frostmanMultiplicityRHS_actual_le_cardScale_mul_eight_rpow
      (epsilon := epsilon) (beta := beta)
      D hscaleHalf hbetaTwo
  have hrelative :=
    loss_mul_cardScaleRHS_le_fixed_mul_ratioGain_mul_sectionEight
      (loss := loss) (K := K) (epsilon := epsilon) (beta := beta)
      (gamma := gamma) (lossExp := lossExp) (kappa := kappa)
      hfine hcoarse hscale hcountPos hbetaTwo hgammaTwo hgap
        hscaleEq hloss hcount
  calc
    loss * frostmanMultiplicityRHS
          scale D.actualFamilyVolume epsilon beta <=
        loss *
          (frostmanMultiplicityRHS scale
              (proposition66ACardScaleVolume scale (Fintype.card iota))
              epsilon beta *
            (8 : ENNReal) ^ (1 - beta / 2)) :=
      mul_le_mul' le_rfl hcard
    _ = (8 : ENNReal) ^ (1 - beta / 2) *
          (loss * frostmanMultiplicityRHS scale
            (proposition66ACardScaleVolume scale (Fintype.card iota))
              epsilon beta) := by
      ac_rfl
    _ <= (8 : ENNReal) ^ (1 - beta / 2) *
          (contractedJohnMiddleFixedCoefficient
              K epsilon beta gamma lossExp *
            (((fine : ENNReal) / (coarse : ENNReal)) ^
              contractedJohnMiddleRatioGain
                epsilon beta gamma lossExp kappa) *
            sectionEightScaleCountFrostmanFactor
              fine coarse (Fintype.card iota) gamma) :=
      mul_le_mul' le_rfl hrelative
    _ = contractedJohnMiddleActualFixedCoefficient
          K epsilon beta gamma lossExp *
        (((fine : ENNReal) / (coarse : ENNReal)) ^
          contractedJohnMiddleRatioGain
            epsilon beta gamma lossExp kappa) *
        sectionEightScaleCountFrostmanFactor
          fine coarse (Fintype.card iota) gamma := by
      unfold contractedJohnMiddleActualFixedCoefficient
      ac_rfl

#print axioms
  loss_mul_actualRHS_le_fixed_mul_ratioGain_mul_sectionEight_of_scale

end
end Family8ContractedJohnMiddleActualVolumeEnvelopeV4

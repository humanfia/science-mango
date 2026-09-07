import Family8Grounding.Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
import Family8Grounding.Family8Prop66AActualFamilyVolumeTransportV1
import Mathlib.Tactic

/-!
# Actual-volume envelope for the contracted-John middle factor, V3

V1 and V2 omitted explicit exponent arguments at separate polymorphic calls
and are not imported.  This successor adds the exact actual-volume loss to
the already frozen relative-scale envelope.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ContractedJohnMiddleActualVolumeEnvelopeV3

open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

def contractedJohnMiddleActualFixedCoefficient
    (K : ENNReal) (epsilon beta gamma lossExp : Real) : ENNReal :=
  (8 : ENNReal) ^ (1 - beta / 2) *
    contractedJohnMiddleFixedCoefficient K epsilon beta gamma lossExp

theorem loss_mul_actualRHS_le_fixed_mul_ratioGain_mul_sectionEight
    {fine coarse scale : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum scale iota)
    {loss K : ENNReal} {epsilon beta gamma lossExp kappa : Real}
    (hD : D.IsAdmissible)
    (hfine : 0 < fine) (hcoarse : 0 < coarse)
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
      D hD.delta_le_half hbetaTwo
  have hrelative :=
    loss_mul_cardScaleRHS_le_fixed_mul_ratioGain_mul_sectionEight
      (loss := loss) (K := K) (epsilon := epsilon) (beta := beta)
      (gamma := gamma) (lossExp := lossExp) (kappa := kappa)
      hfine hcoarse hD.delta_pos hcountPos hbetaTwo hgammaTwo hgap
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

#print axioms contractedJohnMiddleActualFixedCoefficient
#print axioms
  loss_mul_actualRHS_le_fixed_mul_ratioGain_mul_sectionEight

end
end Family8ContractedJohnMiddleActualVolumeEnvelopeV3

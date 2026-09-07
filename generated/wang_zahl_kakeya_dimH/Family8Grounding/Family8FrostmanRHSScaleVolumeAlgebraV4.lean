import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV3

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8FrostmanRHSScaleVolumeAlgebraV4

open Family8KatzTaoFrostmanPropertiesV1
open Family8FrostmanRHSScaleVolumeAlgebraV3

noncomputable section

/-- The complete finite scalar left after converting a fixed-John selected
Frostman RHS at `delta/8` back to the source scale and source volume. -/
def fixedJohnFrostmanTransportScalar
    (loss copyVolumeFactor : ENNReal)
    (epsilon gamma : Real) : ENNReal :=
  loss * ((8 : ENNReal) ^ epsilon * (8 : ENNReal) ^ (2 * gamma)) *
    copyVolumeFactor ^ (1 - gamma / 2)

/-- Increasing the volume by a factor `A` increases the Frostman RHS by at
most `A^(1-gamma/2)` whenever `gamma ≤ 2`. -/
theorem frostmanMultiplicityRHS_le_of_volume_le_factor_mul
    {delta : NNReal} {selectedVolume sourceVolume factor : ENNReal}
    {epsilon gamma : Real}
    (hgamma : gamma <= 2)
    (hvolume : selectedVolume <= factor * sourceVolume) :
    frostmanMultiplicityRHS delta selectedVolume epsilon gamma <=
      frostmanMultiplicityRHS delta sourceVolume epsilon gamma *
        factor ^ (1 - gamma / 2) := by
  have hp : 0 <= 1 - gamma / 2 := by linarith
  have hpow :
      selectedVolume ^ (1 - gamma / 2) <=
        (factor * sourceVolume) ^ (1 - gamma / 2) :=
    ENNReal.rpow_le_rpow hvolume hp
  unfold frostmanMultiplicityRHS
  calc
    (delta : ENNReal) ^ (-epsilon) *
          (delta : ENNReal) ^ (-2 * gamma) *
          selectedVolume ^ (1 - gamma / 2) <=
        ((delta : ENNReal) ^ (-epsilon) *
          (delta : ENNReal) ^ (-2 * gamma)) *
          (factor * sourceVolume) ^ (1 - gamma / 2) := by
      exact mul_le_mul_right hpow _
    _ = ((delta : ENNReal) ^ (-epsilon) *
          (delta : ENNReal) ^ (-2 * gamma) *
          sourceVolume ^ (1 - gamma / 2)) *
        factor ^ (1 - gamma / 2) := by
      rw [ENNReal.mul_rpow_of_nonneg factor sourceVolume hp]
      ac_rfl

/-- Combined scale/volume transport.  This is the exact algebraic endpoint
consumed after V5: all unresolved geometry is now confined to a power bound
for the displayed scalar, not to the final multiplicity RHS. -/
theorem loss_mul_frostmanMultiplicityRHS_div_eight_le_source
    {delta : NNReal} {selectedVolume sourceVolume loss copyVolumeFactor : ENNReal}
    {epsilon gamma : Real}
    (hgamma : gamma <= 2)
    (hvolume : selectedVolume <= copyVolumeFactor * sourceVolume) :
    loss * frostmanMultiplicityRHS (delta / 8)
        selectedVolume epsilon gamma <=
      fixedJohnFrostmanTransportScalar loss copyVolumeFactor epsilon gamma *
        frostmanMultiplicityRHS delta sourceVolume epsilon gamma := by
  have hvolumeRHS :=
    frostmanMultiplicityRHS_le_of_volume_le_factor_mul
      (delta := delta) (epsilon := epsilon) (gamma := gamma)
      hgamma hvolume
  rw [frostmanMultiplicityRHS_div_eight]
  unfold fixedJohnFrostmanTransportScalar
  calc
    loss *
          (((8 : ENNReal) ^ epsilon * (8 : ENNReal) ^ (2 * gamma)) *
            frostmanMultiplicityRHS delta selectedVolume epsilon gamma) <=
        loss *
          (((8 : ENNReal) ^ epsilon * (8 : ENNReal) ^ (2 * gamma)) *
            (frostmanMultiplicityRHS delta sourceVolume epsilon gamma *
              copyVolumeFactor ^ (1 - gamma / 2))) := by
      exact mul_le_mul_right (mul_le_mul_right hvolumeRHS _) _
    _ = (loss *
          ((8 : ENNReal) ^ epsilon * (8 : ENNReal) ^ (2 * gamma)) *
          copyVolumeFactor ^ (1 - gamma / 2)) *
        frostmanMultiplicityRHS delta sourceVolume epsilon gamma := by
      ac_rfl

#print axioms fixedJohnFrostmanTransportScalar
#print axioms frostmanMultiplicityRHS_le_of_volume_le_factor_mul
#print axioms loss_mul_frostmanMultiplicityRHS_div_eight_le_source

end
end Family8FrostmanRHSScaleVolumeAlgebraV4

import Family8Grounding.Family8LongIntervalBootstrapNumericsV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

namespace Family8LongIntervalKatzTaoCountNormalizationV2

open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8LongIntervalBootstrapNumericsV1

/-!
# Count normalization for the long-interval Katz--Tao endpoint

The generalized Katz--Tao theorem returns a power of the literal number of
coarse tubes.  The paper's long-interval bootstrap instead uses the
normalized variable `X = |T_b| b^2`.  This file records that these are
exactly the same expression; there is no comparison constant or loss at
this interface.
-/

/-- Substituting `X = tubeCount * b^2` into the long-interval expression
recovers the literal Katz--Tao multiplicity right-hand side. -/
theorem katzTaoMultiplicityRHS_eq_longIntervalKatzTaoRHSENNReal
    {d b X : NNReal} {tubeCount : Nat}
    {epsilon etaPrime beta : Real}
    (hd : 0 < d) (hb : 0 < b) (htubeCount : 0 < tubeCount)
    (hX : X = (tubeCount : NNReal) * b ^ 2) :
    katzTaoMultiplicityRHS d tubeCount
        (longIntervalDeltaLoss epsilon etaPrime) beta =
      longIntervalKatzTaoRHSENNReal d b X epsilon etaPrime beta := by
  have htubeCountNN : 0 < (tubeCount : NNReal) := by
    exact_mod_cast htubeCount
  have hXpos : 0 < X := by
    rw [hX]
    exact mul_pos htubeCountNN (pow_pos hb 2)
  have hdiv : X / b ^ 2 = (tubeCount : NNReal) := by
    rw [hX]
    apply (div_eq_iff (pow_ne_zero 2 hb.ne')).2
    ring
  have hNN :
      d ^ (-longIntervalDeltaLoss epsilon etaPrime) *
          (tubeCount : NNReal) ^ beta =
        longIntervalKatzTaoRHS d b X epsilon etaPrime beta := by
    rw [longIntervalKatzTaoRHS_eq_divisionForm, hdiv]
  have hcast :
      ((d ^ (-longIntervalDeltaLoss epsilon etaPrime) *
          (tubeCount : NNReal) ^ beta : NNReal) : ENNReal) =
        (longIntervalKatzTaoRHS d b X epsilon etaPrime beta : ENNReal) := by
    exact_mod_cast hNN
  rw [← coe_longIntervalKatzTaoRHS hd hb hXpos]
  unfold katzTaoMultiplicityRHS
  simpa only [ENNReal.coe_mul,
    ENNReal.coe_rpow_of_ne_zero hd.ne',
    ENNReal.coe_rpow_of_ne_zero htubeCountNN.ne',
    ENNReal.coe_natCast] using hcast

/-- Multiplicity-facing form of the complete long-interval numerical
bootstrap after the lossless count normalization above. -/
theorem katzTaoMultiplicityRHS_le_longIntervalFrostmanTargetENNReal
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    {d b X : NNReal} {tubeCount : Nat}
    (hd : 0 < d) (hdOne : d ≤ 1) (hdb : d ≤ b)
    (hbUpper : b ≤ d ^ (1 - P.epsilon))
    (hX : X = (tubeCount : NNReal) * b ^ 2)
    (hXLower : d ^ (10 * P.eta j / (P.epsilon * beta)) ≤ X)
    (hXUpper : X ≤ d ^
      (-longIntervalDeltaLoss P.epsilon
        (10 * P.eta j / (P.epsilon * beta))))
    (htubeCount : 0 < tubeCount)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1) :
    katzTaoMultiplicityRHS d tubeCount
        (longIntervalDeltaLoss P.epsilon
          (10 * P.eta j / (P.epsilon * beta))) beta ≤
      longIntervalFrostmanTargetENNReal d b X
        (10 * P.eta j / (P.epsilon * beta)) gamma := by
  calc
    katzTaoMultiplicityRHS d tubeCount
          (longIntervalDeltaLoss P.epsilon
            (10 * P.eta j / (P.epsilon * beta))) beta =
        longIntervalKatzTaoRHSENNReal d b X P.epsilon
          (10 * P.eta j / (P.epsilon * beta)) beta :=
      katzTaoMultiplicityRHS_eq_longIntervalKatzTaoRHSENNReal
        hd (hd.trans_le hdb) htubeCount hX
    _ ≤ longIntervalFrostmanTargetENNReal d b X
          (10 * P.eta j / (P.epsilon * beta)) gamma :=
      longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal
        P j hd hdOne hdb hbUpper hXLower hXUpper hbeta hgamma

#print axioms katzTaoMultiplicityRHS_eq_longIntervalKatzTaoRHSENNReal
#print axioms katzTaoMultiplicityRHS_le_longIntervalFrostmanTargetENNReal

end Family8LongIntervalKatzTaoCountNormalizationV2

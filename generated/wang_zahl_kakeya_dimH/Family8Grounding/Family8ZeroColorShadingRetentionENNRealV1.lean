import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ZeroColorShadingRetentionENNRealV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumDensityRetentionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Lift zero-colour retention from `Real` back to `ENNReal`

The finite Chernoff selector is stated for real-valued weights.  Actual
shading mass and density use `ENNReal`.  Since every finite-family shading
mass is finite, the real retention inequality loses no information and gives
the exact `2k` density loss required by the sampled datum.
-/

/-- A real `1/(2k)` shading-mass retention estimate is exactly enough for the
corresponding `ENNReal` multiplicative bound. -/
theorem shadingMass_le_two_mul_k_mul_of_toReal_div_le
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (k : Nat) [NeZero k]
    (omega : iota → Fin k)
    (hretained :
      D.shading.shadingMass.toReal / (2 * (k : Real)) ≤
        (zeroColorActualDatum D k omega).shading.shadingMass.toReal) :
    D.shading.shadingMass ≤
      ((2 * k : Nat) : ENNReal) *
        (zeroColorActualDatum D k omega).shading.shadingMass := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hfactor : 0 < 2 * (k : Real) := by positivity
  have hreal :
      D.shading.shadingMass.toReal ≤
        (2 * (k : Real)) *
          (zeroColorActualDatum D k omega).shading.shadingMass.toReal :=
    by simpa [mul_comm] using (div_le_iff₀ hfactor).mp hretained
  have hsourceTop : D.shading.shadingMass ≠ ∞ :=
    (D.shading.shadingMass_le_familyVolume.trans_lt
      (familyVolume_lt_top D.family.bodyFamily)).ne
  have hsampleTop :
      (zeroColorActualDatum D k omega).shading.shadingMass ≠ ∞ :=
    ((zeroColorActualDatum D k omega).shading.shadingMass_le_familyVolume.trans_lt
      (familyVolume_lt_top
        (zeroColorActualDatum D k omega).family.bodyFamily)).ne
  have hrightTop :
      ((2 * k : Nat) : ENNReal) *
          (zeroColorActualDatum D k omega).shading.shadingMass ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hsampleTop
  apply (ENNReal.toReal_le_toReal hsourceTop hrightTop).mp
  simpa using hreal

/-- Direct density form consumed by the generalized Katz--Tao application. -/
theorem source_shadingDensity_div_two_mul_k_le_zeroColorActualDatum
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (k : Nat) [NeZero k]
    (omega : iota → Fin k)
    (hretained :
      D.shading.shadingMass.toReal / (2 * (k : Real)) ≤
        (zeroColorActualDatum D k omega).shading.shadingMass.toReal) :
    D.shading.shadingDensity / ((2 * k : Nat) : ENNReal) ≤
      (zeroColorActualDatum D k omega).shading.shadingDensity := by
  apply source_shadingDensity_div_loss_le_zeroColorActualDatum
  exact shadingMass_le_two_mul_k_mul_of_toReal_div_le D k omega hretained

#print axioms shadingMass_le_two_mul_k_mul_of_toReal_div_le
#print axioms source_shadingDensity_div_two_mul_k_le_zeroColorActualDatum

end
end Family8ZeroColorShadingRetentionENNRealV1

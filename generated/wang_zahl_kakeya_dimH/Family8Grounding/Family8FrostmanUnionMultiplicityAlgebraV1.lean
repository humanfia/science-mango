import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

open scoped ENNReal NNReal
open MeasureTheory

namespace Family8FrostmanUnionMultiplicityAlgebraV1

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Exact union-volume form of the Frostman multiplicity estimate

This file proves the algebra behind Definition `K_F(beta)`, including all
zero-mass cases.  It also isolates the numerical conversion used in the
all-Frostman branch of Main Lemma 1.  No union-volume lower bound or tube
packing bound is assumed to be a theorem here.
-/

/-- The union-volume right-hand side equivalent to `K_F(beta)`. -/
def frostmanUnionLowerRHS (delta : NNReal) (actualVolume : ENNReal)
    (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ epsilon *
    (delta : ENNReal) ^ (2 * beta) *
      actualVolume ^ (beta / 2)

/-- The multiplicity and union-volume right-hand sides multiply to the
actual summed tube volume.  Nonnegativity of both volume exponents is why
this identity also covers `actualVolume = 0`. -/
theorem frostmanMultiplicityRHS_mul_frostmanUnionLowerRHS
    {delta : NNReal} {actualVolume : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2) :
    frostmanMultiplicityRHS delta actualVolume epsilon beta *
        frostmanUnionLowerRHS delta actualVolume epsilon beta =
      actualVolume := by
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hbetaHalf : 0 ≤ beta / 2 := by linarith
  have hOneSub : 0 ≤ 1 - beta / 2 := by linarith
  unfold frostmanMultiplicityRHS frostmanUnionLowerRHS
  calc
    ((delta : ENNReal) ^ (-epsilon) *
          (delta : ENNReal) ^ (-2 * beta) *
          actualVolume ^ (1 - beta / 2)) *
        ((delta : ENNReal) ^ epsilon *
          (delta : ENNReal) ^ (2 * beta) *
          actualVolume ^ (beta / 2)) =
        (((delta : ENNReal) ^ (-epsilon) *
            (delta : ENNReal) ^ epsilon) *
          ((delta : ENNReal) ^ (-2 * beta) *
            (delta : ENNReal) ^ (2 * beta))) *
          (actualVolume ^ (1 - beta / 2) *
            actualVolume ^ (beta / 2)) := by ac_rfl
    _ = ((delta : ENNReal) ^ ((-epsilon) + epsilon) *
          (delta : ENNReal) ^ ((-2 * beta) + (2 * beta))) *
          actualVolume ^ ((1 - beta / 2) + (beta / 2)) := by
      rw [ENNReal.rpow_add (-epsilon) epsilon hd0 hdTop,
        ENNReal.rpow_add (-2 * beta) (2 * beta) hd0 hdTop,
        ENNReal.rpow_add_of_nonneg (1 - beta / 2) (beta / 2)
          hOneSub hbetaHalf]
    _ = actualVolume := by ring_nf; simp

/-- A Frostman-form union-volume lower bound implies the exact average
multiplicity upper bound.  `ENNReal.div_le_of_le_mul` makes the proof valid
even when the shaded union has zero volume. -/
theorem averageMultiplicity_le_frostmanMultiplicityRHS_of_unionLower
    {delta : NNReal} {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F)
    {epsilon beta : Real}
    (hdelta : 0 < delta) (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2)
    (hunion : frostmanUnionLowerRHS delta (familyVolume F) epsilon beta ≤
      volume Y.shadedUnion) :
    Y.averageMultiplicity ≤
      frostmanMultiplicityRHS delta (familyVolume F) epsilon beta := by
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  calc
    Y.shadingMass ≤ familyVolume F := Y.shadingMass_le_familyVolume
    _ = frostmanMultiplicityRHS delta (familyVolume F) epsilon beta *
          frostmanUnionLowerRHS delta (familyVolume F) epsilon beta :=
      (frostmanMultiplicityRHS_mul_frostmanUnionLowerRHS
        hdelta hbeta0 hbeta2).symm
    _ ≤ frostmanMultiplicityRHS delta (familyVolume F) epsilon beta *
          volume Y.shadedUnion :=
      mul_le_mul_right hunion _

/-- The numerical comparison in the all-Frostman branch: if the summed
tube volume is at most `delta^(-2)`, then the `K_F(gamma/2)` volume factor is
at most `delta^(gamma/2)`. -/
theorem allFrostman_volumeFactor_le
    {delta : NNReal} {actualVolume : ENNReal} {gamma : Real}
    (hdelta : 0 < delta) (hgamma : 0 ≤ gamma)
    (hvolume : actualVolume ≤ (delta : ENNReal) ^ (-2 : Real)) :
    (delta : ENNReal) ^ gamma * actualVolume ^ (gamma / 4) ≤
      (delta : ENNReal) ^ (gamma / 2) := by
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hquarter : 0 ≤ gamma / 4 := by linarith
  calc
    (delta : ENNReal) ^ gamma * actualVolume ^ (gamma / 4)
        ≤ (delta : ENNReal) ^ gamma *
            ((delta : ENNReal) ^ (-2 : Real)) ^ (gamma / 4) := by
          exact mul_le_mul_right
            (ENNReal.rpow_le_rpow hvolume hquarter) _
    _ = (delta : ENNReal) ^ gamma *
          (delta : ENNReal) ^ ((-2 : Real) * (gamma / 4)) := by
          rw [ENNReal.rpow_mul]
    _ = (delta : ENNReal) ^
          (gamma + ((-2 : Real) * (gamma / 4))) := by
          rw [ENNReal.rpow_add gamma ((-2 : Real) * (gamma / 4)) hd0 hdTop]
    _ = (delta : ENNReal) ^ (gamma / 2) := by
          congr 1
          ring_nf

/-- Adding the allowed `delta^epsilon` loss only weakens the required union
lower bound.  This is the exact exponent conversion used after the Sticky
all-Frostman output. -/
theorem frostmanUnionLowerRHS_halfExponent_le
    {delta : NNReal} {actualVolume : ENNReal} {epsilon gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hgamma : 0 ≤ gamma)
    (hvolume : actualVolume ≤ (delta : ENNReal) ^ (-2 : Real)) :
    frostmanUnionLowerRHS delta actualVolume epsilon (gamma / 2) ≤
      (delta : ENNReal) ^ (gamma / 2) := by
  have hdeltaENN : (delta : ENNReal) ≤ 1 := by
    simpa using ENNReal.coe_le_coe.mpr hdeltaOne
  have hloss : (delta : ENNReal) ^ epsilon ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow hdeltaENN hepsilon
  have hfactor := allFrostman_volumeFactor_le hdelta hgamma hvolume
  unfold frostmanUnionLowerRHS
  have hrewrite :
      (delta : ENNReal) ^ (2 * (gamma / 2)) *
          actualVolume ^ ((gamma / 2) / 2) =
        (delta : ENNReal) ^ gamma * actualVolume ^ (gamma / 4) := by
    congr 1 <;> ring_nf
  rw [mul_assoc, hrewrite]
  exact (mul_le_of_le_one_left (by positivity) hloss).trans hfactor

#print axioms frostmanMultiplicityRHS_mul_frostmanUnionLowerRHS
#print axioms averageMultiplicity_le_frostmanMultiplicityRHS_of_unionLower
#print axioms allFrostman_volumeFactor_le
#print axioms frostmanUnionLowerRHS_halfExponent_le

end

end Family8FrostmanUnionMultiplicityAlgebraV1

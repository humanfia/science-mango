import Family8Grounding.Family8ZeroColorPolynomialJohnKatzTaoV1
import Family8Grounding.Family8ZeroColorShadingRetentionENNRealV1
import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Family8Grounding.Family8FiniteRandomRigidMotionFrostmanConnectorV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ZeroColorSampledDensityCardCancellationV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorPolynomialJohnKatzTaoV1
open Family8ZeroColorShadingRetentionENNRealV1
open Family8ActualFamilyVolumePackingV1
open Family8FiniteRandomRigidMotionFrostmanConnectorV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# Cancellation of the zero-colour sampling multiplicity in shading density

The retained mass of one colour loses a factor `2 k`.  Applying the crude
subfamily-volume monotonicity would therefore also lose `k` in density.  The
same random selection, however, has cardinality at most `tail * (#T / k)`.
Combining this with the literal tube-volume sandwich gives

`k * volume(sample) <= 16 * tail * volume(source)`.

Thus the two occurrences of `k` cancel and the sampled density loses only the
logarithmic tail factor.  This is the deterministic density input needed by
the explicit-concentration form of Lemma 3.7.
-/

/-- The cardinality gain `1/k` converts to the corresponding summed-volume
gain, with the exact ratio `8 / (1/2) = 16` from the actual tube bounds. -/
theorem zeroColorActualDatum_volume_cross_le
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (k : Nat) [NeZero k] (omega : iota -> Fin k) (tail : Real)
    (hscaledCard :
      (k : ENNReal) * ((zeroColorSample k omega).card : ENNReal) <=
        ENNReal.ofReal tail * (Fintype.card iota : ENNReal)) :
    (k : ENNReal) *
        (zeroColorActualDatum D k omega).actualFamilyVolume <=
      (16 * ENNReal.ofReal tail) * D.actualFamilyVolume := by
  let sampled := zeroColorActualDatum D k omega
  have hsampleVolume :
      sampled.actualFamilyVolume <=
        ((zeroColorSample k omega).card : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := by
    simpa [sampled] using
      actualFamilyVolume_le_card_mul_eight_sq sampled hdeltaHalf
  have hsourceVolume :
      (Fintype.card iota : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) <= D.actualFamilyVolume :=
    card_mul_half_sq_le_actualFamilyVolume D hdeltaHalf
  calc
    (k : ENNReal) * sampled.actualFamilyVolume <=
        (k : ENNReal) *
          (((zeroColorSample k omega).card : ENNReal) *
            (8 * (delta : ENNReal) ^ 2)) := by gcongr
    _ = ((k : ENNReal) *
          ((zeroColorSample k omega).card : ENNReal)) *
            (8 * (delta : ENNReal) ^ 2) := by ac_rfl
    _ <= (ENNReal.ofReal tail * (Fintype.card iota : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2) := by gcongr
    _ = (16 * ENNReal.ofReal tail) *
          ((Fintype.card iota : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)) := by
      rw [div_eq_mul_inv]
      have hcancel : (2 : ENNReal)⁻¹ * 2 = 1 :=
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      have htwo : (2 : ENNReal)⁻¹ * 16 = 8 := by
        calc
          _ = ((2 : ENNReal)⁻¹ * 2) * 8 := by ring
          _ = 8 := by rw [hcancel, one_mul]
      calc
        (ENNReal.ofReal tail * (Fintype.card iota : ENNReal)) *
            (8 * (delta : ENNReal) ^ 2) =
          ENNReal.ofReal tail * (Fintype.card iota : ENNReal) *
            (delta : ENNReal) ^ 2 * 8 := by ac_rfl
        _ = ENNReal.ofReal tail * (Fintype.card iota : ENNReal) *
            (delta : ENNReal) ^ 2 * ((2 : ENNReal)⁻¹ * 16) := by rw [htwo]
        _ = (16 * ENNReal.ofReal tail) *
            ((Fintype.card iota : ENNReal) *
              ((delta : ENNReal) ^ 2 * (2 : ENNReal)⁻¹)) := by ac_rfl
    _ <= (16 * ENNReal.ofReal tail) * D.actualFamilyVolume := by gcongr

/-- Mass retention and the cross-multiplied volume estimate cancel the
sampling multiplicity exactly.  Only `32 * tail` remains in density. -/
theorem source_shadingDensity_le_thirtyTwo_tail_mul_zeroColor
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (k : Nat) [NeZero k] (omega : iota -> Fin k) (tail : Real)
    (hretained :
      D.shading.shadingMass.toReal / (2 * (k : Real)) <=
        (zeroColorActualDatum D k omega).shading.shadingMass.toReal)
    (hscaledCard :
      (k : ENNReal) * ((zeroColorSample k omega).card : ENNReal) <=
        ENNReal.ofReal tail * (Fintype.card iota : ENNReal)) :
    D.shading.shadingDensity <=
      (32 * ENNReal.ofReal tail) *
        (zeroColorActualDatum D k omega).shading.shadingDensity := by
  let sampled := zeroColorActualDatum D k omega
  have hmass : D.shading.shadingMass <=
      ((2 * k : Nat) : ENNReal) * sampled.shading.shadingMass := by
    simpa [sampled] using
      shadingMass_le_two_mul_k_mul_of_toReal_div_le D k omega hretained
  have hvolume :
      (k : ENNReal) * familyVolume sampled.family.bodyFamily <=
        (16 * ENNReal.ofReal tail) * familyVolume D.family.bodyFamily := by
    simpa [sampled, ActualTubeDatum.actualFamilyVolume] using
      zeroColorActualDatum_volume_cross_le
        D hdeltaHalf k omega tail hscaledCard
  by_cases hzero : familyVolume D.family.bodyFamily = 0
  · have hmassZero : D.shading.shadingMass = 0 :=
      nonpos_iff_eq_zero.mp
        (D.shading.shadingMass_le_familyVolume.trans_eq hzero)
    simp [Shading.shadingDensity, hzero, hmassZero]
  · rw [← ENNReal.mul_le_mul_iff_right hzero
      (familyVolume_ne_top D.family.bodyFamily)]
    calc
      familyVolume D.family.bodyFamily * D.shading.shadingDensity =
          D.shading.shadingMass := by
        rw [mul_comm, shadingDensity_mul_familyVolume]
      _ <= ((2 * k : Nat) : ENNReal) * sampled.shading.shadingMass := hmass
      _ = 2 * sampled.shading.shadingDensity *
          ((k : ENNReal) * familyVolume sampled.family.bodyFamily) := by
        rw [← shadingDensity_mul_familyVolume]
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        ac_rfl
      _ <= 2 * sampled.shading.shadingDensity *
          ((16 * ENNReal.ofReal tail) *
            familyVolume D.family.bodyFamily) := by gcongr
      _ = familyVolume D.family.bodyFamily *
          ((32 * ENNReal.ofReal tail) *
            sampled.shading.shadingDensity) := by
        calc
          2 * sampled.shading.shadingDensity *
              ((16 * ENNReal.ofReal tail) *
                familyVolume D.family.bodyFamily) =
            familyVolume D.family.bodyFamily *
              (((2 : ENNReal) * 16 * ENNReal.ofReal tail) *
                sampled.shading.shadingDensity) := by ac_rfl
          _ = familyVolume D.family.bodyFamily *
              ((32 * ENNReal.ofReal tail) *
                sampled.shading.shadingDensity) := by norm_num

/-- A real-valued selected-card estimate supplies the cross-multiplied
`ENNReal` cardinal estimate, provided the sampling multiplicity does not
exceed the source cardinality. -/
theorem scaledCard_le_tail_mul_card_of_real_bound
    {iota : Type} [Fintype iota]
    (k : Nat) [NeZero k] (selected : Finset iota) (tail : Real)
    (htail : 0 <= tail)
    (hkCard : k <= Fintype.card iota)
    (hcard :
      (selected.card : Real) <=
        tail * averageZeroColorCardinalCap iota k) :
    (k : ENNReal) * (selected.card : ENNReal) <=
      ENNReal.ofReal tail * (Fintype.card iota : ENNReal) := by
  have hkReal : 0 < (k : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hratio :
      (1 : Real) <= (Fintype.card iota : Real) / (k : Real) := by
    apply (le_div_iff₀ hkReal).2
    have hkCardReal : (k : Real) <= (Fintype.card iota : Real) := by
      exact_mod_cast hkCard
    simpa only [one_mul] using hkCardReal
  have hcap : averageZeroColorCardinalCap iota k =
      (Fintype.card iota : Real) / (k : Real) := by
    exact max_eq_right hratio
  have hscaledReal :
      (k : Real) * (selected.card : Real) <=
        tail * (Fintype.card iota : Real) := by
    calc
      (k : Real) * (selected.card : Real) <=
          (k : Real) *
            (tail * ((Fintype.card iota : Real) / (k : Real))) := by
        gcongr
        simpa [hcap] using hcard
      _ = tail * (Fintype.card iota : Real) := by
        field_simp
  have hleftTop :
      (k : ENNReal) * (selected.card : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have hrightTop :
      ENNReal.ofReal tail * (Fintype.card iota : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  apply (ENNReal.toReal_le_toReal hleftTop hrightTop).mp
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal htail] using hscaledReal

/-- Direct consumer for the real cardinality conclusion of the simultaneous
polynomial-John zero-colour selector. -/
theorem source_shadingDensity_le_thirtyTwo_tail_mul_zeroColor_of_real_card
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (k : Nat) [NeZero k] (omega : iota -> Fin k) (tail : Real)
    (htail : 0 <= tail)
    (hkCard : k <= Fintype.card iota)
    (hretained :
      D.shading.shadingMass.toReal / (2 * (k : Real)) <=
        (zeroColorActualDatum D k omega).shading.shadingMass.toReal)
    (hcard :
      ((zeroColorSample k omega).card : Real) <=
        tail * averageZeroColorCardinalCap iota k) :
    D.shading.shadingDensity <=
      (32 * ENNReal.ofReal tail) *
        (zeroColorActualDatum D k omega).shading.shadingDensity := by
  apply source_shadingDensity_le_thirtyTwo_tail_mul_zeroColor
    D hdeltaHalf k omega tail hretained
  exact scaledCard_le_tail_mul_card_of_real_bound
    k (zeroColorSample k omega) tail htail hkCard hcard

#print axioms zeroColorActualDatum_volume_cross_le
#print axioms source_shadingDensity_le_thirtyTwo_tail_mul_zeroColor
#print axioms scaledCard_le_tail_mul_card_of_real_bound
#print axioms source_shadingDensity_le_thirtyTwo_tail_mul_zeroColor_of_real_card

end
end Family8ZeroColorSampledDensityCardCancellationV1

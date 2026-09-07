import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8FrostmanExponentTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# Closing a Frostman exponent by an epsilon limit

For `lower <= upper`, direct pointwise comparison of the two Frostman right-
hand sides would require

`actualFamilyVolume <= delta ^ (-4)`.

Indeed, their ratio is a nonnegative power of
`delta ^ (-4) / actualFamilyVolume`.  The current admissibility structure
contains pairwise volume-overlap essential distinctness, but the repository
does not yet contain the global parameter-space packing theorem needed to
deduce that summed-volume upper bound.  Essential distinctness currently
only supplies injectivity of the tube map, not a quantitative global card
bound.  Thus this file does not present a conditional monotonicity facade.

What is unconditional, and is enough for a limit closure, is the reverse
input: a nonempty actual family has volume at least `delta^2 / 2`.  Applying
`K_F(beta + epsilon/8)` with loss `epsilon/2` then gives exactly the desired
`K_F(beta)` right-hand side.  Empty index types are discharged separately.
-/

/-- A nonempty actual tube family contains one full tube-volume contribution. -/
theorem half_delta_sq_le_actualFamilyVolume_of_nonempty
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hiota : Nonempty iota)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    (delta : ENNReal) ^ 2 / 2 ≤ D.actualFamilyVolume := by
  let i : iota := Classical.choice hiota
  calc
    (delta : ENNReal) ^ 2 / 2 ≤ volume (D.family.tubes i).carrier :=
      (D.family.tubes i).half_sq_le_volume_of_le_half hdeltaHalf
    _ ≤ ∑ j : iota, volume (D.family.tubes j).carrier := by
      exact Finset.single_le_sum
        (fun j _ ↦ show (0 : ENNReal) ≤ volume (D.family.tubes j).carrier
          from bot_le)
        (Finset.mem_univ i)
    _ = D.actualFamilyVolume := by
      simp only [ActualTubeDatum.actualFamilyVolume, familyVolume,
        UniformTubeFamily.bodyFamily, Tube.coe_body]

/-- At radius at most one half, the fourth power of the radius is bounded by
the volume floor `delta^2 / 2`. -/
theorem delta_four_le_half_delta_sq
    {delta : NNReal} (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    (delta : ENNReal) ^ 4 ≤ (delta : ENNReal) ^ 2 / 2 := by
  have hdeltaENN :
      (delta : ENNReal) ≤ (2 : ENNReal)⁻¹ := by
    simpa only [ENNReal.coe_inv_two] using ENNReal.coe_le_coe.mpr hdeltaHalf
  have hdeltaSq : (delta : ENNReal) ^ 2 ≤ (2 : ENNReal)⁻¹ := by
    calc
      (delta : ENNReal) ^ 2 =
          (delta : ENNReal) * (delta : ENNReal) := by ring
      _ ≤ (delta : ENNReal) * 1 := by
        gcongr
        exact hdeltaENN.trans (by norm_num)
      _ = (delta : ENNReal) := by simp
      _ ≤ (2 : ENNReal)⁻¹ := hdeltaENN
  calc
    (delta : ENNReal) ^ 4 =
        (delta : ENNReal) ^ 2 * (delta : ENNReal) ^ 2 := by ring
    _ ≤ (delta : ENNReal) ^ 2 * (2 : ENNReal)⁻¹ := by
      gcongr
    _ = (delta : ENNReal) ^ 2 / 2 := by
      rw [div_eq_mul_inv]

/-- The exact numerical epsilon absorption.  No upper bound on the number
of tubes is used. -/
theorem frostmanMultiplicityRHS_eighth_step_le
    {delta : NNReal} {actualVolume : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hepsilon : 0 < epsilon)
    (hvolumeLower : (delta : ENNReal) ^ 2 / 2 ≤ actualVolume)
    (hvolumeTop : actualVolume ≠ ∞) :
    frostmanMultiplicityRHS delta actualVolume (epsilon / 2)
        (beta + epsilon / 8) ≤
      frostmanMultiplicityRHS delta actualVolume epsilon beta := by
  let d : ENNReal := (delta : ENNReal)
  let p : Real := epsilon / 16
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hvolumePos : 0 < actualVolume := by
    have hfloorPos : 0 < (delta : ENNReal) ^ 2 / 2 :=
      ENNReal.div_pos (pow_ne_zero 2 hd0) (by norm_num)
    exact hfloorPos.trans_le hvolumeLower
  have hvolume0 : actualVolume ≠ 0 := hvolumePos.ne'
  have hp : 0 ≤ p := by
    dsimp only [p]
    positivity
  have hdeltaFourVolume : d ^ 4 ≤ actualVolume := by
    exact (delta_four_le_half_delta_sq hdeltaHalf).trans hvolumeLower
  have hratio : d ^ 4 * actualVolume⁻¹ ≤ 1 := by
    calc
      d ^ 4 * actualVolume⁻¹ ≤ actualVolume * actualVolume⁻¹ := by
        gcongr
      _ = 1 := ENNReal.mul_inv_cancel hvolume0 hvolumeTop
  have hfactor : (d ^ 4 * actualVolume⁻¹) ^ p ≤ 1 := by
    exact ENNReal.rpow_le_one hratio hp
  have hfactorIdentity :
      d ^ (epsilon / 4) * actualVolume ^ (-epsilon / 16) =
        (d ^ 4 * actualVolume⁻¹) ^ p := by
    have hfour : epsilon / 4 = (4 : Real) * p := by
      dsimp only [p]
      ring
    have hsixteen : -epsilon / 16 = -p := by
      dsimp only [p]
      ring
    rw [hfour, ENNReal.rpow_mul, ENNReal.rpow_ofNat, hsixteen,
      ENNReal.rpow_neg, ← ENNReal.inv_rpow,
      ENNReal.mul_rpow_of_nonneg _ _ hp]
  have hleftCombined :
      frostmanMultiplicityRHS delta actualVolume (epsilon / 2)
          (beta + epsilon / 8) =
        d ^ (-epsilon / 2 - 2 * (beta + epsilon / 8)) *
          actualVolume ^ (1 - (beta + epsilon / 8) / 2) := by
    unfold frostmanMultiplicityRHS
    dsimp only [d]
    calc
      (delta : ENNReal) ^ (-(epsilon / 2)) *
            (delta : ENNReal) ^ (-2 * (beta + epsilon / 8)) *
            actualVolume ^ (1 - (beta + epsilon / 8) / 2) =
          (delta : ENNReal) ^
              (-(epsilon / 2) + (-2 * (beta + epsilon / 8))) *
            actualVolume ^ (1 - (beta + epsilon / 8) / 2) := by
        rw [ENNReal.rpow_add (-(epsilon / 2))
          (-2 * (beta + epsilon / 8)) hd0 hdTop]
      _ = (delta : ENNReal) ^
            (-epsilon / 2 - 2 * (beta + epsilon / 8)) *
            actualVolume ^ (1 - (beta + epsilon / 8) / 2) := by
        congr 2
        ring
  have hrightCombined :
      frostmanMultiplicityRHS delta actualVolume epsilon beta =
        d ^ (-epsilon - 2 * beta) *
          actualVolume ^ (1 - beta / 2) := by
    unfold frostmanMultiplicityRHS
    dsimp only [d]
    calc
      (delta : ENNReal) ^ (-epsilon) *
            (delta : ENNReal) ^ (-2 * beta) *
            actualVolume ^ (1 - beta / 2) =
          (delta : ENNReal) ^ ((-epsilon) + (-2 * beta)) *
            actualVolume ^ (1 - beta / 2) := by
        rw [ENNReal.rpow_add (-epsilon) (-2 * beta) hd0 hdTop]
      _ = (delta : ENNReal) ^ (-epsilon - 2 * beta) *
            actualVolume ^ (1 - beta / 2) := by
        congr 2
        ring
  rw [hleftCombined, hrightCombined]
  have hdeltaExponent :
      -epsilon / 2 - 2 * (beta + epsilon / 8) =
        (-epsilon - 2 * beta) + epsilon / 4 := by ring
  have hvolumeExponent :
      1 - (beta + epsilon / 8) / 2 =
        (1 - beta / 2) + (-epsilon / 16) := by ring
  rw [hdeltaExponent,
    ENNReal.rpow_add (-epsilon - 2 * beta) (epsilon / 4) hd0 hdTop,
    hvolumeExponent,
    ENNReal.rpow_add (1 - beta / 2) (-epsilon / 16)
      hvolume0 hvolumeTop]
  calc
    (d ^ (-epsilon - 2 * beta) * d ^ (epsilon / 4)) *
          (actualVolume ^ (1 - beta / 2) *
            actualVolume ^ (-epsilon / 16)) =
        (d ^ (-epsilon - 2 * beta) *
          actualVolume ^ (1 - beta / 2)) *
            (d ^ (epsilon / 4) * actualVolume ^ (-epsilon / 16)) := by
      ac_rfl
    _ = (d ^ (-epsilon - 2 * beta) *
          actualVolume ^ (1 - beta / 2)) *
            (d ^ 4 * actualVolume⁻¹) ^ p := by
      rw [hfactorIdentity]
    _ ≤ (d ^ (-epsilon - 2 * beta) *
          actualVolume ^ (1 - beta / 2)) * 1 := by
      gcongr
    _ = d ^ (-epsilon - 2 * beta) *
          actualVolume ^ (1 - beta / 2) := by simp

/-- Epsilon-limit closure for the paper's Frostman property.

This is the unconditional replacement for the unavailable direct exponent
transport: if `K_F(gamma)` is known for every `gamma > beta`, then
`K_F(beta)` holds. -/
theorem frostmanProperty_of_forall_gt
    {beta : Real}
    (hall : ∀ gamma : Real, beta < gamma → FrostmanProperty gamma) :
    FrostmanProperty beta := by
  intro epsilon hepsilon
  let gamma : Real := beta + epsilon / 8
  have hbetaGamma : beta < gamma := by
    dsimp only [gamma]
    linarith
  have hhalfEpsilon : 0 < epsilon / 2 := by positivity
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half, hsource⟩ :=
    (hall gamma hbetaGamma).exists_parameters hhalfEpsilon
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_⟩
  intro delta iota _ _ D hD hdelta hF
  by_cases hiota : Nonempty iota
  · have hsourceBound :
        D.shading.averageMultiplicity ≤
          frostmanMultiplicityRHS delta D.actualFamilyVolume
            (epsilon / 2) gamma :=
      hsource delta iota D hD hdelta hF
    have hvolumeLower :
        (delta : ENNReal) ^ 2 / 2 ≤ D.actualFamilyVolume :=
      half_delta_sq_le_actualFamilyVolume_of_nonempty D hiota hD.delta_le_half
    have hnumeric :
        frostmanMultiplicityRHS delta D.actualFamilyVolume
            (epsilon / 2) gamma ≤
          frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta := by
      simpa only [gamma] using
        frostmanMultiplicityRHS_eighth_step_le
          hD.delta_pos hD.delta_le_half hepsilon hvolumeLower
            (familyVolume_ne_top D.family.bodyFamily)
    exact hsourceBound.trans hnumeric
  · let _ : IsEmpty iota := ⟨fun i ↦ hiota ⟨i⟩⟩
    simp [Shading.averageMultiplicity, Shading.shadingMass,
      Shading.shadedUnion]

#print axioms half_delta_sq_le_actualFamilyVolume_of_nonempty
#print axioms delta_four_le_half_delta_sq
#print axioms frostmanMultiplicityRHS_eighth_step_le
#print axioms frostmanProperty_of_forall_gt

end

end Family8FrostmanExponentTransportV1

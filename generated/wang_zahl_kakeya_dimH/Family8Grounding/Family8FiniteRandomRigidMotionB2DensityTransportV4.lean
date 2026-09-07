import Family8Grounding.Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2DensityTransportV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1

noncomputable section

/-!
# Density retained by honest B2 normalization

The normalized shading mass is exactly `1/512` of the source mass, while
the sum of normalized tube volumes is at most `1/4` of the source family
volume.  Consequently normalization retains at least `1/128` of the source
shading density.  This is the scalar input needed for the fixed-John power
absorption and is proved without a density callback.
-/

/-- The normalized family-volume denominator loses at most a factor four. -/
theorem eighthNormalizedDatum_familyVolume_le_quarter
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    familyVolume (eighthNormalizedDatum D).family.bodyFamily ≤
      (1 / 4 : ENNReal) * familyVolume D.family.bodyFamily := by
  unfold familyVolume
  calc
    (∑ i, volume
        ((eighthNormalizedDatum D).family.bodyFamily i : Set Space)) ≤
        ∑ i, (1 / 4 : ENNReal) *
          volume (D.family.bodyFamily i : Set Space) := by
      exact Finset.sum_le_sum fun i _hi => by
        simpa only [eighthNormalizedDatum, eighthNormalizedTubeFamily,
          UniformTubeFamily.bodyFamily, Tube.coe_body] using
          eighthNormalizedTube_volume_le_quarter
            (D.family.tubes i) hdeltaHalf
    _ = (1 / 4 : ENNReal) *
        ∑ i, volume (D.family.bodyFamily i : Set Space) := by
      rw [Finset.mul_sum]

/-- A nonempty admissible actual tube family has positive total volume. -/
theorem actualDatum_familyVolume_pos
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    0 < familyVolume D.family.bodyFamily := by
  classical
  let i : iota := Classical.choice (inferInstance : Nonempty iota)
  have hi : 0 < volume (D.family.tubes i).carrier :=
    Tube.volume_pos (D.family.tubes i) hD.delta_pos
  unfold familyVolume
  have hle :
      volume (D.family.tubes i).carrier ≤
        ∑ j, volume (D.family.tubes j).carrier :=
    Finset.single_le_sum
      (f := fun j : iota => volume (D.family.tubes j).carrier)
      (fun _ _ => bot_le) (Finset.mem_univ i)
  exact hi.trans_le (by
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using hle)

/-- Honest normalization retains at least one eighth-cubed divided by the
one-quarter tube-volume loss, namely `1/128`, of shading density. -/
theorem source_shadingDensity_div_128_le_eighthNormalized
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    D.shading.shadingDensity / 128 ≤
      (eighthNormalizedDatum D).shading.shadingDensity := by
  have hfamily := eighthNormalizedDatum_familyVolume_le_quarter
    D hD.delta_le_half
  have hmassTop : D.shading.shadingMass ≠ ∞ :=
    D.shading.shadingMass_lt_top.ne
  have hvolumeTop : familyVolume D.family.bodyFamily ≠ ∞ :=
    familyVolume_ne_top D.family.bodyFamily
  have hvolumeZero : familyVolume D.family.bodyFamily ≠ 0 :=
    (actualDatum_familyVolume_pos D hD).ne'
  have hleftTop :
      D.shading.shadingMass / familyVolume D.family.bodyFamily / 128 ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.div_ne_top hmassTop hvolumeZero) (by norm_num)
  have hrightTop :
      ((1 / 512 : ENNReal) * D.shading.shadingMass) /
          ((1 / 4 : ENNReal) * familyVolume D.family.bodyFamily) ≠ ∞ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (by norm_num) hmassTop
    · exact mul_ne_zero (by norm_num) hvolumeZero
  unfold Shading.shadingDensity
  change D.shading.shadingMass / familyVolume D.family.bodyFamily / 128 ≤
    (eighthNormalizedShading D.family D.shading).shadingMass /
      familyVolume (eighthNormalizedDatum D).family.bodyFamily
  rw [eighthNormalizedShading_shadingMass]
  calc
    D.shading.shadingMass / familyVolume D.family.bodyFamily / 128 =
        ((1 / 512 : ENNReal) * D.shading.shadingMass) /
          ((1 / 4 : ENNReal) * familyVolume D.family.bodyFamily) := by
      apply (ENNReal.toReal_eq_toReal_iff' hleftTop hrightTop).mp
      norm_num [ENNReal.toReal_div, ENNReal.toReal_mul]
      ring
    _ ≤ ((1 / 512 : ENNReal) * D.shading.shadingMass) /
          familyVolume (eighthNormalizedDatum D).family.bodyFamily :=
      ENNReal.div_le_div_left hfamily _

#print axioms eighthNormalizedDatum_familyVolume_le_quarter
#print axioms actualDatum_familyVolume_pos
#print axioms source_shadingDensity_div_128_le_eighthNormalized

end
end Family8FiniteRandomRigidMotionB2DensityTransportV4

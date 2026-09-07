import Family8Grounding.Family8FiniteRandomRigidMotionB2DensityTransportV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrozenCoarseB2DensityTransportScaleOnlyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2DensityTransportV4

noncomputable section

/-!
# B2 normalization density transport from scale data only

The factor-128 density calculation uses only positive tube scale,
half-scale volume bounds, and a nonempty index type.  Raw frozen coarse
parents need not be pairwise essentially distinct or lie in the unit ball;
those properties are manufactured after normalization and fresh selection.
-/

/-- A nonempty uniform tube family at positive radius has positive total
family volume, without any admissibility premise. -/
theorem actualDatum_familyVolume_pos_of_scale
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdeltaPos : 0 < delta) :
    0 < familyVolume D.family.bodyFamily := by
  classical
  let i : iota := Classical.choice (inferInstance : Nonempty iota)
  have hi : 0 < volume (D.family.tubes i).carrier :=
    Tube.volume_pos (D.family.tubes i) hdeltaPos
  unfold familyVolume
  have hle :
      volume (D.family.tubes i).carrier <=
        ∑ j, volume (D.family.tubes j).carrier :=
    Finset.single_le_sum
      (f := fun j : iota => volume (D.family.tubes j).carrier)
      (fun _ _ => bot_le) (Finset.mem_univ i)
  exact hi.trans_le (by
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using hle)

/-- Honest eighth normalization retains at least one factor `1/128` of
source density under the exact scale hypotheses already available for a
frozen coarse family. -/
theorem source_shadingDensity_div_128_le_eighthNormalized_of_scale
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    D.shading.shadingDensity / 128 <=
      (eighthNormalizedDatum D).shading.shadingDensity := by
  have hfamily := eighthNormalizedDatum_familyVolume_le_quarter
    D hdeltaHalf
  have hmassTop : D.shading.shadingMass ≠ ∞ :=
    D.shading.shadingMass_lt_top.ne
  have hvolumeTop : familyVolume D.family.bodyFamily ≠ ∞ :=
    familyVolume_ne_top D.family.bodyFamily
  have hvolumeZero : familyVolume D.family.bodyFamily ≠ 0 :=
    (actualDatum_familyVolume_pos_of_scale D hdeltaPos).ne'
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
  change D.shading.shadingMass / familyVolume D.family.bodyFamily / 128 <=
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
    _ <= ((1 / 512 : ENNReal) * D.shading.shadingMass) /
          familyVolume (eighthNormalizedDatum D).family.bodyFamily :=
      ENNReal.div_le_div_left hfamily _

#print axioms actualDatum_familyVolume_pos_of_scale
#print axioms
  source_shadingDensity_div_128_le_eighthNormalized_of_scale

end
end Family8FrozenCoarseB2DensityTransportScaleOnlyV1

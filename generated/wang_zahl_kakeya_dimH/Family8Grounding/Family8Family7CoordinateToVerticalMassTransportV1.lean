import Family8Grounding.Family8Family7CoordinateToVerticalShadingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CoordinateToVerticalMassTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalShadingV1
open Family8GeneralizedFrostmanMultiplicityV1

noncomputable section

universe u

/-! # Exact summed-mass transport under the coordinate permutation -/

theorem coordinateToVerticalShading_shadingMass
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) :
    (coordinateToVerticalShading k F Y).shadingMass = Y.shadingMass := by
  unfold Shading.shadingMass
  apply Finset.sum_congr rfl
  intro i _hi
  rw [coordinateToVerticalShading_carrier,
    volume_rigidMotion_image]

theorem coordinateToVerticalFamily_familyVolume
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota) :
    familyVolume (coordinateToVerticalFamily k F).bodyFamily =
      familyVolume F.bodyFamily := by
  unfold familyVolume
  apply Finset.sum_congr rfl
  intro i _hi
  rw [UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
    coordinateToVerticalFamily_tubes,
    rigidTube_volume,
    UniformTubeFamily.bodyFamily_apply, Tube.coe_body]

theorem coordinateToVerticalShading_shadingDensity
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) :
    (coordinateToVerticalShading k F Y).shadingDensity =
      Y.shadingDensity := by
  unfold Shading.shadingDensity
  rw [coordinateToVerticalShading_shadingMass,
    coordinateToVerticalFamily_familyVolume]

#print axioms coordinateToVerticalShading_shadingMass
#print axioms coordinateToVerticalFamily_familyVolume
#print axioms coordinateToVerticalShading_shadingDensity

end

end Family8Family7CoordinateToVerticalMassTransportV1

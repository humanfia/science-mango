import Family8Grounding.Family8Family7CoordinateToVerticalMassTransportV1
import Family8Grounding.Family8GeneralizedFrostmanMultiplicityV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection

/-!
# Selected-subtype density under the coordinate permutation, V3

V1 omitted the selected-coarse namespace and V2 omitted the rigid-motion
volume namespace.  This clean successor keeps the literal selected subtype
and the same three exact identities while declaring both dependencies.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CoordinateToVerticalSelectedSubtypeDensityV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalMassTransportV1
open Family8Family7CoordinateToVerticalShadingV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8GeneralizedFrostmanMultiplicityV1

noncomputable section

universe u

theorem coordinateToVertical_selectedCoarseFamily_familyVolume
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    (s : Finset iota) :
    familyVolume
        (selectedCoarseFamily
          (coordinateToVerticalFamily axis F).bodyFamily s) =
      familyVolume (selectedCoarseFamily F.bodyFamily s) := by
  rw [selectedCoarseFamily_volume, selectedCoarseFamily_volume]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
    coordinateToVerticalFamily_tubes, rigidTube_volume,
    UniformTubeFamily.bodyFamily_apply, Tube.coe_body]

theorem coordinateToVertical_selectedCoarseShading_shadingMass
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) (s : Finset iota) :
    (selectedCoarseShading
      (coordinateToVerticalShading axis F Y) s).shadingMass =
        (selectedCoarseShading Y s).shadingMass := by
  rw [selectedCoarseShading_mass, selectedCoarseShading_mass]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [coordinateToVerticalShading_carrier,
    volume_rigidMotion_image]

/-- Exact selected-subtype density identity under the same coordinate
permutation. -/
theorem coordinateToVertical_selectedCoarseShading_shadingDensity
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) (s : Finset iota) :
    (selectedCoarseShading
      (coordinateToVerticalShading axis F Y) s).shadingDensity =
        (selectedCoarseShading Y s).shadingDensity := by
  unfold Shading.shadingDensity
  rw [coordinateToVertical_selectedCoarseShading_shadingMass,
    coordinateToVertical_selectedCoarseFamily_familyVolume]

#print axioms coordinateToVertical_selectedCoarseFamily_familyVolume
#print axioms coordinateToVertical_selectedCoarseShading_shadingMass
#print axioms coordinateToVertical_selectedCoarseShading_shadingDensity

end
end Family8Family7CoordinateToVerticalSelectedSubtypeDensityV3

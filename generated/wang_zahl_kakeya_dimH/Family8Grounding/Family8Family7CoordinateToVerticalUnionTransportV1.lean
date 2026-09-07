import Family8Grounding.Family8Family7CoordinateToVerticalMassTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CoordinateToVerticalUnionTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalShadingV1
open Family8Family7CoordinateToVerticalMassTransportV1
open Family8GeneralizedFrostmanMultiplicityV1

noncomputable section

universe u

/-! # Exact union and average-multiplicity transport -/

theorem coordinateToVerticalShading_shadedUnion
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) :
    (coordinateToVerticalShading k F Y).shadedUnion =
      coordinateToVerticalRigidMotion k '' Y.shadedUnion := by
  simp only [Shading.shadedUnion, coordinateToVerticalShading_carrier,
    Set.image_iUnion]

theorem coordinateToVerticalShading_shadedUnion_volume
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) :
    volume (coordinateToVerticalShading k F Y).shadedUnion =
      volume Y.shadedUnion := by
  rw [coordinateToVerticalShading_shadedUnion,
    volume_rigidMotion_image]

theorem coordinateToVerticalShading_averageMultiplicity
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) :
    (coordinateToVerticalShading k F Y).averageMultiplicity =
      Y.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [coordinateToVerticalShading_shadingMass,
    coordinateToVerticalShading_shadedUnion_volume]

#print axioms coordinateToVerticalShading_shadedUnion
#print axioms coordinateToVerticalShading_shadedUnion_volume
#print axioms coordinateToVerticalShading_averageMultiplicity

end

end Family8Family7CoordinateToVerticalUnionTransportV1

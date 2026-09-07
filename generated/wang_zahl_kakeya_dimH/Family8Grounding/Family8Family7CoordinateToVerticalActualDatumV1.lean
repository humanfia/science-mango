import Family8Grounding.Family8Family7CoordinateToVerticalUnionTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CoordinateToVerticalActualDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalShadingV1
open Family8Family7CoordinateToVerticalMassTransportV1
open Family8Family7CoordinateToVerticalUnionTransportV1

noncomputable section

/-! # Same-index actual-datum and admissibility transport -/

def coordinateToVerticalActualDatum
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (D : ActualTubeDatum delta iota) :
    ActualTubeDatum delta iota where
  family := coordinateToVerticalFamily k D.family
  shading := coordinateToVerticalShading k D.family D.shading

@[simp] theorem coordinateToVerticalActualDatum_family
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (D : ActualTubeDatum delta iota) :
    (coordinateToVerticalActualDatum k D).family =
      coordinateToVerticalFamily k D.family :=
  rfl

@[simp] theorem coordinateToVerticalActualDatum_shading
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (D : ActualTubeDatum delta iota) :
    (coordinateToVerticalActualDatum k D).shading =
      coordinateToVerticalShading k D.family D.shading :=
  rfl

theorem coordinateToVerticalActualDatum_actualFamilyVolume
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (D : ActualTubeDatum delta iota) :
    (coordinateToVerticalActualDatum k D).actualFamilyVolume =
      D.actualFamilyVolume := by
  unfold ActualTubeDatum.actualFamilyVolume
  exact coordinateToVerticalFamily_familyVolume k D.family

theorem coordinateToVerticalActualDatum_isAdmissible
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible) :
    (coordinateToVerticalActualDatum k D).IsAdmissible where
  delta_pos := hD.delta_pos
  delta_le_half := hD.delta_le_half
  contained_in_unit_ball i := by
    rw [coordinateToVerticalActualDatum_family,
      coordinateToVerticalFamily_tubes,
      rigidTube_coordinateToVertical_carrier]
    rintro _x ⟨y, hy, rfl⟩
    have hyBall := hD.contained_in_unit_ball i hy
    rw [Metric.mem_closedBall] at hyBall ⊢
    calc
      dist (coordinateToVerticalRigidMotion k y) 0 =
          dist (coordinateToVerticalRigidMotion k y)
            (coordinateToVerticalRigidMotion k 0) := by
        rw [coordinateToVerticalRigidMotion_zero]
      _ = dist y 0 :=
        (coordinateToVerticalRigidMotion k).isometry.dist_eq y 0
      _ ≤ 1 := hyBall
  pairwise_essentiallyDistinct := by
    intro i _hi j _hj hij
    rw [coordinateToVerticalActualDatum_family,
      coordinateToVerticalFamily_tubes,
      coordinateToVerticalFamily_tubes,
      essentiallyDistinct_rigidTube_iff]
    exact hD.pairwise_essentiallyDistinct
      (Set.mem_univ i) (Set.mem_univ j) hij

#print axioms coordinateToVerticalActualDatum
#print axioms coordinateToVerticalActualDatum_actualFamilyVolume
#print axioms coordinateToVerticalActualDatum_isAdmissible

end

end Family8Family7CoordinateToVerticalActualDatumV1

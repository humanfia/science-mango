import FamilyStickyGrounding.FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
import FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
import FamilyStickyCinematicL32ProjectedTubeVerticalCarrierStripV1
import FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
import Mathlib.Tactic

/-!
# Honest graph-strip support for a projected actual tube

The image of a radius-`r` tube in the zero cinematic chart is not, in
general, supported in the radius-`r` vertical strip: changing the height by
`r` moves a graph of slope at most two by another `2r`.  The literal bound
available from the fixed vertical chart is therefore `3r`.

This file records only that geometric containment.  It has no quasi-product,
active-cardinality, or multiplicity hypothesis.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8ProjectedTubeImageGraphStripSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32ProjectedTubeVerticalCarrierStripV1
open FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1

noncomputable section

/-- In the zero cinematic chart, a projected actual tube lies in the
three-radius vertical neighborhood of its literal graph. -/
theorem projectedTubeImageCarrier_subset_verticalCarrier_univ_three
    {radius : NNReal} (T : Tube radius)
    (hvertical : (1 / 2 : Real) <= |T.axis.direction 2|) :
    projectedTubeImageCarrier (fun _ => 0) T ⊆
      projectedTubeVerticalCarrier (fun _ => 0) Set.univ
        (3 * (radius : Real)) T := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hvertical_ne : T.axis.direction 2 ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  obtain ⟨t, _ht, hx, _hy, hz⟩ :=
    tubeCarrier_subset_coordinateLineTube T hvertical_ne hp
  have hC : |tubeGraphC T| <= 2 := by
    simpa only [tubeGraphC, projectedTubeGraphC] using
      abs_projectedTubeGraphC_le_two_of_vertical_half hvertical
  have hzt : |t - p 2| <= (radius : Real) := by
    simpa only [abs_sub_comm] using hz
  have hshift : |tubeGraphC T * (t - p 2)| <=
      2 * (radius : Real) := by
    rw [abs_mul]
    exact mul_le_mul hC hzt (abs_nonneg _) (by norm_num)
  refine ⟨Set.mem_univ _, ?_⟩
  simp only [projectedTwistedProjection, zero_mul, add_zero]
  change
    |p 0 - projectedTubeCinematicTrace (fun _ => 0) T (p 2)| <=
      3 * (radius : Real)
  calc
    |p 0 - projectedTubeCinematicTrace (fun _ => 0) T (p 2)| =
        |(p 0 - (tubeGraphA T + tubeGraphC T * t)) +
          tubeGraphC T * (t - p 2)| := by
      congr 1
      simp only [projectedTubeCinematicTrace, projectedTubeGraphA,
        projectedTubeGraphB, projectedTubeGraphC, projectedTubeGraphD,
        tubeGraphA, tubeGraphC, zero_mul, add_zero]
      ring
    _ <= |p 0 - (tubeGraphA T + tubeGraphC T * t)| +
        |tubeGraphC T * (t - p 2)| := abs_add_le _ _
    _ <= (radius : Real) + 2 * (radius : Real) :=
      add_le_add hx hshift
    _ = 3 * (radius : Real) := by ring

/-- If the actual tube is supported in the radius-two ambient ball, its
zero-chart image is in the explicit parameter strip `[-2,2]`, with the
honest three-radius transverse width. -/
theorem projectedTubeImageCarrier_subset_pyzGraphStrip_negTwo_two_three
    {radius : NNReal} (T : Tube radius)
    (hvertical : (1 / 2 : Real) <= |T.axis.direction 2|)
    (hB2 : T.carrier ⊆ Metric.closedBall (0 : Space) 2) :
    projectedTubeImageCarrier (fun _ => 0) T ⊆
      pyzCarrierGraphStrip (-2) 2
        (projectedTubeCinematicTrace (fun _ => 0) T)
        (3 * (radius : Real)) := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := hq
  have hpNorm : ‖p‖ <= 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hB2 hp
  have hp2abs : |p 2| <= 2 := by
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le p (2 : Fin 3)).trans hpNorm
  have hparameter : (projectedTwistedProjection (fun _ => 0) p).2 ∈
      Set.Icc (-2 : Real) 2 := by
    simp only [projectedTwistedProjection]
    exact abs_le.mp hp2abs
  have hverticalCarrier :=
    projectedTubeImageCarrier_subset_verticalCarrier_univ_three
      T hvertical ⟨p, hp, hpq⟩
  rw [← projectedTubeVerticalCarrier_Icc_eq_pyzCarrierGraphStrip]
  rw [mem_projectedTubeVerticalCarrier]
  refine ⟨?_, ?_⟩
  · simpa only [hpq] using hparameter
  · exact hverticalCarrier.2

#print axioms projectedTubeImageCarrier_subset_verticalCarrier_univ_three
#print axioms
  projectedTubeImageCarrier_subset_pyzGraphStrip_negTwo_two_three

end
end Family8ProjectedTubeImageGraphStripSupportV1

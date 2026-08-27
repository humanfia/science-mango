import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairTraceV1
import FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1

open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Actual tubes normalized in the graph `c` coordinate

An arbitrary graph-coordinate quadruple `(a,b,c,d)` determines an honest
project `Tube`: take base point `(a,b,0)` and normalize the nonzero direction
vector `(c,d,1)`.  Normalizing the direction changes none of the four graph
ratios.  This gives a callback-free way to replace only the `c` coordinate
of an actual tube.

The reduced coefficient metric reads only `(a,b,d)`, so it is invariant under
this replacement.  The cinematic trace changes by exactly `(c' - c) * theta`;
on `|theta| <= 1`, every vertical-neighborhood containment therefore survives
after adding the `c`-gap to its radius.
-/

/-- The raw graph direction `(c,d,1)` is never zero. -/
theorem point3_graphDirection_ne_zero (c d : Real) :
    point3 c d 1 ≠ 0 := by
  intro h
  have hcoord := congrArg (fun p : Space => p (2 : Fin 3)) h
  change (1 : Real) = 0 at hcoord
  norm_num at hcoord

/-- Unit direction representing graph slopes `(c,d)`. -/
def graphCoordinateDirection (c d : Real) : Space :=
  NormedSpace.normalize (point3 c d 1)

@[simp] theorem norm_graphCoordinateDirection (c d : Real) :
    ‖graphCoordinateDirection c d‖ = 1 := by
  exact NormedSpace.norm_normalize (point3_graphDirection_ne_zero c d)

/-- An honest unit-segment tube having the prescribed graph coordinates. -/
def graphCoordinateTube
    (radius : NNReal) (a b c d : Real) : Tube radius where
  axis := {
    base := point3 a b 0
    direction := graphCoordinateDirection c d
    norm_direction := norm_graphCoordinateDirection c d }

@[simp] theorem graphCoordinateTube_axis_base
    (radius : NNReal) (a b c d : Real) :
    (graphCoordinateTube radius a b c d).axis.base = point3 a b 0 :=
  rfl

@[simp] theorem graphCoordinateTube_axis_direction
    (radius : NNReal) (a b c d : Real) :
    (graphCoordinateTube radius a b c d).axis.direction =
      graphCoordinateDirection c d :=
  rfl

@[simp] theorem graphCoordinateDirection_apply_zero (c d : Real) :
    graphCoordinateDirection c d (0 : Fin 3) =
      ‖point3 c d 1‖⁻¹ * c := by
  simp [graphCoordinateDirection, NormedSpace.normalize, point3]

@[simp] theorem graphCoordinateDirection_apply_one (c d : Real) :
    graphCoordinateDirection c d (1 : Fin 3) =
      ‖point3 c d 1‖⁻¹ * d := by
  simp [graphCoordinateDirection, NormedSpace.normalize, point3]

@[simp] theorem graphCoordinateDirection_apply_two (c d : Real) :
    graphCoordinateDirection c d (2 : Fin 3) =
      ‖point3 c d 1‖⁻¹ := by
  simp [graphCoordinateDirection, NormedSpace.normalize, point3]

/-- The constructed tube has nonzero vertical direction, as required by the
height-graph adapter. -/
theorem graphCoordinateTube_direction_two_ne_zero
    (radius : NNReal) (a b c d : Real) :
    (graphCoordinateTube radius a b c d).axis.direction (2 : Fin 3) ≠ 0 := by
  simp only [graphCoordinateTube_axis_direction,
    graphCoordinateDirection_apply_two]
  exact inv_ne_zero (norm_ne_zero_iff.mpr (point3_graphDirection_ne_zero c d))

@[simp] theorem tubeGraphC_graphCoordinateTube
    (radius : NNReal) (a b c d : Real) :
    tubeGraphC (graphCoordinateTube radius a b c d) = c := by
  rw [tubeGraphC]
  simp only [graphCoordinateTube_axis_direction,
    graphCoordinateDirection_apply_zero,
    graphCoordinateDirection_apply_two]
  field_simp [norm_ne_zero_iff.mpr (point3_graphDirection_ne_zero c d)]

@[simp] theorem tubeGraphD_graphCoordinateTube
    (radius : NNReal) (a b c d : Real) :
    tubeGraphD (graphCoordinateTube radius a b c d) = d := by
  rw [tubeGraphD]
  simp only [graphCoordinateTube_axis_direction,
    graphCoordinateDirection_apply_one,
    graphCoordinateDirection_apply_two]
  field_simp [norm_ne_zero_iff.mpr (point3_graphDirection_ne_zero c d)]

@[simp] theorem tubeGraphA_graphCoordinateTube
    (radius : NNReal) (a b c d : Real) :
    tubeGraphA (graphCoordinateTube radius a b c d) = a := by
  simp [tubeGraphA, point3]

@[simp] theorem tubeGraphB_graphCoordinateTube
    (radius : NNReal) (a b c d : Real) :
    tubeGraphB (graphCoordinateTube radius a b c d) = b := by
  simp [tubeGraphB, point3]

@[simp] theorem projectedTubeGraphC_graphCoordinateTube
    (radius : NNReal) (a b c d : Real) :
    projectedTubeGraphC (graphCoordinateTube radius a b c d) = c := by
  change tubeGraphC (graphCoordinateTube radius a b c d) = c
  exact tubeGraphC_graphCoordinateTube radius a b c d

@[simp] theorem projectedTubeGraphD_graphCoordinateTube
    (radius : NNReal) (a b c d : Real) :
    projectedTubeGraphD (graphCoordinateTube radius a b c d) = d := by
  change tubeGraphD (graphCoordinateTube radius a b c d) = d
  exact tubeGraphD_graphCoordinateTube radius a b c d

@[simp] theorem projectedTubeGraphA_graphCoordinateTube
    (radius : NNReal) (a b c d : Real) :
    projectedTubeGraphA (graphCoordinateTube radius a b c d) = a := by
  change tubeGraphA (graphCoordinateTube radius a b c d) = a
  exact tubeGraphA_graphCoordinateTube radius a b c d

@[simp] theorem projectedTubeGraphB_graphCoordinateTube
    (radius : NNReal) (a b c d : Real) :
    projectedTubeGraphB (graphCoordinateTube radius a b c d) = b := by
  change tubeGraphB (graphCoordinateTube radius a b c d) = b
  exact tubeGraphB_graphCoordinateTube radius a b c d

/-- Replace the graph `c` coordinate of `T`, preserving its graph
coordinates `(a,b,d)` exactly. -/
def normalizeTubeC {radius : NNReal} (T : Tube radius) (c : Real) :
    Tube radius :=
  graphCoordinateTube radius
    (tubeGraphA T) (tubeGraphB T) c (tubeGraphD T)

@[simp] theorem tubeGraphA_normalizeTubeC
    {radius : NNReal} (T : Tube radius) (c : Real) :
    tubeGraphA (normalizeTubeC T c) = tubeGraphA T := by
  simp [normalizeTubeC]

@[simp] theorem tubeGraphB_normalizeTubeC
    {radius : NNReal} (T : Tube radius) (c : Real) :
    tubeGraphB (normalizeTubeC T c) = tubeGraphB T := by
  simp [normalizeTubeC]

@[simp] theorem tubeGraphC_normalizeTubeC
    {radius : NNReal} (T : Tube radius) (c : Real) :
    tubeGraphC (normalizeTubeC T c) = c := by
  simp [normalizeTubeC]

@[simp] theorem tubeGraphD_normalizeTubeC
    {radius : NNReal} (T : Tube radius) (c : Real) :
    tubeGraphD (normalizeTubeC T c) = tubeGraphD T := by
  simp [normalizeTubeC]

@[simp] theorem projectedTubeGraphA_normalizeTubeC
    {radius : NNReal} (T : Tube radius) (c : Real) :
    projectedTubeGraphA (normalizeTubeC T c) = projectedTubeGraphA T := by
  change tubeGraphA (normalizeTubeC T c) = tubeGraphA T
  simp

@[simp] theorem projectedTubeGraphB_normalizeTubeC
    {radius : NNReal} (T : Tube radius) (c : Real) :
    projectedTubeGraphB (normalizeTubeC T c) = projectedTubeGraphB T := by
  change tubeGraphB (normalizeTubeC T c) = tubeGraphB T
  simp

@[simp] theorem projectedTubeGraphC_normalizeTubeC
    {radius : NNReal} (T : Tube radius) (c : Real) :
    projectedTubeGraphC (normalizeTubeC T c) = c := by
  change tubeGraphC (normalizeTubeC T c) = c
  simp

@[simp] theorem projectedTubeGraphD_normalizeTubeC
    {radius : NNReal} (T : Tube radius) (c : Real) :
    projectedTubeGraphD (normalizeTubeC T c) = projectedTubeGraphD T := by
  change tubeGraphD (normalizeTubeC T c) = tubeGraphD T
  simp

/-- Normalize `T` to the literal graph `c` coordinate of `U`. -/
def normalizeTubeCTo {radius : NNReal} (T U : Tube radius) : Tube radius :=
  normalizeTubeC T (tubeGraphC U)

@[simp] theorem tubeGraphC_normalizeTubeCTo
    {radius : NNReal} (T U : Tube radius) :
    tubeGraphC (normalizeTubeCTo T U) = tubeGraphC U := by
  simp [normalizeTubeCTo]

@[simp] theorem projectedTubeGraphC_normalizeTubeCTo
    {radius : NNReal} (T U : Tube radius) :
    projectedTubeGraphC (normalizeTubeCTo T U) = projectedTubeGraphC U := by
  change tubeGraphC (normalizeTubeCTo T U) = tubeGraphC U
  simp

/-- The ordinary reduced `(a,b,d)` coefficient distance is unchanged by
normalizing either `c` coordinate. -/
@[simp] theorem tubePairCoefficientDistance_normalizeTubeC_left
    {radius : NNReal} (T U : Tube radius) (c : Real) :
    tubePairCoefficientDistance (normalizeTubeC T c) U =
      tubePairCoefficientDistance T U := by
  simp [tubePairCoefficientDistance, tubePairDeltaA,
    tubePairDeltaB, tubePairDeltaD]

@[simp] theorem tubePairCoefficientDistance_normalizeTubeC_right
    {radius : NNReal} (T U : Tube radius) (c : Real) :
    tubePairCoefficientDistance T (normalizeTubeC U c) =
      tubePairCoefficientDistance T U := by
  simp [tubePairCoefficientDistance, tubePairDeltaA,
    tubePairDeltaB, tubePairDeltaD]

/-- The projected metric used by the actual `G'` construction is unchanged
by `c` normalization. -/
@[simp] theorem projectedTubePairCoefficientDistance_normalizeTubeC_left
    {radius : NNReal} (T U : Tube radius) (c : Real) :
    projectedTubePairCoefficientDistance (normalizeTubeC T c) U =
      projectedTubePairCoefficientDistance T U := by
  simp [projectedTubePairCoefficientDistance, projectedTubePairDeltaA,
    projectedTubePairDeltaB, projectedTubePairDeltaD]

@[simp] theorem projectedTubePairCoefficientDistance_normalizeTubeC_right
    {radius : NNReal} (T U : Tube radius) (c : Real) :
    projectedTubePairCoefficientDistance T (normalizeTubeC U c) =
      projectedTubePairCoefficientDistance T U := by
  simp [projectedTubePairCoefficientDistance, projectedTubePairDeltaA,
    projectedTubePairDeltaB, projectedTubePairDeltaD]

@[simp] theorem projectedTubePairCoefficientDistance_normalizeTubeC_both
    {radius : NNReal} (T U : Tube radius) (cT cU : Real) :
    projectedTubePairCoefficientDistance
        (normalizeTubeC T cT) (normalizeTubeC U cU) =
      projectedTubePairCoefficientDistance T U := by
  simp

/-- The scalar cinematic trace attached to an actual tube. -/
def actualTubeCinematicTrace {radius : NNReal}
    (f : Real -> Real) (T : Tube radius) (theta : Real) : Real :=
  cinematicTraceValue f
    (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta

/-- Replacing `c` changes the trace by the exact linear error
`(c' - c) * theta`. -/
theorem actualTubeCinematicTrace_normalizeTubeC_sub
    {radius : NNReal} (T : Tube radius) (c : Real)
    (f : Real -> Real) (theta : Real) :
    actualTubeCinematicTrace f (normalizeTubeC T c) theta -
        actualTubeCinematicTrace f T theta =
      (c - tubeGraphC T) * theta := by
  simp only [actualTubeCinematicTrace, tubeGraphA_normalizeTubeC,
    tubeGraphB_normalizeTubeC, tubeGraphC_normalizeTubeC,
    tubeGraphD_normalizeTubeC, cinematicTraceValue]
  ring

/-- On the height range `|theta| <= 1`, the trace displacement is bounded by
the absolute `c`-gap. -/
theorem abs_actualTubeCinematicTrace_normalizeTubeC_sub_le
    {radius : NNReal} (T : Tube radius) (c : Real)
    (f : Real -> Real) (theta : Real) (htheta : |theta| <= 1) :
    |actualTubeCinematicTrace f (normalizeTubeC T c) theta -
        actualTubeCinematicTrace f T theta| <=
      |c - tubeGraphC T| := by
  rw [actualTubeCinematicTrace_normalizeTubeC_sub, abs_mul]
  simpa using mul_le_mul_of_nonneg_left htheta (abs_nonneg (c - tubeGraphC T))

/-- A pointwise graph perturbation of size `error` enlarges a vertical
neighborhood radius by at most `error`. -/
theorem cinematicVerticalNeighborhood_subset_of_pointwise_abs_sub_le
    (g k : Real -> Real) (I : Set Real) (R error : Real)
    (hgap : forall theta, theta ∈ I -> |k theta - g theta| <= error) :
    cinematicVerticalNeighborhood g I R ⊆
      cinematicVerticalNeighborhood k I (R + error) := by
  rintro q ⟨hqI, hq⟩
  refine ⟨hqI, ?_⟩
  calc
    |q.1 - k q.2| = |(q.1 - g q.2) + (g q.2 - k q.2)| := by ring_nf
    _ <= |q.1 - g q.2| + |g q.2 - k q.2| := abs_add_le _ _
    _ <= R + error := by
      exact add_le_add hq (by simpa [abs_sub_comm] using hgap q.2 hqI)

/-- Direct neighborhood transfer for `c` normalization, paying the exact
absolute `c`-gap. -/
theorem actualTubeCinematicTrace_neighborhood_subset_normalizeTubeC
    {radius : NNReal} (T : Tube radius) (c : Real)
    (f : Real -> Real) (I : Set Real) (R : Real)
    (hunit : forall theta, theta ∈ I -> |theta| <= 1) :
    cinematicVerticalNeighborhood (actualTubeCinematicTrace f T) I R ⊆
      cinematicVerticalNeighborhood
        (actualTubeCinematicTrace f (normalizeTubeC T c)) I
        (R + |c - tubeGraphC T|) := by
  apply cinematicVerticalNeighborhood_subset_of_pointwise_abs_sub_le
  intro theta htheta
  exact abs_actualTubeCinematicTrace_normalizeTubeC_sub_le
    T c f theta (hunit theta htheta)

/-- If the `c`-gap is bounded by `error`, the same transfer pays only the
explicit cap `error`. -/
theorem actualTubeCinematicTrace_neighborhood_subset_normalizeTubeC_of_gap
    {radius : NNReal} (T : Tube radius) (c : Real)
    (f : Real -> Real) (I : Set Real) (R error : Real)
    (hunit : forall theta, theta ∈ I -> |theta| <= 1)
    (hgap : |c - tubeGraphC T| <= error) :
    cinematicVerticalNeighborhood (actualTubeCinematicTrace f T) I R ⊆
      cinematicVerticalNeighborhood
        (actualTubeCinematicTrace f (normalizeTubeC T c)) I (R + error) := by
  apply cinematicVerticalNeighborhood_subset_of_pointwise_abs_sub_le
  intro theta htheta
  exact (abs_actualTubeCinematicTrace_normalizeTubeC_sub_le
    T c f theta (hunit theta htheta)).trans hgap

/-- Normalize the left tube to the right tube's `c` coordinate.  A projected
`c`-bucket gap is accepted directly, so no exact-`C` provenance is required. -/
theorem actualTubeCinematicTrace_neighborhood_subset_normalizeTubeCTo_of_projected_gap
    {radius : NNReal} (T U : Tube radius)
    (f : Real -> Real) (I : Set Real) (R error : Real)
    (hunit : forall theta, theta ∈ I -> |theta| <= 1)
    (hgap : |projectedTubeGraphC T - projectedTubeGraphC U| <= error) :
    cinematicVerticalNeighborhood (actualTubeCinematicTrace f T) I R ⊆
      cinematicVerticalNeighborhood
        (actualTubeCinematicTrace f (normalizeTubeCTo T U)) I (R + error) := by
  apply actualTubeCinematicTrace_neighborhood_subset_normalizeTubeC_of_gap
  · exact hunit
  · change |tubeGraphC T - tubeGraphC U| <= error at hgap
    simpa [normalizeTubeCTo, abs_sub_comm] using hgap

/-- Any reference set already contained in the original tube neighborhood
remains contained after normalizing to the right tube's `c` coordinate. -/
theorem subset_actualTubeCinematicTrace_normalizeTubeCTo_neighborhood_of_projected_gap
    {radius : NNReal} (T U : Tube radius)
    (f : Real -> Real) (I : Set Real) (R error : Real)
    (S : Set (Real × Real))
    (hunit : forall theta, theta ∈ I -> |theta| <= 1)
    (hgap : |projectedTubeGraphC T - projectedTubeGraphC U| <= error)
    (hcontain : S ⊆
      cinematicVerticalNeighborhood (actualTubeCinematicTrace f T) I R) :
    S ⊆ cinematicVerticalNeighborhood
      (actualTubeCinematicTrace f (normalizeTubeCTo T U)) I (R + error) := by
  exact hcontain.trans
    (actualTubeCinematicTrace_neighborhood_subset_normalizeTubeCTo_of_projected_gap
      T U f I R error hunit hgap)

#print axioms point3_graphDirection_ne_zero
#print axioms tubeGraphA_graphCoordinateTube
#print axioms tubeGraphB_graphCoordinateTube
#print axioms tubeGraphC_graphCoordinateTube
#print axioms tubeGraphD_graphCoordinateTube
#print axioms projectedTubePairCoefficientDistance_normalizeTubeC_left
#print axioms actualTubeCinematicTrace_normalizeTubeC_sub
#print axioms abs_actualTubeCinematicTrace_normalizeTubeC_sub_le
#print axioms actualTubeCinematicTrace_neighborhood_subset_normalizeTubeCTo_of_projected_gap
#print axioms subset_actualTubeCinematicTrace_normalizeTubeCTo_neighborhood_of_projected_gap

end

end FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1

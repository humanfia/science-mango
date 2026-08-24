import FamilyStickyCinematicL32PyzActualUnitBallVerticalNormRetentionV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32PyzActualUnitBallVerticalNormRetentionV1

noncomputable section

/-!
# Literal selection of the fixed vertical direction chart

Wang--Zahl's line space is restricted, before the projected graph argument,
to one fixed chart whose final direction coordinate has absolute value at
least `1/2`.  We encode that selection as an actual finite filter.  Hence a
later ambient index family only needs to be known to lie in the selected
filter; the pointwise vertical inequality is then produced internally.

This module deliberately does not import the legacy upper-hemisphere DAG.
It also does not claim a cardinality-retention theorem for selecting a chart
from an arbitrary unoriented tube family: that earlier finite-cover step is
separate from the PYZ projected argument.
-/

/-- Literal orientation-invariant fixed vertical chart on source indices. -/
def fixedVerticalChartIndices
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota) :
    Finset iota :=
  source.filter fun i =>
    (1 / 2 : Real) ≤ |(fine.tubes i).axis.direction 2|

@[simp]
theorem mem_fixedVerticalChartIndices_iff
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    {i : iota} :
    i ∈ fixedVerticalChartIndices fine source ↔
      i ∈ source ∧
        (1 / 2 : Real) ≤ |(fine.tubes i).axis.direction 2| := by
  simp [fixedVerticalChartIndices]

theorem fixedVerticalChartIndices_subset_source
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota) :
    fixedVerticalChartIndices fine source ⊆ source := by
  intro i hi
  exact (mem_fixedVerticalChartIndices_iff fine source).mp hi |>.1

/-- Membership in the literal selected chart supplies the analytic vertical
denominator bound. -/
theorem vertical_half_of_mem_fixedVerticalChartIndices
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    {i : iota} (hi : i ∈ fixedVerticalChartIndices fine source) :
    (1 / 2 : Real) ≤ |(fine.tubes i).axis.direction 2| :=
  (mem_fixedVerticalChartIndices_iff fine source).mp hi |>.2

/-- Any ambient family selected inside the fixed chart inherits the vertical
bound on all its actual indices. -/
theorem ambient_vertical_half_of_subset_fixedVerticalChart
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source ambient : Finset iota)
    (hselected : ambient ⊆ fixedVerticalChartIndices fine source) :
    ∀ i, i ∈ ambient →
      (1 / 2 : Real) ≤ |(fine.tubes i).axis.direction 2| := by
  intro i hi
  exact vertical_half_of_mem_fixedVerticalChartIndices fine source
    (hselected hi)

/-- Norm critical retention with the vertical inequality transported from
the literal fixed-chart selection. -/
theorem ambientCriticalFamily_weighted_card_retention_of_fixedVerticalChart
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (source ambient active : Finset iota)
    (hselected : ambient ⊆ fixedVerticalChartIndices fine source)
    (hfamily : (actualProjectedAmbientCriticalFamily fine ambient active).Nonempty)
    (hunit : ∀ i, i ∈ ambient →
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) ≤ 16)
    (exponent : Real) (hexponent : 0 ≤ exponent)
    (testCenter : Tube radius)
    (htestCenter : testCenter ∈
      actualProjectedAmbientCriticalFamily fine ambient active) :
    let family := actualProjectedAmbientCriticalFamily fine ambient active
    (family.card : Real) * (16 : Real) ^ (-exponent) ≤
      ((finiteNormCriticalBall family projectedTubePairCoefficientDistance
        (radius : Real) 16 exponent hfamily).card : Real) *
      (finiteCriticalMaximizerScale family
        projectedTubePairCoefficientDistance (radius : Real) 16 exponent
        hfamily) ^ (-exponent) := by
  exact ambientCriticalFamily_weighted_card_retention_sixteen
    fine ambient active hfamily hunit
      (ambient_vertical_half_of_subset_fixedVerticalChart
        fine source ambient hselected)
      hradius hradiusSixteen exponent hexponent testCenter htestCenter

end
end FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

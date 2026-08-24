import FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
import FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1
import FamilyStickyCinematicL32ActualProjectedAttainedTangencyBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionIntervalsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionNestingV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedAttainedTangencyBridgeV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1

noncomputable section

universe u v

/-!
# The stored tangency stage on the correct middle interval

The physical projected carrier keeps its outer interval (and hence its
outer-sixteenth incidence).  Only the tangency metric is specialized here:
it is the actual attained minimum on the centered half of that outer
interval.  Since every value of a finite incidence pattern is computed from
one of finitely many active sets, the resulting scale, centre, `Y₁`, and
positive multiplicity cells remain measurable without a measurable-choice
premise.
-/

/-- Actual attained tangency metric on the centered half of the outer
parameter interval.  The active set is retained as an argument because the
finite critical-scale kernel is pattern-indexed. -/
noncomputable def actualProjectedCenteredHalfTangencyDistance
    {radius : NNReal} {iota : Type u}
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (_active : Finset iota) (T U : Tube radius) : Real :=
  tubePairAttainedTangencyDistance T U f f1 f2
    (centeredFractionLeft outerA outerB (1 / 2 : Real))
    (centeredFractionRight outerA outerB (1 / 2 : Real))
    (centered_half_and_quarter_endpoints_ordered hOuter).1
    (fun z _hz => hf z) (fun z _hz => hf1 z)

/-- The direct attained metric equals the compact-minimum scalar used by the
projected critical selector, now on exactly the centered half interval. -/
theorem actualProjectedCenteredHalfTangencyDistance_eq_projected
    {radius : NNReal} {iota : Type u}
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (active : Finset iota) (T U : Tube radius) :
    actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
        hOuter hf hf1 active T U =
      actualProjectedTangencyDistance f f1 f2
        (centeredFractionLeft outerA outerB (1 / 2 : Real))
        (centeredFractionRight outerA outerB (1 / 2 : Real))
        (centered_half_and_quarter_endpoints_ordered hOuter).1
        (fun z _hz => hf z) (fun z _hz => hf1 z) active T U := by
  dsimp only [actualProjectedCenteredHalfTangencyDistance,
    actualProjectedTangencyDistance]
  exact (projectedTubePairTangencyDistance_eq_attained T U f f1 f2
    (centeredFractionLeft outerA outerB (1 / 2 : Real))
    (centeredFractionRight outerA outerB (1 / 2 : Real))
    (centered_half_and_quarter_endpoints_ordered hOuter).1
    (fun z _hz => hf z) (fun z _hz => hf1 z)).symm

/-- The compact-minimum data for every value of the centered-half metric is
provided by the actual tube-pair minimizer theorem. -/
theorem actualProjectedCenteredHalfTangencyDistance_spec
    {radius : NNReal} {iota : Type u}
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (active : Finset iota) (T U : Tube radius) :
    ∃ thetaDelta,
      thetaDelta ∈ Icc
        (centeredFractionLeft outerA outerB (1 / 2 : Real))
        (centeredFractionRight outerA outerB (1 / 2 : Real)) ∧
      0 ≤ actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA
        outerB hOuter hf hf1 active T U ∧
      actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
          hOuter hf hf1 active T U =
        traceTangencyCost f f1 (tubePairDeltaA T U)
          (tubePairDeltaB T U) (tubePairDeltaD T U) thetaDelta ∧
      ∀ theta, theta ∈ Icc
          (centeredFractionLeft outerA outerB (1 / 2 : Real))
          (centeredFractionRight outerA outerB (1 / 2 : Real)) →
        actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
            hOuter hf hf1 active T U ≤
          traceTangencyCost f f1 (tubePairDeltaA T U)
            (tubePairDeltaB T U) (tubePairDeltaD T U) theta := by
  simpa only [actualProjectedCenteredHalfTangencyDistance] using
    tubePairAttainedTangencyDistance_spec T U f f1 f2
      (centeredFractionLeft outerA outerB (1 / 2 : Real))
      (centeredFractionRight outerA outerB (1 / 2 : Real))
      (centered_half_and_quarter_endpoints_ordered hOuter).1
      (fun z _hz => hf z) (fun z _hz => hf1 z)

/-- The direct centered-half attained metric vanishes on the diagonal. -/
theorem actualProjectedCenteredHalfTangencyDistance_self
    {radius : NNReal} {iota : Type u}
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (active : Finset iota) (T : Tube radius) :
    actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1 active T T = 0 := by
  obtain ⟨theta, _htheta, hnonneg, _hdef, hminimum⟩ :=
    actualProjectedCenteredHalfTangencyDistance_spec f f1 f2 outerA outerB
      hOuter hf hf1 active T T
  apply le_antisymm
  · have hleft := hminimum
      (centeredFractionLeft outerA outerB (1 / 2 : Real))
      ⟨le_rfl, (centered_half_and_quarter_endpoints_ordered hOuter).1⟩
    simpa [tubePairDeltaA, tubePairDeltaB, tubePairDeltaD,
      traceTangencyCost, traceFunction, traceFirstDerivative, traceJet0,
      traceJet1] using hleft
  · exact hnonneg

/-- Literal centered-half tangency scale on the norm-localized family. -/
noncomputable def actualProjectedCenteredHalfLocalizedTangencyScale
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) : point → Real :=
  finiteIncidenceLocalizedTangencyScale physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1)
    (radius : Real) ceiling exponent

/-- The stored centered-half tangency scale is measurable solely from the
literal finite physical carrier events. -/
theorem measurable_actualProjectedCenteredHalfLocalizedTangencyScale
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) :
    Measurable (actualProjectedCenteredHalfLocalizedTangencyScale fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent) := by
  exact measurable_finiteIncidenceLocalizedTangencyScale physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (fun i hi => physical.measurable_carrier i hi)
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1)
    (radius : Real) ceiling exponent

/-- Literal `Y₁` built with the attained centered-half metric while keeping
the original outer physical incidence family. -/
noncomputable def actualProjectedCenteredHalfTangencyY1
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) :
    FiniteProjectedShading point iota :=
  finiteIncidenceLocalizedTangencyY1 base hbase physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (fun i hi => physical.measurable_carrier i hi)
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1)
    fine.tubes (radius : Real) ceiling exponent threshold

/-- Total actual centre stored by the centered-half tangency stage. -/
noncomputable def actualProjectedCenteredHalfTangencyCenterTubeAt
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) : point → Tube radius :=
  fun x => (finiteIncidenceLocalizedTangencyCenter physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1)
    (radius : Real) ceiling exponent x).getD globalCenter

/-- Positive multiplicity cell of the literal centered-half `Y₁`. -/
def actualProjectedCenteredHalfTangencyE2
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (lower upper : Nat) : Set point :=
  (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent threshold).multiplicityBand lower upper

theorem measurableSet_actualProjectedCenteredHalfTangencyE2
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (lower upper : Nat) :
    MeasurableSet (actualProjectedCenteredHalfTangencyE2 base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent threshold lower upper) := by
  exact FiniteProjectedShading.measurableSet_multiplicityBand
    (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold) lower upper

#print axioms actualProjectedCenteredHalfTangencyDistance
#print axioms actualProjectedCenteredHalfTangencyDistance_eq_projected
#print axioms actualProjectedCenteredHalfTangencyDistance_spec
#print axioms actualProjectedCenteredHalfTangencyDistance_self
#print axioms actualProjectedCenteredHalfLocalizedTangencyScale
#print axioms measurable_actualProjectedCenteredHalfLocalizedTangencyScale
#print axioms actualProjectedCenteredHalfTangencyY1
#print axioms actualProjectedCenteredHalfTangencyCenterTubeAt
#print axioms actualProjectedCenteredHalfTangencyE2
#print axioms measurableSet_actualProjectedCenteredHalfTangencyE2

end

end FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1

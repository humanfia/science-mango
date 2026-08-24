import FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
import FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32ActualProjectedNormLocalizedTangencyE2SelectionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedTangencyY1E2V1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32JetSeparationV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Positive dyadic multiplicity cell after norm-first tangency localization

The label is the dyadic bucket of the literal active cardinality of `Y₁`.
Thus the continuum set remains measurable by finite incidence, and the loss
is the actual number of dyadic cardinality labels rather than the size of the
ambient tube family.
-/

/-- Literal real-valued active multiplicity of a finite projected shading. -/
def projectedActiveMultiplicity
    {point : Type u} [MeasurableSpace point] {index : Type v}
    (Z : FiniteProjectedShading point index) (x : point) : Real :=
  (Z.activeAtPoint x).card

theorem measurable_projectedActiveMultiplicity
    {point : Type u} [MeasurableSpace point] {index : Type v}
    (Z : FiniteProjectedShading point index) :
    Measurable (projectedActiveMultiplicity Z) := by
  exact Z.measurable_activeValue fun active => (active.card : Real)

/-- A concrete actual projected tube has zero tangency distance from itself.
This is proved directly from the compact minimizer, without importing the
legacy finite-good-pairs facade. -/
theorem projectedTubePairTangencyDistance_self
    {radius : NNReal} (T : Tube radius)
    (f f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, z ∈ Icc A B → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc A B → HasDerivAt f1 (f2 z) z) :
    projectedTubePairTangencyDistance T T f f1 f2 A B hAB
      hfDeriv hf1Deriv = 0 := by
  let hminimizer := exists_trace_tangencyParameter_with_minimizer
    f f1 f2
      (projectedTubePairDeltaA T T)
      (projectedTubePairDeltaB T T)
      (projectedTubePairDeltaD T T)
      hAB hfDeriv hf1Deriv
  have hspec := Classical.choose_spec hminimizer
  rcases hspec with ⟨theta, hnonneg, _htheta, _hdef, hminimum⟩
  apply le_antisymm
  · have hA := hminimum A ⟨le_rfl, hAB⟩
    simpa [projectedTubePairTangencyDistance, hminimizer,
      projectedTubePairDeltaA, projectedTubePairDeltaB,
      projectedTubePairDeltaD, traceTangencyCost, traceFunction,
      traceFirstDerivative, traceJet0, traceJet1] using hA
  · exact hnonneg

/-- The honest dyadic multiplicity cell inside the base of `Z`. -/
def projectedPositiveMultiplicityDyadicCell
    {point : Type u} [MeasurableSpace point] {index : Type v}
    (Z : FiniteProjectedShading point index) (label : Int) : Set point :=
  continuumCriticalSingleDyadicCell Z.base
    (projectedActiveMultiplicity Z) label

/-- A nonempty literal active family on every base point admits a positive
dyadic multiplicity cell with the exact finite-label average loss. -/
theorem exists_projectedPositiveMultiplicityDyadicCell
    {point : Type u} [MeasurableSpace point] {index : Type v}
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (hbaseNonempty : Z.base.Nonempty)
    (hactive : ∀ x, x ∈ Z.base → (Z.activeAtPoint x).Nonempty) :
    ∃ label ∈ Finset.Icc (dyadicCeilBucket 1)
        (dyadicCeilBucket (Z.ambient.card : Real)),
      mu Z.base /
          (continuumCriticalSingleDyadicBinFactor 1
            (Z.ambient.card : Real) : ENNReal) ≤
        mu (projectedPositiveMultiplicityDyadicCell Z label) ∧
      0 < dyadicCeilUpper label ∧
      MeasurableSet (projectedPositiveMultiplicityDyadicCell Z label) ∧
      projectedPositiveMultiplicityDyadicCell Z label ⊆ Z.base ∧
      ∀ x ∈ projectedPositiveMultiplicityDyadicCell Z label,
        dyadicCeilUpper label / 2 <
            projectedActiveMultiplicity Z x ∧
          projectedActiveMultiplicity Z x ≤ dyadicCeilUpper label := by
  obtain ⟨x0, hx0⟩ := hbaseNonempty
  have hambientCard : (1 : Real) ≤ Z.ambient.card := by
    have hcard : 1 ≤ (Z.activeAtPoint x0).card :=
      Finset.one_le_card.mpr (hactive x0 hx0)
    exact_mod_cast hcard.trans (Finset.card_le_card
      (finiteIncidenceActiveAtPoint_subset Z.ambient
        (fun i x => x ∈ Z.carrier i) x0))
  have hscaleBounds : ∀ x ∈ Z.base,
      (1 : Real) ≤ projectedActiveMultiplicity Z x ∧
        projectedActiveMultiplicity Z x ≤ Z.ambient.card := by
    intro x hx
    constructor
    · change (1 : Real) ≤ ((Z.activeAtPoint x).card : Real)
      exact_mod_cast Finset.one_le_card.mpr (hactive x hx)
    · change ((Z.activeAtPoint x).card : Real) ≤ (Z.ambient.card : Real)
      exact_mod_cast Finset.card_le_card
        (finiteIncidenceActiveAtPoint_subset Z.ambient
          (fun i x => x ∈ Z.carrier i) x)
  obtain ⟨label, hlabel, hmeasure, hlabelPos, hbin⟩ :=
    exists_continuumCritical_single_dyadic_selection mu
      (projectedActiveMultiplicity Z) Z.measurable_base (by norm_num)
      hambientCard (measurable_projectedActiveMultiplicity Z) hscaleBounds
  refine ⟨label, hlabel, ?_, hlabelPos, ?_, ?_, hbin⟩
  · simpa [projectedPositiveMultiplicityDyadicCell] using hmeasure
  · exact measurableSet_continuumCriticalSingleDyadicCell
      Z.measurable_base (measurable_projectedActiveMultiplicity Z) label
  · intro x hx
    exact hx.1

#print axioms projectedActiveMultiplicity
#print axioms measurable_projectedActiveMultiplicity
#print axioms projectedTubePairTangencyDistance_self
#print axioms projectedPositiveMultiplicityDyadicCell
#print axioms exists_projectedPositiveMultiplicityDyadicCell

end

end FamilyStickyCinematicL32ActualProjectedNormLocalizedTangencyE2SelectionV1

import FamilyStickyCinematicL32PyzActualPositiveCenterTwoStageSelectionCanonicalV1
import FamilyStickyCinematicL32PyzActualAllCenterRichPayloadDirectDichotomyV1

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualPositiveCenterTwoStageSelectionCanonicalV1
open FamilyStickyCinematicL32PyzActualAllCenterRichPayloadDirectDichotomyV1

noncomputable section

universe u v

/-!
# Canonical rich payload on actual members of the centre set

The payload contains the literal two-stage selection certificate.  The
all-centre theorem indexes by `centers.attach`, so it never fabricates a
measurability proof or a positive-mass witness outside the selected finite
centre family.
-/

def positiveCenterTangencyScale
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real) : point → Real :=
  actualProjectedCenteredHalfLocalizedTangencyScale fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
    (36 * globalScale) tangencyExponent

def positiveCenterTangencyCell
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real) (tangencyLabel : Int) : Set point :=
  continuumCriticalSingleDyadicCell base
    (positiveCenterTangencyScale fine physical f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter tangencyExponent)
    tangencyLabel

def positiveCenterY1
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
    (tangencyExponent : Real) (tangencyLabel : Int) :
    FiniteProjectedShading point iota :=
  let tangencyScale := positiveCenterTangencyScale fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
    tangencyExponent
  let E_t := continuumCriticalSingleDyadicCell base tangencyScale
    tangencyLabel
  let hEtMeasurable := measurableSet_continuumCriticalSingleDyadicCell hbase
    (measurable_actualProjectedCenteredHalfLocalizedTangencyScale fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      (36 * globalScale) tangencyExponent) tangencyLabel
  actualProjectedCenteredHalfTangencyY1 E_t hEtMeasurable fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
    (36 * globalScale) tangencyExponent (dyadicCeilUpper tangencyLabel)

def positiveCenterE2
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
    (tangencyExponent : Real) (tangencyLabel finalLabel : Int) : Set point :=
  projectedPositiveMultiplicityDyadicCell
    (positiveCenterY1 base hbase fine physical f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter tangencyExponent tangencyLabel)
    finalLabel

structure ActualPositiveCenterCanonicalPayload
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real) where
  tangencyLabel : Int
  tangencyLabel_mem : tangencyLabel ∈
    Finset.Icc (dyadicCeilBucket (radius : Real))
      (dyadicCeilBucket (36 * globalScale))
  finalLabel : Int
  q : point
  certificate :
    let E_t := positiveCenterTangencyCell base fine physical f f1 f2
      outerA outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      tangencyLabel
    let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      tangencyLabel
    let E2 := positiveCenterE2 base hbase fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      tangencyLabel finalLabel
    finalLabel ∈ Finset.Icc (dyadicCeilBucket 1)
        (dyadicCeilBucket (Y1.ambient.card : Real)) ∧
      q ∈ E2 ∧
      mu base ≤ actualAllCenterPostNormBinLoss radius globalScale
          physical.ambient.card * mu E2 ∧
      0 < mu E_t ∧ E_t ⊆ base ∧
      (∀ x, x ∈ E_t →
        dyadicCeilUpper tangencyLabel / 2 <
            positiveCenterTangencyScale fine physical f f1 f2 outerA outerB
              hOuter hf hf1 globalScale globalCenter tangencyExponent x ∧
          positiveCenterTangencyScale fine physical f f1 f2 outerA outerB
              hOuter hf hf1 globalScale globalCenter tangencyExponent x ≤
            dyadicCeilUpper tangencyLabel) ∧
      0 < mu E2 ∧ MeasurableSet E2 ∧ E2 ⊆ E_t ∧
      (∀ x, x ∈ E2 → (Y1.activeAtPoint x).Nonempty)

theorem exists_actualPositiveCenterCanonicalPayload
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (hbasePos : 0 < mu base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (hradius : 0 < radius)
    (hradiusTangency : (radius : Real) ≤ 36 * globalScale)
    (hlocalized : ∀ x, x ∈ base →
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint x)).Nonempty) :
    Nonempty (ActualPositiveCenterCanonicalPayload mu base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent) := by
  obtain ⟨tangencyLabel, htangencyLabel, finalLabel, hfinalLabel, q, hq,
      hmeasure, hEtPos, hEtSubset, htangencyBin, hE2Pos, hE2Measurable,
      hE2Subset, hactive⟩ :=
    exists_actualPositiveCenter_twoStageSelection mu base hbase hbasePos fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent hradius hradiusTangency hlocalized
  refine ⟨{
    tangencyLabel := tangencyLabel
    tangencyLabel_mem := htangencyLabel
    finalLabel := finalLabel
    q := q
    certificate := ?_ }⟩
  dsimp only [positiveCenterTangencyCell, positiveCenterTangencyScale,
    positiveCenterY1, positiveCenterE2]
  exact ⟨hfinalLabel, hq, hmeasure, hEtPos, hEtSubset, htangencyBin,
    hE2Pos, hE2Measurable, hE2Subset, hactive⟩

theorem actualAllCenter_canonicalPayload_high_or_all_low
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real)
    (centers : Finset (Tube radius)) (cell : Tube radius → Set point)
    (tangencyExponent : Real) (logCount : Nat)
    (hradius : 0 < radius)
    (hradiusTangency : (radius : Real) ≤ 36 * globalScale)
    (hcellMeasurable : ∀ center, center ∈ centers →
      MeasurableSet (cell center))
    (hlocalized : ∀ center, center ∈ centers → ∀ x, x ∈ cell center →
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale center
        (physical.activeAtPoint x)).Nonempty) :
    (∃ center, ∃ hcenter : center ∈ centers,
      0 < mu (cell center) ∧
      ∃ payload : ActualPositiveCenterCanonicalPayload mu (cell center)
          (hcellMeasurable center hcenter) fine physical f f1 f2 outerA outerB
          hOuter hf hf1 globalScale center tangencyExponent,
        24 * logCount ≤ pyzE2DegreeLower payload.finalLabel) ∨
    (∀ center, ∀ hcenter : center ∈ centers, 0 < mu (cell center) →
      ∃ payload : ActualPositiveCenterCanonicalPayload mu (cell center)
          (hcellMeasurable center hcenter) fine physical f f1 f2 outerA outerB
          hOuter hf hf1 globalScale center tangencyExponent,
        pyzE2DegreeLower payload.finalLabel < 24 * logCount) := by
  classical
  let Center := {center : Tube radius // center ∈ centers}
  let Payload : Center → Type _ := fun center ↦
    ActualPositiveCenterCanonicalPayload mu (cell center.1)
      (hcellMeasurable center.1 center.2) fine physical f f1 f2 outerA outerB
      hOuter hf hf1 globalScale center.1 tangencyExponent
  have hpayload : ∀ center : Center, center ∈ centers.attach →
      0 < mu (cell center.1) → Nonempty (Payload center) := by
    intro center _hcenter hpositive
    exact exists_actualPositiveCenterCanonicalPayload mu (cell center.1)
      (hcellMeasurable center.1 center.2) hpositive fine physical f f1 f2
      outerA outerB hOuter hf hf1 globalScale center.1 tangencyExponent
      hradius hradiusTangency (hlocalized center.1 center.2)
  have hdichotomy := actualAllCenter_richPayload_high_or_all_low centers.attach
    (fun center : Center ↦ 0 < mu (cell center.1)) Payload
    (fun _center payload ↦ payload.finalLabel) logCount hpayload
  rcases hdichotomy with hhigh | hlow
  · rcases hhigh with ⟨center, _hcenter, hpositive, payload, hdegree⟩
    exact Or.inl ⟨center.1, center.2, hpositive, payload, hdegree⟩
  · refine Or.inr ?_
    intro center hcenter hpositive
    let attachedCenter : Center := ⟨center, hcenter⟩
    obtain ⟨payload, hdegree⟩ := hlow attachedCenter (by simp)
      hpositive
    exact ⟨payload, hdegree⟩

#print axioms exists_actualPositiveCenterCanonicalPayload
#print axioms actualAllCenter_canonicalPayload_high_or_all_low

end

end FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5

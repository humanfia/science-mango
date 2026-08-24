import FamilyStickyCinematicL32PyzActualPositiveCenterTangencySelectionV1
import FamilyStickyCinematicL32PyzActualPositiveCenterFinalSelectionV1
import FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualPositiveCenterTwoStageSelectionCanonicalV1

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
open FamilyStickyCinematicL32PyzActualPositiveCenterTangencySelectionV1
open FamilyStickyCinematicL32PyzActualPositiveCenterFinalSelectionV1

noncomputable section

/-!
# Canonical rich payload for one positive norm-cover cell

The measurability proof used to define `Y₁` is fixed canonically from the
literal cell and scale, rather than existentially quantified.  This makes the
payload stable under proof irrelevance when it is chosen simultaneously over
a finite family of centres.
-/

universe u v

theorem exists_actualPositiveCenter_twoStageSelection
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
    let tangencyScale :=
      actualProjectedCenteredHalfLocalizedTangencyScale fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent
    ∃ tangencyLabel ∈
        Finset.Icc (dyadicCeilBucket (radius : Real))
          (dyadicCeilBucket (36 * globalScale)),
      let tangencyThreshold := dyadicCeilUpper tangencyLabel
      let E_t := continuumCriticalSingleDyadicCell base tangencyScale
        tangencyLabel
      let hEtMeasurable := measurableSet_continuumCriticalSingleDyadicCell
        hbase
        (measurable_actualProjectedCenteredHalfLocalizedTangencyScale fine
          physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
          globalCenter (36 * globalScale) tangencyExponent)
        tangencyLabel
      let Y1 := actualProjectedCenteredHalfTangencyY1 E_t hEtMeasurable
        fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter (36 * globalScale) tangencyExponent tangencyThreshold
      ∃ finalLabel ∈ Finset.Icc (dyadicCeilBucket 1)
          (dyadicCeilBucket (Y1.ambient.card : Real)),
        let E2 := projectedPositiveMultiplicityDyadicCell Y1 finalLabel
        ∃ q ∈ E2,
          mu base ≤ actualAllCenterPostNormBinLoss radius globalScale
              physical.ambient.card * mu E2 ∧
            0 < mu E_t ∧ E_t ⊆ base ∧
            (∀ x, x ∈ E_t →
              tangencyThreshold / 2 < tangencyScale x ∧
                tangencyScale x ≤ tangencyThreshold) ∧
            0 < mu E2 ∧ MeasurableSet E2 ∧ E2 ⊆ E_t ∧
            (∀ x, x ∈ E2 → (Y1.activeAtPoint x).Nonempty) := by
  dsimp only
  let tangencyScale :=
    actualProjectedCenteredHalfLocalizedTangencyScale fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      (36 * globalScale) tangencyExponent
  obtain ⟨tangencyLabel, htangencyLabel, _hEtMeasurableOld, hEtPos,
      htangencyMul, hEtSubset, htangencyBin, hlocalizedEt⟩ :=
    exists_actualPositiveCenter_tangencySelection mu base hbase hbasePos fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent hradius hradiusTangency hlocalized
  let threshold := dyadicCeilUpper tangencyLabel
  let E_t := continuumCriticalSingleDyadicCell base tangencyScale
    tangencyLabel
  let hEtMeasurable := measurableSet_continuumCriticalSingleDyadicCell hbase
    (measurable_actualProjectedCenteredHalfLocalizedTangencyScale fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      (36 * globalScale) tangencyExponent) tangencyLabel
  obtain ⟨finalLabel, hfinalLabel, q, hq, hfinalMul, hE2Pos,
      hE2Measurable, hE2Subset, hactive⟩ :=
    exists_actualPositiveCenter_finalSelection mu E_t hEtMeasurable hEtPos
      fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter (36 * globalScale) tangencyExponent threshold
      (by
        unfold threshold dyadicCeilUpper
        exact (Real.rpow_pos_of_pos (by norm_num) _).le)
      hlocalizedEt
  let Y1 := actualProjectedCenteredHalfTangencyY1 E_t hEtMeasurable fine
    physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
    (36 * globalScale) tangencyExponent threshold
  let E2 := projectedPositiveMultiplicityDyadicCell Y1 finalLabel
  have hcombined : mu base ≤
      actualAllCenterPostNormBinLoss radius globalScale
        physical.ambient.card * mu E2 := by
    calc
      mu base ≤
          (continuumCriticalSingleDyadicBinFactor (radius : Real)
            (36 * globalScale) : ENNReal) * mu E_t := htangencyMul
      _ ≤ (continuumCriticalSingleDyadicBinFactor (radius : Real)
            (36 * globalScale) : ENNReal) *
          ((continuumCriticalSingleDyadicBinFactor 1
            (physical.ambient.card : Real) : ENNReal) * mu E2) :=
        mul_le_mul_right hfinalMul _
      _ = actualAllCenterPostNormBinLoss radius globalScale
          physical.ambient.card * mu E2 := by
        unfold actualAllCenterPostNormBinLoss
        ac_rfl
  refine ⟨tangencyLabel, htangencyLabel, finalLabel, hfinalLabel, q, hq,
    hcombined, hEtPos, hEtSubset, ?_, hE2Pos, hE2Measurable, hE2Subset,
    hactive⟩
  intro x hx
  simpa only [threshold, E_t] using htangencyBin x hx

#print axioms exists_actualPositiveCenter_twoStageSelection

end

end FamilyStickyCinematicL32PyzActualPositiveCenterTwoStageSelectionCanonicalV1

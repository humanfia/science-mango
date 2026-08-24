import FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
import FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
import FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1

noncomputable section

/-!
# Tangency critical selection after the global norm cover

The family supplied to the tangency maximizer is now literally the
pointwise norm family restricted to the already selected global `3B`.  This
restores the order in PYZ Section 5.1: norm maximizer, global norm cover,
then tangency maximizer and `Y₁`.  All scale and centre labels remain
functions of the same finite incidence pattern.
-/

universe u v w

variable {X : Type u} {index : Type v} {alpha : Type w}
  [MeasurableSpace X]

/-- Pointwise family `F_B(x)` after fixing the global norm cover centre. -/
def finiteIncidenceNormLocalizedFamilyValue
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (active : Finset index) : Finset alpha :=
  finiteGlobalNormLocalizedFamily (familyOfActive active) normDistance
    globalScale globalCenter

/-- Tangency critical scale on the norm-localized family. -/
noncomputable def finiteIncidenceLocalizedTangencyScale
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) : X → Real :=
  finiteIncidenceCriticalScale ambient incidence
    (finiteIncidenceNormLocalizedFamilyValue familyOfActive normDistance
      globalScale globalCenter)
    tangencyDistance delta ceiling exponent

/-- The localized tangency scale is measurable from the original finite
incidence events. -/
theorem measurable_finiteIncidenceLocalizedTangencyScale
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) :
    Measurable (finiteIncidenceLocalizedTangencyScale ambient incidence
      familyOfActive normDistance globalScale globalCenter tangencyDistance
      delta ceiling exponent) := by
  exact measurable_finiteIncidenceCriticalScale ambient incidence hincidence
    (finiteIncidenceNormLocalizedFamilyValue familyOfActive normDistance
      globalScale globalCenter)
    tangencyDistance delta ceiling exponent

set_option linter.unusedSectionVars false in
/-- On a source set where `F_B(x)` is nonempty, the localized tangency scale
has the automatic compact-interval bounds. -/
theorem finiteIncidenceLocalizedTangencyScale_bounds
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    {delta ceiling exponent : Real} (hdeltaCeiling : delta ≤ ceiling)
    {x : X}
    (hfamily : (finiteIncidenceNormLocalizedFamilyValue familyOfActive
      normDistance globalScale globalCenter
      (finiteIncidenceActiveAtPoint ambient incidence x)).Nonempty) :
    delta ≤ finiteIncidenceLocalizedTangencyScale ambient incidence
        familyOfActive normDistance globalScale globalCenter tangencyDistance
        delta ceiling exponent x ∧
      finiteIncidenceLocalizedTangencyScale ambient incidence familyOfActive
          normDistance globalScale globalCenter tangencyDistance delta ceiling
          exponent x ≤ ceiling := by
  simpa only [finiteIncidenceLocalizedTangencyScale,
    finiteIncidenceCriticalScale, finiteIncidenceCriticalScaleValue,
    dif_pos hfamily] using
    (finiteCriticalMaximizerScale_bounds
      (finiteIncidenceNormLocalizedFamilyValue familyOfActive normDistance
        globalScale globalCenter
        (finiteIncidenceActiveAtPoint ambient incidence x))
      (tangencyDistance
        (finiteIncidenceActiveAtPoint ambient incidence x))
      hfamily hdeltaCeiling)

/-- Canonical tangency centre selected only after norm localization. -/
noncomputable def finiteIncidenceLocalizedTangencyCenter
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) : X → Option alpha :=
  finiteIncidenceCriticalCenter ambient incidence
    (finiteIncidenceNormLocalizedFamilyValue familyOfActive normDistance
      globalScale globalCenter)
    tangencyDistance delta ceiling exponent

/-- Literal `Y₁` acceptance for one source index. -/
def finiteIncidenceLocalizedTangencyCarrierAccept
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (elementOfIndex : index → alpha) (threshold : Real) (i : index)
    (active : Finset index) (selected : Option alpha) : Prop :=
  i ∈ active ∧
    elementOfIndex i ∈ finiteIncidenceNormLocalizedFamilyValue
      familyOfActive normDistance globalScale globalCenter active ∧
    match selected with
    | none => False
    | some center =>
        tangencyDistance active (elementOfIndex i) center ≤ threshold

/-- Literal measurable `Y₁` carrier after norm localization. -/
def finiteIncidenceLocalizedTangencyCarrier
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (elementOfIndex : index → alpha)
    (delta ceiling exponent threshold : Real) (i : index) : Set X :=
  {x | finiteIncidenceLocalizedTangencyCarrierAccept familyOfActive
    normDistance globalScale globalCenter tangencyDistance elementOfIndex
    threshold i (finiteIncidenceActiveAtPoint ambient incidence x)
    (finiteIncidenceLocalizedTangencyCenter ambient incidence familyOfActive
      normDistance globalScale globalCenter tangencyDistance delta ceiling
      exponent x)}

/-- The post-cover `Y₁` carrier is measurable with no selector callback. -/
theorem measurableSet_finiteIncidenceLocalizedTangencyCarrier
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (elementOfIndex : index → alpha)
    (delta ceiling exponent threshold : Real) (i : index) :
    MeasurableSet (finiteIncidenceLocalizedTangencyCarrier ambient incidence
      familyOfActive normDistance globalScale globalCenter tangencyDistance
      elementOfIndex delta ceiling exponent threshold i) := by
  simpa only [finiteIncidenceLocalizedTangencyCarrier,
    finiteIncidenceLocalizedTangencyCenter,
    finiteIncidenceCriticalCenter] using
    (measurableSet_finiteIncidenceCriticalCenterPredicate ambient incidence
      hincidence
      (finiteIncidenceNormLocalizedFamilyValue familyOfActive normDistance
        globalScale globalCenter)
      tangencyDistance delta ceiling exponent
      (finiteIncidenceLocalizedTangencyCarrierAccept familyOfActive
        normDistance globalScale globalCenter tangencyDistance elementOfIndex
        threshold i))

/-- Continuum tangency-scale selection on the already fixed norm-cover cell. -/
theorem exists_finiteIncidenceLocalizedTangency_singleDyadicSelection
    (mu : Measure X) (E_B : Set X) (hE_B : MeasurableSet E_B)
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    {delta ceiling exponent : Real}
    (hdelta : 0 < delta) (hdeltaCeiling : delta ≤ ceiling)
    (hfamily : ∀ x ∈ E_B,
      (finiteIncidenceNormLocalizedFamilyValue familyOfActive normDistance
        globalScale globalCenter
        (finiteIncidenceActiveAtPoint ambient incidence x)).Nonempty) :
    let scale := finiteIncidenceLocalizedTangencyScale ambient incidence
      familyOfActive normDistance globalScale globalCenter tangencyDistance
      delta ceiling exponent
    ∃ label ∈ Finset.Icc (FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1.dyadicCeilBucket delta)
        (FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1.dyadicCeilBucket ceiling),
      mu E_B /
          (continuumCriticalSingleDyadicBinFactor delta ceiling : ENNReal) ≤
        mu (continuumCriticalSingleDyadicCell E_B scale label) ∧
      0 < FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1.dyadicCeilUpper label ∧
      ∀ x ∈ continuumCriticalSingleDyadicCell E_B scale label,
        FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1.dyadicCeilUpper label /
            2 < scale x ∧
        scale x ≤
          FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1.dyadicCeilUpper label := by
  dsimp only
  exact exists_continuumCritical_single_dyadic_selection mu
    (finiteIncidenceLocalizedTangencyScale ambient incidence familyOfActive
      normDistance globalScale globalCenter tangencyDistance delta ceiling
      exponent)
    hE_B hdelta hdeltaCeiling
    (measurable_finiteIncidenceLocalizedTangencyScale ambient incidence
      hincidence familyOfActive normDistance globalScale globalCenter
      tangencyDistance delta ceiling exponent)
    (fun x hx => finiteIncidenceLocalizedTangencyScale_bounds ambient incidence
      familyOfActive normDistance globalScale globalCenter tangencyDistance
      hdeltaCeiling (hfamily x hx))

#print axioms finiteIncidenceNormLocalizedFamilyValue
#print axioms finiteIncidenceLocalizedTangencyScale
#print axioms measurable_finiteIncidenceLocalizedTangencyScale
#print axioms finiteIncidenceLocalizedTangencyScale_bounds
#print axioms finiteIncidenceLocalizedTangencyCenter
#print axioms finiteIncidenceLocalizedTangencyCarrier
#print axioms measurableSet_finiteIncidenceLocalizedTangencyCarrier
#print axioms exists_finiteIncidenceLocalizedTangency_singleDyadicSelection

end

end FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1

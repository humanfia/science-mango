import FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
import FamilyStickyCinematicL32ContinuumCriticalDoubleDyadicSelectionV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32ContinuumActualCriticalDoubleDyadicSelectionV1

open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32ContinuumCriticalDoubleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# Actual critical maximizers fed into continuum double-dyadic selection

All interval bounds below are generated from membership in the actual finite
critical carrier.  Relative to the existing pointwise finite geometry, the
new analytic inputs are exactly measurability of `E` and measurability of the
two total actual critical-scale maps.
-/

universe u v

variable {X : Type u} {alpha : Type v} [MeasurableSpace X]

theorem exists_actualCritical_continuum_double_dyadic_selection
    (μ : Measure X) (E : Set X)
    (family : X → Finset alpha)
    (normDistance tangencyDistance : X → alpha → alpha → Real)
    (delta normCeiling tangencyCeiling normExponent tangencyExponent : Real)
    (hE : MeasurableSet E) (hdelta : 0 < delta)
    (hnormCeiling : delta ≤ normCeiling)
    (htangencyCeiling : delta ≤ tangencyCeiling)
    (hfamily : ∀ x ∈ E, (family x).Nonempty)
    (hnormMeasurable : Measurable
      (actualCriticalScaleOn E family normDistance
        delta normCeiling normExponent hfamily))
    (htangencyMeasurable : Measurable
      (actualCriticalScaleOn E family tangencyDistance
        delta tangencyCeiling tangencyExponent hfamily)) :
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket delta)
        (dyadicCeilBucket normCeiling),
      ∃ tangencyLabel ∈ Finset.Icc (dyadicCeilBucket delta)
          (dyadicCeilBucket tangencyCeiling),
        μ E / (continuumCriticalDoubleDyadicBinFactor delta normCeiling
            tangencyCeiling : ENNReal) ≤
          μ (continuumCriticalDoubleDyadicCell E
            (actualCriticalScaleOn E family normDistance
              delta normCeiling normExponent hfamily)
            (actualCriticalScaleOn E family tangencyDistance
              delta tangencyCeiling tangencyExponent hfamily)
            normLabel tangencyLabel) ∧
        0 < dyadicCeilUpper normLabel ∧
        0 < dyadicCeilUpper tangencyLabel ∧
        ∀ x ∈ continuumCriticalDoubleDyadicCell E
            (actualCriticalScaleOn E family normDistance
              delta normCeiling normExponent hfamily)
            (actualCriticalScaleOn E family tangencyDistance
              delta tangencyCeiling tangencyExponent hfamily)
            normLabel tangencyLabel,
          dyadicCeilUpper normLabel / 2 <
              actualCriticalScaleOn E family normDistance
                delta normCeiling normExponent hfamily x ∧
          actualCriticalScaleOn E family normDistance
              delta normCeiling normExponent hfamily x ≤
            dyadicCeilUpper normLabel ∧
          dyadicCeilUpper tangencyLabel / 2 <
              actualCriticalScaleOn E family tangencyDistance
                delta tangencyCeiling tangencyExponent hfamily x ∧
          actualCriticalScaleOn E family tangencyDistance
              delta tangencyCeiling tangencyExponent hfamily x ≤
            dyadicCeilUpper tangencyLabel := by
  apply exists_continuumCritical_double_dyadic_selection μ
    (actualCriticalScaleOn E family normDistance
      delta normCeiling normExponent hfamily)
    (actualCriticalScaleOn E family tangencyDistance
      delta tangencyCeiling tangencyExponent hfamily)
    hE hdelta hnormCeiling htangencyCeiling
    hnormMeasurable htangencyMeasurable
  · intro x hx
    exact actualCriticalScaleOn_bounds E family normDistance hfamily
      hnormCeiling hx
  · intro x hx
    exact actualCriticalScaleOn_bounds E family tangencyDistance hfamily
      htangencyCeiling hx

#print axioms exists_actualCritical_continuum_double_dyadic_selection

end

end FamilyStickyCinematicL32ContinuumActualCriticalDoubleDyadicSelectionV1

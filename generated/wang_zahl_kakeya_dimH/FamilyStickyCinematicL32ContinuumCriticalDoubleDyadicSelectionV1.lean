import FamilyStickyCinematicL32ContinuumDoubleMeasurableBucketV1
import FamilyStickyCinematicL32ContinuumDyadicCeilBucketMeasurableV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32ContinuumCriticalDoubleDyadicSelectionV1

open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32ContinuumDoubleMeasurableBucketV1
open FamilyStickyCinematicL32ContinuumDyadicCeilBucketMeasurableV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# Continuum double-dyadic critical-scale selection

This is the faithful measure-theoretic bridge from a measurable continuum set
to one finite pair of dyadic scale labels.  It never replaces the continuum
set by an arbitrary finite point selector.  The source-specific obligations
are precisely measurability and the paper scale bounds for the two real-valued
critical-scale maps.
-/

universe u

variable {X : Type u} [MeasurableSpace X]

/-- Exact number of possible pairs of ceil-log dyadic labels. -/
def continuumCriticalDoubleDyadicBinFactor
    (delta normCeiling tangencyCeiling : Real) : Nat :=
  (dyadicCeilBucket normCeiling + 1 - dyadicCeilBucket delta).toNat *
    (dyadicCeilBucket tangencyCeiling + 1 -
      dyadicCeilBucket delta).toNat

/-- The literal continuum cell on which both dyadic labels are fixed. -/
def continuumCriticalDoubleDyadicCell
    (E : Set X) (normScale tangencyScale : X → Real)
    (normLabel tangencyLabel : Int) : Set X :=
  measurableDoubleLabelCell E
    (fun x => dyadicCeilBucket (normScale x))
    (fun x => dyadicCeilBucket (tangencyScale x))
    normLabel tangencyLabel

theorem measurableSet_continuumCriticalDoubleDyadicCell
    {E : Set X} {normScale tangencyScale : X → Real}
    (hE : MeasurableSet E) (hnorm : Measurable normScale)
    (htangency : Measurable tangencyScale)
    (normLabel tangencyLabel : Int) :
    MeasurableSet (continuumCriticalDoubleDyadicCell E normScale
      tangencyScale normLabel tangencyLabel) := by
  exact measurableSet_measurableDoubleLabelCell hE
    (measurable_dyadicCeilBucket.comp hnorm)
    (measurable_dyadicCeilBucket.comp htangency)
    normLabel tangencyLabel

/-- Simultaneous measurable dyadic selection with the exact product loss and
the half-open-bin conclusions needed by the later Lemma 5.7/5.8 interfaces.

The theorem deliberately takes real-valued critical scale maps, not arbitrary
finite labels.  Thus a later source adapter must prove that the actual norm and
tangency critical-scale maps are measurable. -/
theorem exists_continuumCritical_double_dyadic_selection
    (μ : Measure X) {E : Set X}
    (normScale tangencyScale : X → Real)
    {delta normCeiling tangencyCeiling : Real}
    (hE : MeasurableSet E) (hdelta : 0 < delta)
    (hnormCeiling : delta ≤ normCeiling)
    (htangencyCeiling : delta ≤ tangencyCeiling)
    (hnormMeasurable : Measurable normScale)
    (htangencyMeasurable : Measurable tangencyScale)
    (hnormBounds : ∀ x ∈ E,
      delta ≤ normScale x ∧ normScale x ≤ normCeiling)
    (htangencyBounds : ∀ x ∈ E,
      delta ≤ tangencyScale x ∧ tangencyScale x ≤ tangencyCeiling) :
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket delta)
        (dyadicCeilBucket normCeiling),
      ∃ tangencyLabel ∈ Finset.Icc (dyadicCeilBucket delta)
          (dyadicCeilBucket tangencyCeiling),
        μ E / (continuumCriticalDoubleDyadicBinFactor delta normCeiling
            tangencyCeiling : ENNReal) ≤
          μ (continuumCriticalDoubleDyadicCell E normScale tangencyScale
            normLabel tangencyLabel) ∧
        0 < dyadicCeilUpper normLabel ∧
        0 < dyadicCeilUpper tangencyLabel ∧
        ∀ x ∈ continuumCriticalDoubleDyadicCell E normScale tangencyScale
            normLabel tangencyLabel,
          dyadicCeilUpper normLabel / 2 < normScale x ∧
          normScale x ≤ dyadicCeilUpper normLabel ∧
          dyadicCeilUpper tangencyLabel / 2 < tangencyScale x ∧
          tangencyScale x ≤ dyadicCeilUpper tangencyLabel := by
  classical
  let normLabels : Finset Int :=
    Finset.Icc (dyadicCeilBucket delta) (dyadicCeilBucket normCeiling)
  let tangencyLabels : Finset Int :=
    Finset.Icc (dyadicCeilBucket delta)
      (dyadicCeilBucket tangencyCeiling)
  have hnormLabelLe :
      dyadicCeilBucket delta ≤ dyadicCeilBucket normCeiling :=
    dyadicCeilBucket_mono hdelta hnormCeiling
  have htangencyLabelLe :
      dyadicCeilBucket delta ≤ dyadicCeilBucket tangencyCeiling :=
    dyadicCeilBucket_mono hdelta htangencyCeiling
  have hnormLabels : normLabels.Nonempty := by
    refine ⟨dyadicCeilBucket delta, ?_⟩
    simpa [normLabels] using hnormLabelLe
  have htangencyLabels : tangencyLabels.Nonempty := by
    refine ⟨dyadicCeilBucket delta, ?_⟩
    simpa [tangencyLabels] using htangencyLabelLe
  have hnormRange : ∀ x ∈ E,
      dyadicCeilBucket (normScale x) ∈ normLabels := by
    intro x hx
    change dyadicCeilBucket (normScale x) ∈
      Finset.Icc (dyadicCeilBucket delta) (dyadicCeilBucket normCeiling)
    rw [Finset.mem_Icc]
    have hbounds := hnormBounds x hx
    have hxPositive : 0 < normScale x := hdelta.trans_le hbounds.1
    exact ⟨dyadicCeilBucket_mono hdelta hbounds.1,
      dyadicCeilBucket_mono hxPositive hbounds.2⟩
  have htangencyRange : ∀ x ∈ E,
      dyadicCeilBucket (tangencyScale x) ∈ tangencyLabels := by
    intro x hx
    change dyadicCeilBucket (tangencyScale x) ∈
      Finset.Icc (dyadicCeilBucket delta)
        (dyadicCeilBucket tangencyCeiling)
    rw [Finset.mem_Icc]
    have hbounds := htangencyBounds x hx
    have hxPositive : 0 < tangencyScale x := hdelta.trans_le hbounds.1
    exact ⟨dyadicCeilBucket_mono hdelta hbounds.1,
      dyadicCeilBucket_mono hxPositive hbounds.2⟩
  obtain ⟨normLabel, hnormLabel, tangencyLabel, htangencyLabel,
      hmeasure⟩ :=
    exists_measurableDoubleLabelCell_measure_ge_average μ
      normLabels tangencyLabels hnormLabels htangencyLabels hE
      (measurable_dyadicCeilBucket.comp hnormMeasurable)
      (measurable_dyadicCeilBucket.comp htangencyMeasurable)
      hnormRange htangencyRange
  refine ⟨normLabel, ?_, tangencyLabel, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [normLabels] using hnormLabel
  · simpa [tangencyLabels] using htangencyLabel
  · simpa [normLabels, tangencyLabels,
      continuumCriticalDoubleDyadicBinFactor,
      continuumCriticalDoubleDyadicCell, Int.card_Icc,
      Function.comp_def] using hmeasure
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · intro x hx
    have hxE : x ∈ E := hx.1
    have hpair :
        (dyadicCeilBucket (normScale x),
          dyadicCeilBucket (tangencyScale x)) =
        (normLabel, tangencyLabel) := by
      simpa [continuumCriticalDoubleDyadicCell,
        measurableDoubleLabelCell, measurableLabelCell] using hx.2
    have hnormEq : dyadicCeilBucket (normScale x) = normLabel :=
      congrArg Prod.fst hpair
    have htangencyEq :
        dyadicCeilBucket (tangencyScale x) = tangencyLabel :=
      congrArg Prod.snd hpair
    have hnormPositive : 0 < normScale x :=
      hdelta.trans_le (hnormBounds x hxE).1
    have htangencyPositive : 0 < tangencyScale x :=
      hdelta.trans_le (htangencyBounds x hxE).1
    have hnormBin := dyadicCeilUpper_half_lt_and_le hnormPositive
    have htangencyBin :=
      dyadicCeilUpper_half_lt_and_le htangencyPositive
    exact ⟨by simpa [hnormEq] using hnormBin.1,
      by simpa [hnormEq] using hnormBin.2,
      by simpa [htangencyEq] using htangencyBin.1,
      by simpa [htangencyEq] using htangencyBin.2⟩

#print axioms continuumCriticalDoubleDyadicBinFactor
#print axioms continuumCriticalDoubleDyadicCell
#print axioms measurableSet_continuumCriticalDoubleDyadicCell
#print axioms exists_continuumCritical_double_dyadic_selection

end

end FamilyStickyCinematicL32ContinuumCriticalDoubleDyadicSelectionV1

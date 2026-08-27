import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteValueFibresWeightedV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverFixedCCodePackingV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresWeightedV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32FiniteValueFibresV1
open FamilyStickyCinematicL32FiniteValueFibresWeightedV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverFixedCCodePackingV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v w z

/-!
# Lossless weighted restricted-C and source-code fibres

The outer split uses the literal final normalized C value.  Inside each such
fibre, the second split uses the source-cover code selected from one cover of
the whole survivor family.  Both identities are exact for arbitrary `ENNReal`
weights; no finiteness or positivity hypothesis on the weights is needed.
-/

section Outer

variable {point : Type u} [MeasurableSpace point]
variable {radius : NNReal} {iota : Type v} [DecidableEq iota]
variable {fineLabel : Type w} [DecidableEq fineLabel]
variable {alpha : Type z} [DecidableEq alpha]
variable {D : CoarseRectangleIncidenceData
  (point := point) (radius := radius) (iota := iota) fineLabel}
variable {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
variable {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
variable {pairScale : Real}
variable (P : ActualRetainedY1ThreeShiftCGridSelection D items
  leftIndex rightIndex labelAt keep pairScale)

/-- Arbitrary extended-real mass splits losslessly over the exact final
normalized-C fibres. -/
theorem finiteENNRealWeight_eq_sum_actualThreeShiftCGridRestrictedFiberWeight
    (survivors : Finset alpha) (shift : Real) (weight : alpha -> ENNReal) :
    finiteENNRealWeight survivors weight =
      ∑ c ∈ actualThreeShiftCGridRestrictedOccupiedValues P survivors shift,
        finiteENNRealWeight
          (actualThreeShiftCGridRestrictedFiber P survivors shift c) weight := by
  simpa only [finiteENNRealWeight,
    actualThreeShiftCGridRestrictedOccupiedValues,
    actualThreeShiftCGridRestrictedFiber] using
      finiteENNRealWeight_eq_sum_finiteValueFiberWeight survivors
        (actualThreeShiftCGridRestrictedValueAt P shift) weight

end Outer


section Inner

variable {point : Type u} [MeasurableSpace point]
variable {radius : NNReal} {iota : Type v} [DecidableEq iota]
variable {fineLabel : Type w} [DecidableEq fineLabel]
variable {alpha : Type z} [DecidableEq alpha]
variable {D : CoarseRectangleIncidenceData
  (point := point) (radius := radius) (iota := iota) fineLabel}
variable {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
variable {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
variable {pairScale : Real}
variable (P : ActualRetainedY1ThreeShiftCGridSelection D items
  leftIndex rightIndex labelAt keep pairScale)

/-- Attach an arbitrary item to a nonempty survivor finset, using the item
itself on the survivor carrier and a fixed survivor only off that carrier. -/
noncomputable def actualThreeShiftCGridRestrictedAttachOrDefault
    (survivors : Finset alpha) (hne : survivors.Nonempty) (a : alpha) :
    ActualY1GridRightCLocalCoverSelectedItem survivors :=
  if ha : a ∈ survivors then ⟨a, ha⟩
  else ⟨Classical.choose hne, Classical.choose_spec hne⟩

@[simp] theorem actualThreeShiftCGridRestrictedAttachOrDefault_val_of_mem
    (survivors : Finset alpha) (hne : survivors.Nonempty)
    {a : alpha} (ha : a ∈ survivors) :
    (actualThreeShiftCGridRestrictedAttachOrDefault survivors hne a).1 = a := by
  simp only [actualThreeShiftCGridRestrictedAttachOrDefault, ha, dite_true]

/-- Total extension of the source-cover code map.  Its value outside the
survivor carrier is irrelevant; the exact fibre below is a subset of that
carrier. -/
noncomputable def actualThreeShiftCGridRestrictedSourceCoverCodeAt
    (survivors : Finset alpha) (hne : survivors.Nonempty)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    alpha -> Tube radius :=
  fun a => actualY1GridRightCLocalCoverCode survivors labelAt pointAt tubeAt
    ballRadius
      (actualThreeShiftCGridRestrictedAttachOrDefault survivors hne a)

@[simp] theorem actualThreeShiftCGridRestrictedSourceCoverCodeAt_of_mem
    (survivors : Finset alpha) (hne : survivors.Nonempty)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    {a : alpha} (ha : a ∈ survivors) :
    actualThreeShiftCGridRestrictedSourceCoverCodeAt (labelAt := labelAt)
        survivors hne pointAt tubeAt ballRadius a =
      actualY1GridRightCLocalCoverCode survivors labelAt pointAt tubeAt
        ballRadius ⟨a, ha⟩ := by
  simp only [actualThreeShiftCGridRestrictedSourceCoverCodeAt,
    actualThreeShiftCGridRestrictedAttachOrDefault, ha, dite_true]

/-- Source-cover codes occupied inside one exact final-C fibre. -/
noncomputable def actualThreeShiftCGridRestrictedSourceCodesAtC
    (survivors : Finset alpha) (rightTube : alpha -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real) :
    Finset (Tube radius) :=
  actualY1GridRightCLocalCoverSourceCodesAtC survivors labelAt rightTube
    pointAt tubeAt ballRadius c

/-- The underlying selected items with one exact final C and one exact
source-cover code. -/
noncomputable def actualThreeShiftCGridRestrictedSourceCodeFiberAtC
    (survivors : Finset alpha) (rightTube : alpha -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius) : Finset alpha :=
  actualY1GridRightCLocalCoverUnderlyingFiber survivors labelAt rightTube
    pointAt tubeAt ballRadius (c, coverCenter)

private theorem restrictedSourceCodesAtC_eq_finiteOccupiedValues
    {survivors : Finset alpha} (hne : survivors.Nonempty)
    {shift c : Real}
    (rightTube : alpha -> Tube radius)
    (hright : forall a, a ∈ survivors ->
      tubeGraphC (rightTube a) =
        actualThreeShiftCGridRestrictedValueAt P shift a)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    finiteOccupiedValues
        (actualThreeShiftCGridRestrictedFiber P survivors shift c)
        (actualThreeShiftCGridRestrictedSourceCoverCodeAt (labelAt := labelAt)
          survivors hne pointAt tubeAt ballRadius) =
      actualThreeShiftCGridRestrictedSourceCodesAtC (labelAt := labelAt)
        survivors rightTube pointAt tubeAt ballRadius c := by
  classical
  ext coverCenter
  rw [mem_finiteOccupiedValues_iff]
  rw [actualThreeShiftCGridRestrictedSourceCodesAtC,
    mem_actualY1GridRightCLocalCoverSourceCodesAtC_iff,
    actualY1GridRightCLocalCoverValues, mem_finiteOccupiedValues_iff]
  constructor
  · rintro ⟨a, haFiber, hcode⟩
    have haData := (mem_finiteValueFiber_iff survivors
      (actualThreeShiftCGridRestrictedValueAt P shift) c a).mp haFiber
    let b : ActualY1GridRightCLocalCoverSelectedItem survivors :=
      ⟨a, haData.1⟩
    refine ⟨b, Finset.mem_univ b, ?_⟩
    apply Prod.ext
    · simpa only [actualY1GridRightCLocalCoverValue, b] using
        (hright a haData.1).trans haData.2
    · change actualY1GridRightCLocalCoverCode survivors labelAt pointAt tubeAt
        ballRadius b = coverCenter
      simpa only [b,
        actualThreeShiftCGridRestrictedSourceCoverCodeAt_of_mem
          (labelAt := labelAt) survivors hne pointAt tubeAt ballRadius haData.1]
        using hcode
  · rintro ⟨b, _hb, hvalue⟩
    have hfirst : tubeGraphC (rightTube b.1) = c := by
      simpa only [actualY1GridRightCLocalCoverValue] using
        congrArg Prod.fst hvalue
    have hsecond : actualY1GridRightCLocalCoverCode survivors labelAt pointAt
        tubeAt ballRadius b = coverCenter := by
      simpa only [actualY1GridRightCLocalCoverValue] using
        congrArg Prod.snd hvalue
    refine ⟨b.1, (mem_finiteValueFiber_iff survivors
      (actualThreeShiftCGridRestrictedValueAt P shift) c b.1).mpr
        ⟨b.2, ?_⟩, ?_⟩
    · exact (hright b.1 b.2).symm.trans hfirst
    · simpa only [actualThreeShiftCGridRestrictedSourceCoverCodeAt_of_mem
        (labelAt := labelAt) survivors hne pointAt tubeAt ballRadius b.2]
        using hsecond

private theorem finiteValueFiber_restrictedSourceCode_eq_underlyingFiber
    {survivors : Finset alpha} (hne : survivors.Nonempty)
    {shift c : Real}
    (rightTube : alpha -> Tube radius)
    (hright : forall a, a ∈ survivors ->
      tubeGraphC (rightTube a) =
        actualThreeShiftCGridRestrictedValueAt P shift a)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (coverCenter : Tube radius) :
    finiteValueFiber
        (actualThreeShiftCGridRestrictedFiber P survivors shift c)
        (actualThreeShiftCGridRestrictedSourceCoverCodeAt (labelAt := labelAt)
          survivors hne pointAt tubeAt ballRadius) coverCenter =
      actualThreeShiftCGridRestrictedSourceCodeFiberAtC (labelAt := labelAt)
        survivors rightTube pointAt tubeAt ballRadius c coverCenter := by
  classical
  ext a
  rw [mem_finiteValueFiber_iff]
  constructor
  · rintro ⟨haFiber, hcode⟩
    have haData := (mem_finiteValueFiber_iff survivors
      (actualThreeShiftCGridRestrictedValueAt P shift) c a).mp haFiber
    let b : ActualY1GridRightCLocalCoverSelectedItem survivors :=
      ⟨a, haData.1⟩
    rw [actualThreeShiftCGridRestrictedSourceCodeFiberAtC,
      actualY1GridRightCLocalCoverUnderlyingFiber]
    apply Finset.mem_image.mpr
    refine ⟨b, ?_, rfl⟩
    apply (mem_finiteValueFiber_iff Finset.univ
      (actualY1GridRightCLocalCoverValue survivors labelAt rightTube pointAt
        tubeAt ballRadius) (c, coverCenter) b).mpr
    refine ⟨Finset.mem_univ b, ?_⟩
    apply Prod.ext
    · simpa only [actualY1GridRightCLocalCoverValue, b] using
        (hright a haData.1).trans haData.2
    · change actualY1GridRightCLocalCoverCode survivors labelAt pointAt tubeAt
        ballRadius b = coverCenter
      simpa only [b,
        actualThreeShiftCGridRestrictedSourceCoverCodeAt_of_mem
          (labelAt := labelAt) survivors hne pointAt tubeAt ballRadius haData.1]
        using hcode
  · intro ha
    have haSelected :=
      actualY1GridRightCLocalCoverUnderlyingFiber_subset survivors labelAt
        rightTube pointAt tubeAt ballRadius (c, coverCenter) ha
    have haRight :=
      actualY1GridRightCLocalCoverUnderlyingFiber_rightGraphC survivors labelAt
        rightTube pointAt tubeAt ballRadius c coverCenter a ha
    have haCode :=
      actualY1GridRightCLocalCoverUnderlyingFiber_coverCode_eq survivors labelAt
        rightTube pointAt tubeAt ballRadius c coverCenter a ha haSelected
    refine ⟨(mem_finiteValueFiber_iff survivors
      (actualThreeShiftCGridRestrictedValueAt P shift) c a).mpr
        ⟨haSelected, ?_⟩, ?_⟩
    · exact (hright a haSelected).symm.trans haRight
    · simpa only [actualThreeShiftCGridRestrictedSourceCoverCodeAt_of_mem
        (labelAt := labelAt) survivors hne pointAt tubeAt ballRadius haSelected]
        using haCode

/-- Inside one exact normalized-C fibre, arbitrary extended-real mass splits
losslessly over the occupied source-cover codes.  The fibres on the right are
the existing underlying joint `(C, code)` fibres, so this theorem plugs into
the fixed-C geometric adapters without a reindexing loss. -/
theorem finiteENNRealWeight_actualThreeShiftCGridRestrictedFiber_eq_sum_sourceCodeFiberWeight
    {survivors : Finset alpha} (hne : survivors.Nonempty)
    {shift c : Real}
    (rightTube : alpha -> Tube radius)
    (hright : forall a, a ∈ survivors ->
      tubeGraphC (rightTube a) =
        actualThreeShiftCGridRestrictedValueAt P shift a)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (weight : alpha -> ENNReal) :
    finiteENNRealWeight
        (actualThreeShiftCGridRestrictedFiber P survivors shift c) weight =
      ∑ coverCenter ∈
          actualThreeShiftCGridRestrictedSourceCodesAtC (labelAt := labelAt)
            survivors rightTube pointAt tubeAt ballRadius c,
        finiteENNRealWeight
          (actualThreeShiftCGridRestrictedSourceCodeFiberAtC
            (labelAt := labelAt) survivors rightTube pointAt tubeAt ballRadius
              c coverCenter) weight := by
  have hpartition := finiteENNRealWeight_eq_sum_finiteValueFiberWeight
    (actualThreeShiftCGridRestrictedFiber P survivors shift c)
    (actualThreeShiftCGridRestrictedSourceCoverCodeAt (labelAt := labelAt)
      survivors hne pointAt tubeAt ballRadius) weight
  rw [restrictedSourceCodesAtC_eq_finiteOccupiedValues P hne rightTube
    hright pointAt tubeAt ballRadius] at hpartition
  simpa only [finiteENNRealWeight,
    finiteValueFiber_restrictedSourceCode_eq_underlyingFiber P hne
      rightTube hright pointAt tubeAt ballRadius] using hpartition

#print axioms finiteENNRealWeight_eq_sum_actualThreeShiftCGridRestrictedFiberWeight
#print axioms finiteENNRealWeight_actualThreeShiftCGridRestrictedFiber_eq_sum_sourceCodeFiberWeight

end Inner

end

end FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresWeightedV1

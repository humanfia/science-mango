import Family8Grounding.Family8GreedyWinnerAutomaticJohnSideBucketV1
import Family8Grounding.Family8GreedyWinnerNormalizedPlankBucketV1
import Family8Grounding.Family8SelectedOccurrenceDensityFrostmanV1
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Mathlib.Tactic

/-!
# A common normalized datum on the exact selected-occurrence outer index

For a literal selected occurrence set and one already chosen John-side label,
this file applies the label's single scalar affine equivalence to the actual
greedy winning bodies and their actual outer shading.  The index type remains
the `Option`-valued selected coarse subtype used by the selected-occurrence
factorization; no occurrence is selected or discarded here.

The wrapper records only exact affine transport, the common `576`-plank
certificate, and the resulting Family 6 datum.  In particular it contains no
owner or thick-plank-control hypothesis.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedOccurrenceNormalizedOuterDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8GreedyWinnerNormalizedPlankBucketV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- The one positive scalar affine equivalence attached to a side label. -/
def selectedOccurrenceNormalizedOuterAffineEquiv
    (labelOuter : Fin 3 -> Int) : Space ≃ᵃ[Real] Space :=
  scalarDilationAffineEquiv
    (sideShapeUpper labelOuter 2)⁻¹
    (inv_pos.mpr (sideShapeUpper_pos labelOuter 2))

/-- Decode an exact selected coarse index `some k` to its occurrence position.
This is a reindexing operation, not a new choice of a retained occurrence. -/
noncomputable def selectedOccurrenceNormalizedOuterPosition
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P Rside}) :
    Fin (blocks fine.bodyFamily P).length :=
  Classical.choose ((mem_selectedOccurrenceIndices P Rside q.1).mp q.2)

theorem selectedOccurrenceNormalizedOuterPosition_mem
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P Rside}) :
    selectedOccurrenceNormalizedOuterPosition P Rside q ∈ Rside :=
  (Classical.choose_spec
    ((mem_selectedOccurrenceIndices P Rside q.1).mp q.2)).1

theorem some_selectedOccurrenceNormalizedOuterPosition_eq
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P Rside}) :
    some (selectedOccurrenceNormalizedOuterPosition P Rside q) = q.1 :=
  (Classical.choose_spec
    ((mem_selectedOccurrenceIndices P Rside q.1).mp q.2)).2

/-- The exact selected outer family in the common normalized coordinates. -/
abbrev selectedOccurrenceNormalizedOuterFamily
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length)) :
    ConvexFamily {q // q ∈ selectedOccurrenceIndices P Rside} :=
  affineImageFamily
    (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter)
    (selectedOccurrenceOuterFamily P Rside)

/-- The exact selected outer shading transported by the same common map. -/
def selectedOccurrenceNormalizedOuterShading
    (Y : Shading fine.bodyFamily)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length)) :
    Shading (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside) :=
  affineImageShading
    (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter)
    (selectedOccurrenceOuterShading P Y Rside)

/-- At an exact selected outer index, the normalized family is literally the
existing normalized greedy winner body at the decoded occurrence position. -/
@[simp] theorem selectedOccurrenceNormalizedOuterFamily_apply
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P Rside}) :
    selectedOccurrenceNormalizedOuterFamily P labelOuter Rside q =
      normalizedWinnerBody P labelOuter
        (selectedOccurrenceNormalizedOuterPosition P Rside q) := by
  let k := selectedOccurrenceNormalizedOuterPosition P Rside q
  have hk : k ∈ Rside :=
    selectedOccurrenceNormalizedOuterPosition_mem P Rside q
  have hq : q = selectedOccurrenceIndexOf P Rside k hk := by
    apply Subtype.ext
    exact (some_selectedOccurrenceNormalizedOuterPosition_eq P Rside q).symm
  change affineImageConvexBody
      (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter)
      (selectedOccurrenceOuterFamily P Rside q) =
    normalizedWinnerBody P labelOuter k
  rw [hq, selectedOccurrenceOuterFamily_indexOf]
  rfl

/-- A literal common side label on `Rside` gives the same genuine plank
dimensions on every member of the exact Option-indexed normalized outer
family. -/
theorem selectedOccurrenceNormalizedOuterFamily_all_isPlank
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (q : {q // q ∈ selectedOccurrenceIndices P Rside}) :
    IsPlank 576 (bucketShortA labelOuter) (bucketShortB labelOuter)
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside q) := by
  let k := selectedOccurrenceNormalizedOuterPosition P Rside q
  have hk : k ∈ Rside :=
    selectedOccurrenceNormalizedOuterPosition_mem P Rside q
  have hkLabel := hlabel k hk
  have hpos : forall j, 0 < winnerLongSide P hdelta k j :=
    fun j => winnerLongSide_pos P hdelta k j
  have h02 := sideShapeUpper_le_of_side_le hpos
    (winnerLongSide_le_two P hdelta k 0)
  have h12 := sideShapeUpper_le_of_side_le hpos
    (winnerLongSide_le_two P hdelta k 1)
  rw [hkLabel] at h02 h12
  have hband0 := sideShapeUpper_half_lt_and_le hpos
  have hband : forall j,
      sideShapeUpper labelOuter j / 2 < winnerLongSide P hdelta k j ∧
        winnerLongSide P hdelta k j <= sideShapeUpper labelOuter j := by
    intro j
    simpa only [hkLabel] using hband0 j
  rw [selectedOccurrenceNormalizedOuterFamily_apply]
  exact normalizedWinnerBody_isPlank P hdelta labelOuter k
    (bucketShortB_le_one labelOuter h02 h12) hband

/-- Common affine normalization preserves the actual outer average exactly. -/
theorem selectedOccurrenceNormalizedOuterShading_averageMultiplicity
    (Y : Shading fine.bodyFamily)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (selectedOccurrenceNormalizedOuterShading
        P Y labelOuter Rside).averageMultiplicity =
      (selectedOccurrenceOuterShading P Y Rside).averageMultiplicity := by
  exact affineImageShading_averageMultiplicity
    (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter)
    (selectedOccurrenceOuterShading P Y Rside)

/-- Common affine normalization preserves the actual outer shading density
exactly. -/
theorem selectedOccurrenceNormalizedOuterShading_shadingDensity
    (Y : Shading fine.bodyFamily)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (selectedOccurrenceNormalizedOuterShading
        P Y labelOuter Rside).shadingDensity =
      (selectedOccurrenceOuterShading P Y Rside).shadingDensity := by
  exact affineImageShading_shadingDensity
    (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter)
    (selectedOccurrenceOuterShading P Y Rside)

/-- Frostman control transports to the normalized outer family without any
change in its constant. -/
theorem selectedOccurrenceNormalizedOuterFamily_isFrostmanIn
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space) {CF : ENNReal}
    (hF : IsFrostmanIn CF (selectedOccurrenceOuterFamily P Rside) ambient) :
    IsFrostmanIn CF
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside)
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient) := by
  exact IsFrostmanIn.affineImage
    (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) hF

/-- The exact normalized outer index count is the literal retained occurrence
count; affine normalization and Option reindexing add no cardinality loss. -/
@[simp] theorem selectedOccurrenceNormalizedOuter_index_card
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length)) :
    Fintype.card {q // q ∈ selectedOccurrenceIndices P Rside} =
      Rside.card := by
  change selectedOccurrenceOuterCount P Rside = Rside.card
  exact selectedOccurrenceOuterCount_eq_card P Rside

/-- Package the normalized family and shading as the literal Family 6 datum.
The ambient certificate is supplied by the caller; no owner or thick-control
field is introduced. -/
def selectedOccurrenceNormalizedOuterDatum
    (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (ambient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient))
    (contained_in_ambient : forall q,
      (selectedOccurrenceOuterFamily P Rside q : Set Space) ⊆
        (ambient : Set Space)) :
    ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P Rside}
      (bucketShortA labelOuter) (bucketShortB labelOuter) where
  family := selectedOccurrenceNormalizedOuterFamily P labelOuter Rside
  shading := selectedOccurrenceNormalizedOuterShading P Y labelOuter Rside
  comparisonConstant := 576
  all_isPlank := selectedOccurrenceNormalizedOuterFamily_all_isPlank
    P hdelta labelOuter Rside hlabel
  ambient := affineImageConvexBody
    (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient
  ambientComparisonConstant := ambientComparisonConstant
  ambient_is_unit_scale := ambient_is_unit_scale
  contained_in_ambient q := Set.image_mono (contained_in_ambient q)

#print axioms selectedOccurrenceNormalizedOuterFamily_apply
#print axioms selectedOccurrenceNormalizedOuterFamily_all_isPlank
#print axioms selectedOccurrenceNormalizedOuterShading_averageMultiplicity
#print axioms selectedOccurrenceNormalizedOuterShading_shadingDensity
#print axioms selectedOccurrenceNormalizedOuterFamily_isFrostmanIn
#print axioms selectedOccurrenceNormalizedOuter_index_card
#print axioms selectedOccurrenceNormalizedOuterDatum

end
end Family8SelectedOccurrenceNormalizedOuterDatumV1

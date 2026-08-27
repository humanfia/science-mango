import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstBilateralSupportBoundaryV1

open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

noncomputable section

/-!
# Exact bilateral fine-label support boundary

The sharp E2/G-prime pipeline currently counts retained incidences after
grouping by coarse rectangle.  Label-first sampling needs a different fact:
one fine label must have a retained tube in each of the two separated
coefficient balls.  This module names the two one-sided supports, identifies
their intersection with the genuine bilateral carrier, and records two
precise sufficient conditions for positivity.

The final finite counterexample formalizes why nonempty left and right
supports inside one common coarse cluster do not by themselves imply a
common fine label.
-/

universe u v

/-- Fine labels hit by retained incidences in one canonical coefficient
ball. -/
noncomputable def actualGPrimeRetainedFineLabelSupport
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (center : iota)
    (ballRadius : Real) : Finset fineLabel :=
  D.fineLabels.filter fun r =>
    (actualGPrimeRetainedFineMetricNeighbors
      N D keep center ballRadius r).Nonempty

@[simp]
theorem mem_actualGPrimeRetainedFineLabelSupport_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (center : iota)
    (ballRadius : Real) (r : fineLabel) :
    r ∈ actualGPrimeRetainedFineLabelSupport
        N D keep center ballRadius ↔
      r ∈ D.fineLabels ∧
        (actualGPrimeRetainedFineMetricNeighbors
          N D keep center ballRadius r).Nonempty := by
  classical
  simp [actualGPrimeRetainedFineLabelSupport]

/-- The label-first carrier is literally the intersection of the two
one-sided fine-label supports. -/
theorem actualGPrimeBilateralRetainedFineLabels_eq_inter_supports
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) :
    actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius =
      actualGPrimeRetainedFineLabelSupport N D keep left ballRadius ∩
        actualGPrimeRetainedFineLabelSupport N D keep right ballRadius := by
  classical
  ext r
  simp only [mem_actualGPrimeBilateralRetainedFineLabels_iff,
    Finset.mem_inter, mem_actualGPrimeRetainedFineLabelSupport_iff]
  tauto

/-- Same-label cross-edge mass.  Its positivity is the exact mass statement
needed before the label-first sampler can run. -/
noncomputable def actualGPrimeCommonFineEdgeMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) : Nat :=
  ∑ r ∈ D.fineLabels,
    (actualGPrimeRetainedFineMetricNeighbors
      N D keep left ballRadius r).card *
    (actualGPrimeRetainedFineMetricNeighbors
      N D keep right ballRadius r).card

/-- Positive same-label cross-edge mass is equivalent to nonempty genuine
bilateral fine-label support. -/
theorem actualGPrimeCommonFineEdgeMass_pos_iff_bilateral_nonempty
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) :
    0 < actualGPrimeCommonFineEdgeMass
        N D keep left right ballRadius ↔
      (actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius).Nonempty := by
  classical
  constructor
  · intro hmass
    change 0 < ∑ r ∈ D.fineLabels,
      (actualGPrimeRetainedFineMetricNeighbors
        N D keep left ballRadius r).card *
      (actualGPrimeRetainedFineMetricNeighbors
        N D keep right ballRadius r).card at hmass
    obtain ⟨r, hr, hterm⟩ := Finset.sum_pos_iff.mp hmass
    have hleftCard : 0 < (actualGPrimeRetainedFineMetricNeighbors
        N D keep left ballRadius r).card :=
      pos_of_mul_pos_left hterm (Nat.zero_le _)
    have hrightCard : 0 < (actualGPrimeRetainedFineMetricNeighbors
        N D keep right ballRadius r).card :=
      pos_of_mul_pos_right hterm (Nat.zero_le _)
    exact ⟨r, (mem_actualGPrimeBilateralRetainedFineLabels_iff
      N D keep left right ballRadius r).mpr
        ⟨hr, Finset.card_pos.mp hleftCard, Finset.card_pos.mp hrightCard⟩⟩
  · rintro ⟨r, hr⟩
    have hrData := (mem_actualGPrimeBilateralRetainedFineLabels_iff
      N D keep left right ballRadius r).mp hr
    change 0 < ∑ r ∈ D.fineLabels,
      (actualGPrimeRetainedFineMetricNeighbors
        N D keep left ballRadius r).card *
      (actualGPrimeRetainedFineMetricNeighbors
        N D keep right ballRadius r).card
    apply Finset.sum_pos'
    · intro s _hs
      exact Nat.zero_le _
    · exact ⟨r, hrData.1, Nat.mul_pos
        (Finset.card_pos.mpr hrData.2.1)
        (Finset.card_pos.mpr hrData.2.2)⟩

/-- A directly usable pigeonhole criterion: if the two one-sided supports
together contain more labels than the ambient fine-label family, then a
genuine common fine label exists. -/
theorem actualGPrimeBilateralRetainedFineLabels_nonempty_of_support_card_sum
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (hcard : D.fineLabels.card <
      (actualGPrimeRetainedFineLabelSupport
        N D keep left ballRadius).card +
      (actualGPrimeRetainedFineLabelSupport
        N D keep right ballRadius).card) :
    (actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius).Nonempty := by
  classical
  let leftSupport := actualGPrimeRetainedFineLabelSupport
    N D keep left ballRadius
  let rightSupport := actualGPrimeRetainedFineLabelSupport
    N D keep right ballRadius
  have hleftSubset : leftSupport ⊆ D.fineLabels := by
    intro r hr
    exact (mem_actualGPrimeRetainedFineLabelSupport_iff
      N D keep left ballRadius r).mp hr |>.1
  have hrightSubset : rightSupport ⊆ D.fineLabels := by
    intro r hr
    exact (mem_actualGPrimeRetainedFineLabelSupport_iff
      N D keep right ballRadius r).mp hr |>.1
  have hunionSubset : leftSupport ∪ rightSupport ⊆ D.fineLabels :=
    Finset.union_subset hleftSubset hrightSubset
  have hunionCard : (leftSupport ∪ rightSupport).card <=
      D.fineLabels.card := Finset.card_le_card hunionSubset
  have hinterCard : 0 < (leftSupport ∩ rightSupport).card := by
    have hidentity := Finset.card_union_add_card_inter
      leftSupport rightSupport
    change D.fineLabels.card < leftSupport.card + rightSupport.card at hcard
    omega
  rw [actualGPrimeBilateralRetainedFineLabels_eq_inter_supports]
  exact Finset.card_pos.mp hinterCard

/-- Formal obstruction: two nonempty fine-label supports can lie in one
common coarse cluster and still be disjoint.  Thus the current common-coarse
G-prime output cannot imply bilateral support without a new overlap/mass
input. -/
theorem same_coarse_nonempty_side_supports_counterexample :
    let fineLabels : Finset Bool := {false, true}
    let leftSupport : Finset Bool := {false}
    let rightSupport : Finset Bool := {true}
    let coarseAt : Bool -> Unit := fun _ => ()
    leftSupport ⊆ fineLabels ∧
      rightSupport ⊆ fineLabels ∧
      leftSupport.Nonempty ∧ rightSupport.Nonempty ∧
      (forall l, l ∈ leftSupport -> forall r, r ∈ rightSupport ->
        coarseAt l = coarseAt r) ∧
      ¬ (leftSupport ∩ rightSupport).Nonempty := by
  decide

#print axioms actualGPrimeRetainedFineLabelSupport
#print axioms mem_actualGPrimeRetainedFineLabelSupport_iff
#print axioms actualGPrimeBilateralRetainedFineLabels_eq_inter_supports
#print axioms actualGPrimeCommonFineEdgeMass
#print axioms actualGPrimeCommonFineEdgeMass_pos_iff_bilateral_nonempty
#print axioms actualGPrimeBilateralRetainedFineLabels_nonempty_of_support_card_sum
#print axioms same_coarse_nonempty_side_supports_counterexample

end

end FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstBilateralSupportBoundaryV1

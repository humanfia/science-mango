import Family8Grounding.Family8Prop51SelectedOccurrenceSourceFrostmanV1
import Mathlib.Tactic

/-!
# Canonical ambient-mass loss for the Proposition 5.1 selection

The selected-source Frostman restriction needs a comparison between the full
and selected ambient contained masses.  This file removes that comparison as
a conclusion-valued premise: once the selected ambient mass is nonzero, the
comparison coefficient is the literal quotient of the two actual masses
(normalized by `max 1`).

The remaining nondegeneracy is geometric.  It asks that the canonical joint
bucket really contain positive source body mass; no desired inequality is
stored in an input structure or accepted as a callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51SelectedOccurrenceAmbientMassRatioV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- The actual source indices in the canonical Proposition 5.1 bucket. -/
abbrev prop51SelectedFineIndices
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) : Finset iota :=
  selectedOccurrenceFineIndices P
    (prop51SelectedOccurrences P Y base M)

/-- The honest full-to-selected ambient body-mass loss. -/
def prop51SelectedAmbientMassLoss
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) : ENNReal :=
  max 1
    (containedMassOn F active K /
      containedMassOn F (prop51SelectedFineIndices P Y base M) K)

/-- Every selected ambient contained mass is finite. -/
theorem prop51SelectedAmbientMass_ne_top
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) :
    containedMassOn F (prop51SelectedFineIndices P Y base M) K ≠ ∞ := by
  classical
  unfold containedMassOn
  apply ENNReal.sum_ne_top.2
  intro i hi
  exact (F i).isCompact.measure_lt_top.ne

/-- The quotient loss gives the exact required ambient-mass retention as soon
as the selected source mass is nonzero. -/
theorem prop51SelectedAmbientMass_retention
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space)
    (hselected : containedMassOn F
      (prop51SelectedFineIndices P Y base M) K ≠ 0) :
    containedMassOn F active K ≤
      prop51SelectedAmbientMassLoss P Y base M K *
        containedMassOn F (prop51SelectedFineIndices P Y base M) K := by
  let selectedMass :=
    containedMassOn F (prop51SelectedFineIndices P Y base M) K
  have hselectedTop : selectedMass ≠ ∞ := by
    exact prop51SelectedAmbientMass_ne_top P Y base M K
  calc
    containedMassOn F active K =
        (containedMassOn F active K / selectedMass) * selectedMass := by
      exact (ENNReal.div_mul_cancel hselected hselectedTop).symm
    _ ≤ max 1 (containedMassOn F active K / selectedMass) *
        selectedMass := by
      gcongr
      exact le_max_right _ _
    _ = prop51SelectedAmbientMassLoss P Y base M K *
        containedMassOn F (prop51SelectedFineIndices P Y base M) K := by
      rfl

/-- Global source Frostman non-concentration restricts to the canonical
selected source family with the literal ambient-mass ratio loss. -/
theorem prop51SelectedOccurrences_source_fine_frostman_of_nonzero
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) {C : ENNReal}
    (hglobal : IsFrostmanOn C F active K)
    (hselected : containedMassOn F
      (prop51SelectedFineIndices P Y base M) K ≠ 0) :
    IsFrostmanOn
      (C * prop51SelectedAmbientMassLoss P Y base M K) F
      (prop51SelectedFineIndices P Y base M) K := by
  exact prop51SelectedOccurrences_source_fine_frostman
    P Y base M K hglobal
      (prop51SelectedAmbientMass_retention P Y base M K hselected)

#print axioms prop51SelectedAmbientMass_ne_top
#print axioms prop51SelectedAmbientMass_retention
#print axioms prop51SelectedOccurrences_source_fine_frostman_of_nonzero

end

end Family8Prop51SelectedOccurrenceAmbientMassRatioV1

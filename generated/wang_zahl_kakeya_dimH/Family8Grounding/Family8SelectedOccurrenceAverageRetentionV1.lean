import Family8Grounding.Family8SelectedOccurrenceDensityFrostmanV1
import Submission.Kakeya.ConvexFactoring.RefinementMultiplicity
import Mathlib.Tactic

/-!
# Average-multiplicity transport to a selected occurrence family

The paper applies the outer estimate after selecting `W'`.  The current
Family 8 endpoint still displays the induced shading on every greedy
occurrence.  This file gives the exact object-level bridge between them.

Restrict the induced shading to `S.image some`.  Its mass, shaded union, and
average multiplicity are exactly those of the attached selected-occurrence
shading.  Consequently any genuine mass-retention estimate

`full.shadingMass <= loss * selected.shadingMass`

implies `full.averageMultiplicity <= loss * selected.averageMultiplicity`.
No analytic multiplicity bound is assumed.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceAverageRetentionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- The full induced occurrence shading before the paper's `W'` selection. -/
abbrev fullOccurrenceInducedShading
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) : Shading (coarseFamily F P) :=
  (convexFactorization F P).inducedShading Y

/-- The same shading restricted, on its original `Option` index type, to the
genuine selected occurrence indices. -/
def selectedOccurrenceRefinement
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length)) :
    IndexedShadingRefinement (fullOccurrenceInducedShading P Y) :=
  IndexedShadingRefinement.restrictTo
    (fullOccurrenceInducedShading P Y) (selectedOccurrenceIndices P S)

/-- Reindexing the selected nonempty carriers by their attached subtype does
not change selected shaded mass. -/
theorem selectedOccurrenceRefinement_shadingMass_eq
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceRefinement P Y S).shading.shadingMass =
      (selectedOccurrenceOuterShading P Y S).shadingMass := by
  unfold selectedOccurrenceRefinement selectedOccurrenceOuterShading
  rw [shadingMass_restrictTo_eq_sum, selectedCoarseShading_mass]

/-- Reindexing the selected nonempty carriers also preserves their literal
shaded union. -/
theorem selectedOccurrenceRefinement_shadedUnion_eq
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceRefinement P Y S).shading.shadedUnion =
      (selectedOccurrenceOuterShading P Y S).shadedUnion := by
  unfold selectedOccurrenceRefinement selectedOccurrenceOuterShading
  ext x
  constructor
  · intro hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    rw [IndexedShadingRefinement.restrictTo_carrier] at hxq
    by_cases hq : q ∈ selectedOccurrenceIndices P S
    · rw [if_pos hq] at hxq
      exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩
    · rw [if_neg hq] at hxq
      exact hxq.elim
  · intro hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨q.1, ?_⟩
    rw [IndexedShadingRefinement.restrictTo_carrier, if_pos q.2]
    exact hxq

/-- Thus the two presentations of selected `W'` have identical average
multiplicity. -/
theorem selectedOccurrenceRefinement_averageMultiplicity_eq
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceRefinement P Y S).shading.averageMultiplicity =
      (selectedOccurrenceOuterShading P Y S).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [selectedOccurrenceRefinement_shadingMass_eq P Y S,
    selectedOccurrenceRefinement_shadedUnion_eq P Y S]

/-- The selected shaded union is automatically contained in the full induced
shaded union. -/
theorem selectedOccurrenceOuterShading_shadedUnion_subset_full
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceOuterShading P Y S).shadedUnion ⊆
      (fullOccurrenceInducedShading P Y).shadedUnion := by
  rw [← selectedOccurrenceRefinement_shadedUnion_eq P Y S]
  exact (selectedOccurrenceRefinement P Y S).shadedUnion_subset

/-- Arbitrary ENNReal mass-retention loss transports the selected Eq. (45)
average bound back to the full induced occurrence shading. -/
theorem fullAverage_le_loss_mul_selectedAverage_of_mass_retention
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length))
    (loss : ENNReal)
    (hretained :
      (fullOccurrenceInducedShading P Y).shadingMass ≤
        loss * (selectedOccurrenceOuterShading P Y S).shadingMass) :
    (fullOccurrenceInducedShading P Y).averageMultiplicity ≤
      loss * (selectedOccurrenceOuterShading P Y S).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  calc
    (fullOccurrenceInducedShading P Y).shadingMass /
          volume (fullOccurrenceInducedShading P Y).shadedUnion ≤
        (loss * (selectedOccurrenceOuterShading P Y S).shadingMass) /
          volume (fullOccurrenceInducedShading P Y).shadedUnion :=
      ENNReal.div_le_div_right hretained _
    _ ≤ (loss * (selectedOccurrenceOuterShading P Y S).shadingMass) /
          volume (selectedOccurrenceOuterShading P Y S).shadedUnion := by
      exact ENNReal.div_le_div_left
        (measure_mono
          (selectedOccurrenceOuterShading_shadedUnion_subset_full P Y S)) _
    _ = loss *
          ((selectedOccurrenceOuterShading P Y S).shadingMass /
            volume (selectedOccurrenceOuterShading P Y S).shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Nat-valued `WithinFactor` retention is the standard refinement form of
the same bridge. -/
theorem fullAverage_le_nsmul_selectedAverage_of_withinFactor
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length))
    (loss : Nat)
    (hretained : WithinFactor loss
      (fullOccurrenceInducedShading P Y).shadingMass
      (selectedOccurrenceOuterShading P Y S).shadingMass) :
    (fullOccurrenceInducedShading P Y).averageMultiplicity ≤
      loss • (selectedOccurrenceOuterShading P Y S).averageMultiplicity := by
  have hrefined : WithinFactor loss
      (fullOccurrenceInducedShading P Y).shadingMass
      (selectedOccurrenceRefinement P Y S).shading.shadingMass := by
    rw [selectedOccurrenceRefinement_shadingMass_eq P Y S]
    exact hretained
  have hresult :=
    (selectedOccurrenceRefinement P Y S).averageMultiplicity_le loss hrefined
  rw [selectedOccurrenceRefinement_averageMultiplicity_eq P Y S] at hresult
  exact hresult

#print axioms selectedOccurrenceRefinement_shadingMass_eq
#print axioms selectedOccurrenceRefinement_shadedUnion_eq
#print axioms selectedOccurrenceRefinement_averageMultiplicity_eq
#print axioms selectedOccurrenceOuterShading_shadedUnion_subset_full
#print axioms fullAverage_le_loss_mul_selectedAverage_of_mass_retention
#print axioms fullAverage_le_nsmul_selectedAverage_of_withinFactor

end

end Family8SelectedOccurrenceAverageRetentionV1

import Family8Grounding.Family8Prop51SelectedOccurrenceAmbientMassRatioV1
import Mathlib.Tactic

/-!
# Positive ambient mass for the canonical Proposition 5.1 occurrence bucket

The selected outer shading is supported by the union of the fine bodies in
the same selected greedy blocks.  Since distinct greedy blocks have disjoint
fine-index fibres, its mass is bounded by the multiplicity-counted body mass
of the literal selected source indices.  Ambient containment then turns this
into a bound by `containedMassOn`.

Consequently positive full induced outer mass, together with the already
proved canonical mass retention, makes the selected ambient denominator
nonzero.  This discharges the last nondegeneracy premise of the literal
mass-ratio Frostman theorem without a conclusion-valued callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51SelectedOccurrenceAmbientMassPositiveV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceAverageRetentionV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8Prop51SelectedOccurrenceAmbientMassRatioV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- One induced occurrence carrier is contained in the finite union of the
fine bodies in its literal greedy block, so its shaded mass is at most the
block's multiplicity-counted body mass. -/
theorem occurrenceOuterShadedMass_le_blockMass
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (k : Fin (blocks F P).length) :
    occurrenceOuterShadedMass P Y k ≤
      blockMass F (blockAt F P k) := by
  have hsubset :
      ((convexFactorization F P).inducedShading Y).carrier (some k) ⊆
        ⋃ i ∈ (blockAt F P k).fiber, (F i : Set Space) := by
    intro x hx
    obtain ⟨_hk, i, hi, hxi⟩ :=
      ((convexFactorization F P).mem_inducedShading_carrier_iff
        Y (some k) x).1 hx
    have hiBlock : i ∈ (blockAt F P k).fiber := by
      rw [← indexFactorization_fiber_eq_blockAt F P k]
      exact hi
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨hiBlock, Y.carrier_subset i hxi⟩⟩
  calc
    occurrenceOuterShadedMass P Y k =
        volume (((convexFactorization F P).inducedShading Y).carrier
          (some k)) := rfl
    _ ≤ volume (⋃ i ∈ (blockAt F P k).fiber, (F i : Set Space)) :=
      measure_mono hsubset
    _ ≤ ∑ i ∈ (blockAt F P k).fiber, volume (F i : Set Space) :=
      measure_biUnion_finset_le (blockAt F P k).fiber _
    _ = blockMass F (blockAt F P k) := rfl

/-- Pairwise disjointness of greedy fibres identifies the sum of selected
block masses with the body mass on the literal selected fine set. -/
theorem selectedOccurrenceOuterShading_mass_le_bodyMassOn
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceOuterShading P Y S).shadingMass ≤
      bodyMassOn F (selectedOccurrenceFineIndices P S) := by
  classical
  rw [selectedOccurrenceOuterShading_mass_eq_sum_occurrenceOuterShadedMass]
  calc
    (∑ k ∈ S, occurrenceOuterShadedMass P Y k) ≤
        ∑ k ∈ S, blockMass F (blockAt F P k) := by
      exact Finset.sum_le_sum fun k _hk =>
        occurrenceOuterShadedMass_le_blockMass P Y k
    _ = bodyMassOn F (selectedOccurrenceFineIndices P S) := by
      unfold selectedOccurrenceFineIndices bodyMassOn blockMass
      exact (Finset.sum_biUnion
        (blockAt_fibers_pairwiseDisjoint F P S)).symm

/-- If every selected fine body lies in `K`, the same outer mass is bounded
by the selected source `containedMassOn` denominator. -/
theorem selectedOccurrenceOuterShading_mass_le_containedMassOn
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length))
    (K : ConvexBody Space)
    (hcontained : ∀ i ∈ selectedOccurrenceFineIndices P S,
      (F i : Set Space) ⊆ (K : Set Space)) :
    (selectedOccurrenceOuterShading P Y S).shadingMass ≤
      containedMassOn F (selectedOccurrenceFineIndices P S) K := by
  calc
    (selectedOccurrenceOuterShading P Y S).shadingMass ≤
        bodyMassOn F (selectedOccurrenceFineIndices P S) :=
      selectedOccurrenceOuterShading_mass_le_bodyMassOn P Y S
    _ = containedMassOn F (selectedOccurrenceFineIndices P S) K :=
      (containedMassOn_eq_bodyMassOn_of_contained F
        (selectedOccurrenceFineIndices P S) K hcontained).symm

/-- Positive full induced outer mass and the canonical retention inequality
force the canonical selected outer shading to have positive mass. -/
theorem prop51SelectedOccurrences_outerShadingMass_ne_zero
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (hfull : (fullOccurrenceInducedShading P Y).shadingMass ≠ 0) :
    (selectedOccurrenceOuterShading P Y
      (prop51SelectedOccurrences P Y base M)).shadingMass ≠ 0 := by
  intro hselected
  apply hfull
  apply le_antisymm
  · have hretained :=
      prop51SelectedOccurrences_shadedMass_retention P Y base M
    rw [hselected, mul_zero] at hretained
    exact hretained
  · exact bot_le

/-- Ambient containment transports selected outer positivity to nonvanishing
of the literal selected `containedMassOn` denominator. -/
theorem prop51SelectedAmbientMass_ne_zero
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space)
    (hfull : (fullOccurrenceInducedShading P Y).shadingMass ≠ 0)
    (hcontained : ∀ i ∈ prop51SelectedFineIndices P Y base M,
      (F i : Set Space) ⊆ (K : Set Space)) :
    containedMassOn F (prop51SelectedFineIndices P Y base M) K ≠ 0 := by
  have houter :=
    prop51SelectedOccurrences_outerShadingMass_ne_zero P Y base M hfull
  have hle := selectedOccurrenceOuterShading_mass_le_containedMassOn
    P Y (prop51SelectedOccurrences P Y base M) K hcontained
  intro hzero
  apply houter
  apply le_antisymm
  · rw [hzero] at hle
    exact hle
  · exact bot_le

/-- Callback-free canonical source Frostman theorem.  The quotient
denominator required by the mass-ratio module is now proved nonzero from the
actual retained outer shading and fine-body containment. -/
theorem prop51SelectedOccurrences_source_fine_frostman_canonical
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) {C : ENNReal}
    (hglobal : IsFrostmanOn C F active K)
    (hfull : (fullOccurrenceInducedShading P Y).shadingMass ≠ 0)
    (hcontained : ∀ i ∈ prop51SelectedFineIndices P Y base M,
      (F i : Set Space) ⊆ (K : Set Space)) :
    IsFrostmanOn
      (C * prop51SelectedAmbientMassLoss P Y base M K) F
      (prop51SelectedFineIndices P Y base M) K := by
  exact prop51SelectedOccurrences_source_fine_frostman_of_nonzero
    P Y base M K hglobal
      (prop51SelectedAmbientMass_ne_zero P Y base M K hfull hcontained)

#print axioms occurrenceOuterShadedMass_le_blockMass
#print axioms selectedOccurrenceOuterShading_mass_le_bodyMassOn
#print axioms selectedOccurrenceOuterShading_mass_le_containedMassOn
#print axioms prop51SelectedOccurrences_outerShadingMass_ne_zero
#print axioms prop51SelectedAmbientMass_ne_zero
#print axioms prop51SelectedOccurrences_source_fine_frostman_canonical

end

end Family8Prop51SelectedOccurrenceAmbientMassPositiveV2

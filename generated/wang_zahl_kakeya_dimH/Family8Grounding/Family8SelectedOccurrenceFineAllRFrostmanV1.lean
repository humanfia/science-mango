import Family8Grounding.Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
import Mathlib.Tactic

/-!
# Source Frostman normalization on an arbitrary set of greedy occurrences

This module removes the canonical Proposition 5.1 selection hypotheses from
the block-density normalization argument.  An arbitrary literal occurrence
set `R` is enough: a common block-mass lower bound on `R` supplies the source
mass floor, and source Katz--Tao control then normalizes on the full union of
the corresponding fine fibres.

The conclusion is deliberately on `selectedOccurrenceFineIndices P R`, not
on a further fine-index subset.  Such a subset would require an additional
retained-mass inequality; set inclusion alone has the wrong direction for a
normalized Frostman restriction.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFineAllRFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- Source Katz--Tao control normalizes on the full fine union underlying an
arbitrary literal occurrence set.  The winning-body containment hypothesis
also supplies fine-body containment internally.  Finiteness of the total
winning-body volume is automatic from compactness and therefore is not a
public premise. -/
theorem selectedOccurrenceFine_isFrostmanOn_of_sourceKatzTao_and_blockMass_lower
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (ambient : ConvexBody Space) (A d : ENNReal)
    (hKT : IsKatzTao A F)
    (hblocks : forall k, k ∈ R ->
      ((blockAt F P k).body : Set Space) ⊆ (ambient : Set Space))
    (hblockMassLower : forall k, k ∈ R ->
      d * volume ((blockAt F P k).body : Set Space) <=
        blockMass F (blockAt F P k))
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hbodyVolume0 : prop51SubselectedBodyVolume P R ≠ 0) :
    IsFrostmanOn
      (A * volume (ambient : Set Space) * d⁻¹ *
        (prop51SubselectedBodyVolume P R)⁻¹)
      F (selectedOccurrenceFineIndices P R) ambient := by
  classical
  let selected := selectedOccurrenceFineIndices P R
  let bodyVolume := prop51SubselectedBodyVolume P R
  let C := A * volume (ambient : Set Space) * d⁻¹ * bodyVolume⁻¹
  have hcontained : forall i, i ∈ selected ->
      (F i : Set Space) ⊆ (ambient : Set Space) := by
    intro i hi
    change i ∈ R.biUnion (fun k => (blockAt F P k).fiber) at hi
    obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hi
    exact ((blockAt F P k).contained i hik).trans (hblocks k hk)
  have hbodyVolumeTop : bodyVolume ≠ ∞ := by
    dsimp only [bodyVolume]
    unfold prop51SubselectedBodyVolume
    apply ENNReal.sum_ne_top.2
    intro k _hk
    exact (blockAt F P k).body.isCompact.measure_lt_top.ne
  have hKTselected : IsKatzTao A (activeSubtypeFamily F selected) := by
    change IsKatzTao A (selectedCoarseFamily F selected)
    exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn (hKT.on selected)
  have hmass : d * bodyVolume <=
      containedMassOn F selected ambient := by
    rw [containedMassOn_eq_bodyMassOn_of_contained
      F selected ambient hcontained]
    dsimp only [bodyVolume, selected]
    unfold prop51SubselectedBodyVolume selectedOccurrenceFineIndices bodyMassOn
    rw [Finset.mul_sum]
    calc
      (∑ k ∈ R, d * volume ((blockAt F P k).body : Set Space)) <=
          ∑ k ∈ R, blockMass F (blockAt F P k) := by
        exact Finset.sum_le_sum fun k hk => hblockMassLower k hk
      _ = ∑ i ∈ R.biUnion (fun k => (blockAt F P k).fiber),
          volume (F i : Set Space) := by
        unfold blockMass
        exact (Finset.sum_biUnion
          (blockAt_fibers_pairwiseDisjoint F P R)).symm
  have hbase : A * volume (ambient : Set Space) <=
      C * containedMass (activeSubtypeFamily F selected) ambient := by
    rw [containedMass_activeSubtypeFamily]
    calc
      A * volume (ambient : Set Space) = C * (d * bodyVolume) := by
        dsimp only [C]
        symm
        calc
          (A * volume (ambient : Set Space) * d⁻¹ * bodyVolume⁻¹) *
              (d * bodyVolume) =
            A * volume (ambient : Set Space) * (d⁻¹ * d) *
              (bodyVolume⁻¹ * bodyVolume) := by ac_rfl
          _ = A * volume (ambient : Set Space) := by
            rw [ENNReal.inv_mul_cancel hd0 hdTop,
              ENNReal.inv_mul_cancel hbodyVolume0 hbodyVolumeTop]
            simp
      _ <= C * containedMassOn F selected ambient :=
        mul_le_mul' le_rfl hmass
  change IsFrostmanOn C F selected ambient
  apply (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    F selected ambient).2
  apply IsKatzTao.isFrostmanIn hKTselected
  · intro i
    exact hcontained i.1 i.2
  · exact hbase

#print axioms
  selectedOccurrenceFine_isFrostmanOn_of_sourceKatzTao_and_blockMass_lower

end

end Family8SelectedOccurrenceFineAllRFrostmanV1

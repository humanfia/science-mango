import Family8Grounding.Family8CoreHighPrefixFiberDensityBucketFineShadingV1
import Family8Grounding.Family8SelectedOccurrenceFineAllRFrostmanV1
import Mathlib.Tactic

/-!
# All-occurrence Frostman control on one joint fibre-density bucket

The joint first-hit payload already fixes one literal occurrence set `R` and
puts every member of `R` in the same density band.  This module turns exactly
those payload fields into source Frostman control on the full fine union
`selectedOccurrenceFineIndices P R`.

No canonical Proposition 5.1 selection is used, and the smaller retained
fine bucket is not normalized.  Nonzero total winning-body volume follows
from `R.Nonempty` and the positive lower endpoint forced by its nonempty
density band; no extra admissibility or scale-positivity hypothesis is needed.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoreHighPrefixFiberDensityBucketAllRFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8CoreHighPrefixFiberDensityBucketFineShadingV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFineAllRFrostmanV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The exact all-`R` Frostman adapter for witnesses extracted from the joint
fibre-density payload.  `hRnonempty` and `hband` are literal fields of that
payload.  The only geometric input left to the caller is containment of the
selected winning bodies in the chosen ambient body. -/
theorem coreHighFiberDensityBucketFine_isFrostmanOn_of_payload_fields
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (highThreshold base : ENNReal) (M : Nat) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
          CoreHighConcentrationOccurrence D P highThreshold q)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1) × Fin (M + 1))
    (ambient : ConvexBody Space) (sourceKT : ENNReal)
    (hKT : IsKatzTao sourceKT D.family.bodyFamily) :
    let R := coreHighFiberDensityOccurrenceBucket
      D P highThreshold base M selected hcover b
    let d := (2 : ENNReal) ^ b.2.1 * base
    R.Nonempty ->
    (forall q, q ∈ R ->
      InENNRealDyadicBand base b.2.1
        (blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q))) ->
    (forall q, q ∈ R ->
      ((blockAt D.family.bodyFamily P q).body : Set Space) ⊆
        (ambient : Set Space)) ->
    IsFrostmanOn
      (sourceKT * volume (ambient : Set Space) * d⁻¹ *
        (prop51SubselectedBodyVolume P R)⁻¹)
      D.family.bodyFamily (selectedOccurrenceFineIndices P R) ambient := by
  dsimp only
  intro hRnonempty hband hblocks
  let R := coreHighFiberDensityOccurrenceBucket
    D P highThreshold base M selected hcover b
  let d := (2 : ENNReal) ^ b.2.1 * base
  have hRnonempty' : R.Nonempty := by
    simpa only [R] using hRnonempty
  have hband' : forall q, q ∈ R ->
      InENNRealDyadicBand base b.2.1
        (blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q)) := by
    simpa only [R] using hband
  have hblocks' : forall q, q ∈ R ->
      ((blockAt D.family.bodyFamily P q).body : Set Space) ⊆
        (ambient : Set Space) := by
    simpa only [R] using hblocks
  have hd0 : d ≠ 0 := by
    intro hd
    obtain ⟨q, hq⟩ := hRnonempty'
    have hupper := (hband' q hq).2
    have hupperEq :
        (2 : ENNReal) ^ (b.2.1 + 1) * base = 2 * d := by
      dsimp only [d]
      rw [pow_succ]
      ac_rfl
    rw [hupperEq, hd, mul_zero] at hupper
    exact (not_lt_of_ge bot_le) hupper
  have hdTop : d ≠ ∞ := by
    intro hd
    obtain ⟨q, hq⟩ := hRnonempty'
    have hlower : d <= blockDensity D.family.bodyFamily
        (blockAt D.family.bodyFamily P q) := by
      simpa only [d] using (hband' q hq).1
    have hdensityTop :
        blockDensity D.family.bodyFamily
            (blockAt D.family.bodyFamily P q) = ∞ :=
      top_unique (by simpa only [hd] using hlower)
    have hupper := (hband' q hq).2
    rw [hdensityTop] at hupper
    exact (not_lt_of_ge le_top) hupper
  have hblockMassLower : forall q, q ∈ R ->
      d * volume ((blockAt D.family.bodyFamily P q).body : Set Space) <=
        blockMass D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) := by
    intro q hq
    have hlower : d <= blockDensity D.family.bodyFamily
        (blockAt D.family.bodyFamily P q) := by
      simpa only [d] using (hband' q hq).1
    exact lower_mul_volume_le_blockMass D.family.bodyFamily
      (blockAt D.family.bodyFamily P q) d hlower
  obtain ⟨q, hq⟩ := hRnonempty'
  have hqDensity0 :
      blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) ≠ 0 := by
    intro hqDensityZero
    have hlower : d <= blockDensity D.family.bodyFamily
        (blockAt D.family.bodyFamily P q) := by
      simpa only [d] using (hband' q hq).1
    rw [hqDensityZero] at hlower
    exact hd0 (nonpos_iff_eq_zero.mp hlower)
  have hqBody0 :
      volume ((blockAt D.family.bodyFamily P q).body : Set Space) ≠ 0 := by
    intro hbody0
    have hmass0 :
        blockMass D.family.bodyFamily
            (blockAt D.family.bodyFamily P q) = 0 := by
      unfold blockMass
      apply Finset.sum_eq_zero
      intro i hi
      exact nonpos_iff_eq_zero.mp
        ((measure_mono
          ((blockAt D.family.bodyFamily P q).contained i hi)).trans_eq hbody0)
    apply hqDensity0
    unfold blockDensity
    rw [hmass0]
    simp
  have hbodyVolume0 : prop51SubselectedBodyVolume P R ≠ 0 := by
    have hsingle :
        volume ((blockAt D.family.bodyFamily P q).body : Set Space) <=
          prop51SubselectedBodyVolume P R := by
      unfold prop51SubselectedBodyVolume
      exact Finset.single_le_sum
        (f := fun k =>
          volume ((blockAt D.family.bodyFamily P k).body : Set Space))
        (fun _ _ => bot_le) hq
    exact ne_of_gt ((bot_lt_iff_ne_bot.mpr hqBody0).trans_le hsingle)
  simpa only [R, d] using
    (selectedOccurrenceFine_isFrostmanOn_of_sourceKatzTao_and_blockMass_lower
      P R ambient sourceKT d hKT hblocks' hblockMassLower
        hd0 hdTop hbodyVolume0)

#print axioms
  coreHighFiberDensityBucketFine_isFrostmanOn_of_payload_fields

end

end Family8CoreHighPrefixFiberDensityBucketAllRFrostmanV1

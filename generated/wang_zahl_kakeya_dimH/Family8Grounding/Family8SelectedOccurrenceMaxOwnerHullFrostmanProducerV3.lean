import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullAggregateV2
import Family8Grounding.Family8PlankLongTubeFrostmanTransferV3
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullUniqueOwnerV2
import Family8Grounding.Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Submission.Kakeya.ConvexFactoring.JointTubeFactoring
import Mathlib.Tactic

/-!
# Explicit Frostman transfer to genuine max-owner occurrence hulls

This successor turns source fine Frostman on the literal selected greedy
fibres into Frostman on the actual max-owner hull family.  There are two
geometric losses and both are displayed:

* `16 * fibreCardCap` for keeping one injective max-shaded witness tube per
  occurrence;
* the exact certified-plank-volume / fine-tube-volume cover loss for enlarging
  that witness to its genuine parent-specific max-owner hull.

No `refined_frostman` conclusion is accepted as a premise.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8PlankLongTubeFrostmanTransferV3
open Family6CanonicalFrostmanConstantCoreV1
open Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerHullUniqueOwnerV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho a b : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- The literal max-shaded fine tube, indexed by the selected occurrence
type used by the max-owner hull family. -/
abbrev selectedOccurrenceMaxWitnessFamily
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    ConvexFamily {q // q ∈ selectedOccurrenceIndices P R} :=
  fun q ↦ fine.bodyFamily (occurrenceMaxShadedWitness C P Y
    (selectedOccurrencePosition C R q))

/-- Every selected max witness belongs to the literal union of the selected
greedy fibres. -/
theorem selectedOccurrenceMaxWitness_mem_selectedFine
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    occurrenceMaxShadedWitness C P Y (selectedOccurrencePosition C R q) ∈
      selectedOccurrenceFineIndices P R := by
  apply Finset.mem_biUnion.mpr
  exact ⟨selectedOccurrencePosition C R q,
    selectedOccurrencePosition_mem C R q,
    occurrenceMaxShadedWitness_mem C P Y _⟩

/-- Max witnesses from distinct selected occurrences are distinct.  This is
the point where literal greedy-fibre disjointness, rather than a cardinality
proxy, is used. -/
theorem selectedOccurrenceMaxWitness_injective
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    Function.Injective (fun q : {q // q ∈ selectedOccurrenceIndices P R} ↦
      occurrenceMaxShadedWitness C P Y
        (selectedOccurrencePosition C R q)) := by
  intro q r hqr
  let k := selectedOccurrencePosition C R q
  let l := selectedOccurrencePosition C R r
  have hkR : k ∈ R := selectedOccurrencePosition_mem C R q
  have hlR : l ∈ R := selectedOccurrencePosition_mem C R r
  have hkw : occurrenceMaxShadedWitness C P Y k ∈
      (blockAt fine.bodyFamily P k).fiber :=
    occurrenceMaxShadedWitness_mem C P Y k
  have hqr' : occurrenceMaxShadedWitness C P Y k =
      occurrenceMaxShadedWitness C P Y l := by
    simpa only [k, l] using hqr
  have hlw : occurrenceMaxShadedWitness C P Y k ∈
      (blockAt fine.bodyFamily P l).fiber := by
    rw [hqr']
    exact occurrenceMaxShadedWitness_mem C P Y l
  have hkl : k = l := by
    by_contra hne
    have hdisj := blockAt_fibers_pairwiseDisjoint fine.bodyFamily P R
      hkR hlR hne
    exact (Finset.disjoint_left.mp hdisj hkw hlw)
  apply Subtype.ext
  calc
    q.1 = some k := (some_selectedOccurrencePosition_eq C R q).symm
    _ = some l := congrArg some hkl
    _ = r.1 := some_selectedOccurrencePosition_eq C R r

/-- An injectively indexed subfamily has no more contained mass than any
ambient finite index set containing its image. -/
theorem containedMass_mappedFamily_le_containedMassOn
    {alpha beta : Type} [Fintype alpha] [Fintype beta] [DecidableEq beta]
    (F : ConvexFamily beta) (f : alpha → beta) (hf : Function.Injective f)
    (s : Finset beta) (hfs : ∀ i, f i ∈ s) (K : ConvexBody Space) :
    containedMass (fun i ↦ F (f i)) K ≤ containedMassOn F s K := by
  classical
  let emb : alpha ↪ beta := ⟨f, hf⟩
  have hsubset :
      (containedIndices (fun i ↦ F (f i)) K).map emb ⊆
        s ∩ containedIndices F K := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    rw [Finset.mem_inter, mem_containedIndices]
    refine ⟨hfs i, ?_⟩
    exact (mem_containedIndices (fun i ↦ F (f i)) K i).mp hi
  have hsum :
      (∑ j ∈ (containedIndices (fun i ↦ F (f i)) K).map emb,
          volume (F j : Set Space)) ≤
        ∑ j ∈ s ∩ containedIndices F K, volume (F j : Set Space) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => bot_le)
  calc
    containedMass (fun i ↦ F (f i)) K =
        ∑ j ∈ (containedIndices (fun i ↦ F (f i)) K).map emb,
          volume (F j : Set Space) := by
      unfold containedMass
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ j ∈ s ∩ containedIndices F K,
          volume (F j : Set Space) := hsum
    _ = containedMassOn F s K := by
      unfold containedMassOn
      apply Finset.sum_congr
      · ext i
        simp
      · intro i hi
        rfl

/-- Applied to actual max witnesses, the numerator in every Frostman test is
bounded by the selected source-fine numerator. -/
theorem containedMass_maxWitness_le_selectedFine
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (K : ConvexBody Space) :
    containedMass (selectedOccurrenceMaxWitnessFamily C Y R) K ≤
      containedMassOn fine.bodyFamily
        (selectedOccurrenceFineIndices P R) K := by
  exact containedMass_mappedFamily_le_containedMassOn fine.bodyFamily
    (fun q ↦ occurrenceMaxShadedWitness C P Y
      (selectedOccurrencePosition C R q))
    (selectedOccurrenceMaxWitness_injective C Y R)
    (selectedOccurrenceFineIndices P R)
    (selectedOccurrenceMaxWitness_mem_selectedFine C Y R) K


/-- The selected fine index set contains at most `M` indices per retained
occurrence. -/
theorem selectedOccurrenceFineIndices_card_le_mul
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M) :
    (selectedOccurrenceFineIndices P R).card ≤ R.card * M := by
  unfold selectedOccurrenceFineIndices
  calc
    (R.biUnion fun k ↦ (blockAt fine.bodyFamily P k).fiber).card ≤
        ∑ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ R, M := by
      exact Finset.sum_le_sum fun k hk ↦ hcard k hk
    _ = R.card * M := by simp

/-- Every literal max-witness tube lies in the source Frostman ambient. -/
theorem selectedOccurrenceMaxWitness_subset_ambient
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space) {CF : ENNReal}
    (hsource : IsFrostmanOn CF fine.bodyFamily
      (selectedOccurrenceFineIndices P R) ambient)
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    (selectedOccurrenceMaxWitnessFamily C Y R q : Set Space) ⊆
      (ambient : Set Space) := by
  exact hsource.1 _ (selectedOccurrenceMaxWitness_mem_selectedFine C Y R q)

/-- The selected source fine ambient mass is at most
`16 * fibreCardCap` times the ambient mass of the injective one-witness
family. -/
theorem selectedFine_ambientMass_le_sixteen_cardCap_mul_maxWitness
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M)
    (ambient : ConvexBody Space) {CF : ENNReal}
    (hsource : IsFrostmanOn CF fine.bodyFamily
      (selectedOccurrenceFineIndices P R) ambient)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    containedMassOn fine.bodyFamily (selectedOccurrenceFineIndices P R)
        ambient ≤
      (16 * (M : ENNReal)) *
        containedMass (selectedOccurrenceMaxWitnessFamily C Y R) ambient := by
  let s := selectedOccurrenceFineIndices P R
  let W := selectedOccurrenceMaxWitnessFamily C Y R
  have hsContained : ∀ i ∈ s,
      (fine.bodyFamily i : Set Space) ⊆ (ambient : Set Space) := hsource.1
  have hsourceUpper : containedMassOn fine.bodyFamily s ambient ≤
      (s.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) :=
    containedMassOn_uniformTube_le_activeCard_mul_eight_sq s ambient
      hsContained hdeltaHalf
  have hcardNat : s.card ≤ R.card * M :=
    selectedOccurrenceFineIndices_card_le_mul C R M hcard
  have hcardENN : (s.card : ENNReal) ≤ ((R.card * M : Nat) : ENNReal) := by
    exact_mod_cast hcardNat
  have hWContained : ∀ q, (W q : Set Space) ⊆ (ambient : Set Space) :=
    selectedOccurrenceMaxWitness_subset_ambient C Y R ambient hsource
  have hqcard : (selectedOccurrenceIndices P R).card = R.card := by
    rw [← Fintype.card_coe]
    simpa only [selectedOccurrenceOuterCount] using
      (selectedOccurrenceOuterCount_eq_card P R)
  have hWLower : (R.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) ≤
      containedMass W ambient := by
    rw [containedMass_eq_familyVolume_of_contained W ambient hWContained]
    unfold familyVolume
    calc
      (R.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) =
          ∑ _q : {q // q ∈ selectedOccurrenceIndices P R},
            ((delta : ENNReal) ^ 2 / 2) := by simp [hqcard]
      _ ≤ ∑ q : {q // q ∈ selectedOccurrenceIndices P R},
          volume (W q : Set Space) := by
        apply Finset.sum_le_sum
        intro q _hq
        simpa [W, selectedOccurrenceMaxWitnessFamily,
          UniformTubeFamily.bodyFamily, Tube.coe_body] using
          (fine.tubes (occurrenceMaxShadedWitness C P Y
            (selectedOccurrencePosition C R q))).half_sq_le_volume_of_le_half
              hdeltaHalf
  have htwo : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hsixteen : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
    calc
      (16 : ENNReal) * (2 : ENNReal)⁻¹ =
          (8 * 2) * (2 : ENNReal)⁻¹ := by norm_num
      _ = 8 * (2 * (2 : ENNReal)⁻¹) := by ring
      _ = 8 := by rw [htwo]; simp
  have hnumeric :
      (((R.card * M : Nat) : ENNReal) *
          (8 * (delta : ENNReal) ^ 2)) =
        (16 * (M : ENNReal)) *
          ((R.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2)) := by
    have hcast : (((R.card * M : Nat) : ENNReal)) =
        (R.card : ENNReal) * (M : ENNReal) := by norm_num
    rw [hcast, div_eq_mul_inv]
    calc
      ((R.card : ENNReal) * (M : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2) =
          (R.card : ENNReal) * (M : ENNReal) *
            (delta : ENNReal) ^ 2 * 8 := by ring
      _ = (R.card : ENNReal) * (M : ENNReal) *
            (delta : ENNReal) ^ 2 * (16 * (2 : ENNReal)⁻¹) := by
          rw [hsixteen]
      _ = (16 * (M : ENNReal)) *
          ((R.card : ENNReal) *
            ((delta : ENNReal) ^ 2 * (2 : ENNReal)⁻¹)) := by ring
  calc
    containedMassOn fine.bodyFamily (selectedOccurrenceFineIndices P R)
        ambient = containedMassOn fine.bodyFamily s ambient := rfl
    _ ≤ (s.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) := hsourceUpper
    _ ≤ (((R.card * M : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2)) := by gcongr
    _ = (16 * (M : ENNReal)) *
        ((R.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2)) := hnumeric
    _ ≤ (16 * (M : ENNReal)) * containedMass W ambient := by
      exact mul_le_mul' le_rfl hWLower

/-- Source fine Frostman on the selected greedy fibres transfers to the
literal one-max-witness family with the explicit uniform-tube/cardinality
loss. -/
theorem selectedOccurrenceMaxWitness_isFrostmanIn
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M)
    (ambient : ConvexBody Space) {CF : ENNReal}
    (hsource : IsFrostmanOn CF fine.bodyFamily
      (selectedOccurrenceFineIndices P R) ambient)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    IsFrostmanIn (CF * (16 * (M : ENNReal)))
      (selectedOccurrenceMaxWitnessFamily C Y R) ambient := by
  let W := selectedOccurrenceMaxWitnessFamily C Y R
  refine ⟨selectedOccurrenceMaxWitness_subset_ambient C Y R ambient hsource,
    ?_⟩
  intro K hK
  calc
    containedMass W K * volume (ambient : Set Space) ≤
        containedMassOn fine.bodyFamily (selectedOccurrenceFineIndices P R) K *
          volume (ambient : Set Space) := by
      exact mul_le_mul'
        (containedMass_maxWitness_le_selectedFine C Y R K) le_rfl
    _ ≤ CF * containedMassOn fine.bodyFamily
          (selectedOccurrenceFineIndices P R) ambient *
        volume (K : Set Space) := hsource.2 K hK
    _ ≤ CF * ((16 * (M : ENNReal)) * containedMass W ambient) *
        volume (K : Set Space) := by
      exact mul_le_mul' (mul_le_mul' le_rfl
        (selectedFine_ambientMass_le_sixteen_cardCap_mul_maxWitness
          C Y R M hcard ambient hsource hdeltaHalf)) le_rfl
    _ = (CF * (16 * (M : ENNReal))) * containedMass W ambient *
        volume (K : Set Space) := by ac_rfl

/-- Exact memberwise body-cover loss from a fine witness tube to a certified
`a x b x 1` max-owner hull. -/
def maxOwnerHullWitnessCoverLoss (delta a b : NNReal) : ENNReal :=
  ((a : ENNReal) * (b : ENNReal)) / ((delta : ENNReal) ^ 2 / 2)

theorem maxOwnerHull_volume_le_coverLoss_mul_witness
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (comparisonConstant : NNReal)
    (all_isPlank : ∀ q, IsPlank comparisonConstant a b
      (selectedOccurrenceMaxOwnerHullFamily C P Y R q))
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    volume (selectedOccurrenceMaxOwnerHullFamily C P Y R q : Set Space) ≤
      maxOwnerHullWitnessCoverLoss delta a b *
        volume (selectedOccurrenceMaxWitnessFamily C Y R q : Set Space) := by
  have hdelta0 : (delta : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hden0 : ((delta : ENNReal) ^ 2 / 2) ≠ 0 := by
    simp [hdelta0]
  have hdenTop : ((delta : ENNReal) ^ 2 / 2) ≠ ∞ := by
    finiteness
  calc
    volume (selectedOccurrenceMaxOwnerHullFamily C P Y R q : Set Space) ≤
        (a : ENNReal) * (b : ENNReal) :=
      (all_isPlank q).volume_upper_bound
    _ = maxOwnerHullWitnessCoverLoss delta a b *
        ((delta : ENNReal) ^ 2 / 2) := by
      exact (ENNReal.div_mul_cancel hden0 hdenTop).symm
    _ ≤ maxOwnerHullWitnessCoverLoss delta a b *
        volume (selectedOccurrenceMaxWitnessFamily C Y R q : Set Space) := by
      gcongr
      simpa [selectedOccurrenceMaxWitnessFamily,
        UniformTubeFamily.bodyFamily, Tube.coe_body] using
        (fine.tubes (occurrenceMaxShadedWitness C P Y
          (selectedOccurrencePosition C R q))).half_sq_le_volume_of_le_half
            hdeltaHalf

/-- Callback-free refined Frostman producer on the exact genuine max-owner
hull family. -/
theorem selectedOccurrenceMaxOwnerHull_isFrostmanIn
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M)
    (ambient : ConvexBody Space) {CF : ENNReal}
    (hsource : IsFrostmanOn CF fine.bodyFamily
      (selectedOccurrenceFineIndices P R) ambient)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (comparisonConstant : NNReal)
    (all_isPlank : ∀ q, IsPlank comparisonConstant a b
      (selectedOccurrenceMaxOwnerHullFamily C P Y R q))
    (hhullAmbient : ∀ q,
      (selectedOccurrenceMaxOwnerHullFamily C P Y R q : Set Space) ⊆
        (ambient : Set Space)) :
    IsFrostmanIn
      (maxOwnerHullWitnessCoverLoss delta a b *
        (CF * (16 * (M : ENNReal))))
      (selectedOccurrenceMaxOwnerHullFamily C P Y R) ambient := by
  exact isFrostmanIn_bodyCover
    (selectedOccurrenceMaxWitness_isFrostmanIn C Y R M hcard ambient hsource
      hdeltaHalf)
    (selectedOccurrenceMaxShadedWitness_carrier_subset_hull C Y R)
    (maxOwnerHull_volume_le_coverLoss_mul_witness C Y R comparisonConstant
      all_isPlank hdelta hdeltaHalf)
    hhullAmbient

#print axioms selectedOccurrenceFineIndices_card_le_mul
#print axioms selectedFine_ambientMass_le_sixteen_cardCap_mul_maxWitness
#print axioms selectedOccurrenceMaxWitness_isFrostmanIn
#print axioms maxOwnerHull_volume_le_coverLoss_mul_witness
#print axioms selectedOccurrenceMaxOwnerHull_isFrostmanIn

end
end Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3

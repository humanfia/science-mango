import Family8Grounding.Family8PlankThickControlOwnerFiberLogBucketV2
import Family8Grounding.Family8PlankThickControlRetainedOwnerFamilyV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerHeavyMassSelectionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Heavy owner rows inside the retained logarithmic bucket

Inside one literal owner-cardinality bucket, retain the owners whose
owner-fibre shaded mass is at least half the average bucket mass.  The light
rows carry at most half of the total bucket mass.  Hence the heavy rows retain
the actual restricted plank mass with loss two, and every heavy row has the
same explicit mass floor.  No conclusion or callback is assumed.
-/

/-- Half the average owner-fibre mass in the selected logarithmic bucket. -/
def retainedOwnerHalfAverageFloor
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) : ENNReal :=
  (∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s) /
    (2 * ((selectedOwnerLogBucket C q).card : ENNReal))

/-- Owners in the retained bucket whose literal fibre mass is at least the
half-average floor. -/
def heavyRetainedOwners
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) : Finset iota :=
  (selectedOwnerLogBucket C q).filter fun s ↦
    retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s

/-- Total literal owner-fibre mass on the heavy rows. -/
def heavyRetainedOwnerMass
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) : ENNReal :=
  ∑ s ∈ heavyRetainedOwners C q, ownerFiberMass C s

theorem ownerFiberMass_ne_top
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s : iota) :
    ownerFiberMass C s ≠ ∞ := by
  unfold ownerFiberMass
  apply ENNReal.sum_ne_top.2
  intro i _hi
  exact (shadingPiece_volume_lt_top D.shading i).ne

theorem selectedOwnerLogBucket_mass_ne_top
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s) ≠ ∞ := by
  apply ENNReal.sum_ne_top.2
  intro s _hs
  exact ownerFiberMass_ne_top C s

theorem heavyRetainedOwnerMass_ne_top
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    heavyRetainedOwnerMass C q ≠ ∞ := by
  unfold heavyRetainedOwnerMass
  apply ENNReal.sum_ne_top.2
  intro s _hs
  exact ownerFiberMass_ne_top C s

@[simp] theorem mem_heavyRetainedOwners
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) (s : iota) :
    s ∈ heavyRetainedOwners C q ↔
      s ∈ selectedOwnerLogBucket C q ∧
        retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s := by
  simp [heavyRetainedOwners]

/-- Every heavy owner has the advertised common rowwise mass floor. -/
theorem retainedOwnerHalfAverageFloor_le_ownerFiberMass
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {s : iota} (hs : s ∈ heavyRetainedOwners C q) :
    retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s :=
  (mem_heavyRetainedOwners C q s).1 hs |>.2

/-- Finite half-average selection: the heavy rows retain at least half of
the complete bucket mass. -/
theorem selectedOwnerLogBucket_mass_le_two_mul_heavyRetainedOwnerMass
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s) ≤
      2 * heavyRetainedOwnerMass C q := by
  classical
  let S := selectedOwnerLogBucket C q
  let weight : iota → ENNReal := ownerFiberMass C
  let total : ENNReal := ∑ s ∈ S, weight s
  let floor : ENNReal := total / (2 * (S.card : ENNReal))
  let heavy : Finset iota := S.filter fun s ↦ floor ≤ weight s
  let light : Finset iota := S.filter fun s ↦ ¬ floor ≤ weight s
  by_cases hS : S.Nonempty
  · have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
    have hcardReal : (0 : Real) < (S.card : Real) := by
      exact_mod_cast hcardNat
    have hcardENN0 : (S.card : ENNReal) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hcardNat)
    have hden0 : (2 * (S.card : ENNReal)) ≠ 0 :=
      mul_ne_zero (by norm_num) hcardENN0
    have htotalTop : total ≠ ∞ := by
      dsimp only [total, weight, S]
      exact selectedOwnerLogBucket_mass_ne_top C q
    have hfloorTop : floor ≠ ∞ := by
      dsimp only [floor]
      exact ENNReal.div_ne_top htotalTop hden0
    have hheavyTop : (∑ s ∈ heavy, weight s) ≠ ∞ := by
      apply ENNReal.sum_ne_top.2
      intro s hs
      apply ownerFiberMass_ne_top C s
    have hrightTop : 2 * (∑ s ∈ heavy, weight s) ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) hheavyTop
    have htotalReal :
        total.toReal = ∑ s ∈ S, (weight s).toReal := by
      dsimp only [total]
      exact ENNReal.toReal_sum fun s hs ↦ by
        dsimp only [weight]
        exact ownerFiberMass_ne_top C s
    have hheavyReal :
        (∑ s ∈ heavy, weight s).toReal =
          ∑ s ∈ heavy, (weight s).toReal := by
      exact ENNReal.toReal_sum fun s hs ↦ by
        dsimp only [weight]
        exact ownerFiberMass_ne_top C s
    have hfloorReal :
        floor.toReal = total.toReal / (2 * (S.card : Real)) := by
      dsimp only [floor]
      simp only [ENNReal.toReal_div, ENNReal.toReal_mul,
        ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
    have hlightTerm : ∀ s ∈ light, (weight s).toReal ≤ floor.toReal := by
      intro s hs
      have hmem := Finset.mem_filter.mp hs
      have hlt : weight s < floor := lt_of_not_ge hmem.2
      exact le_of_lt
        ((ENNReal.toReal_lt_toReal
          (by dsimp only [weight]; exact ownerFiberMass_ne_top C s)
          hfloorTop).2 hlt)
    have hlightReal :
        (∑ s ∈ light, (weight s).toReal) ≤
          (light.card : Real) * floor.toReal := by
      calc
        (∑ s ∈ light, (weight s).toReal) ≤
            ∑ _s ∈ light, floor.toReal :=
          Finset.sum_le_sum fun s hs ↦ hlightTerm s hs
        _ = (light.card : Real) * floor.toReal := by simp
    have hlightCard : (light.card : Real) ≤ (S.card : Real) := by
      dsimp only [light]
      exact_mod_cast
        (Finset.card_le_card (Finset.filter_subset
          (fun s ↦ ¬ floor ≤ weight s) S))
    have hlightReal' :
        (∑ s ∈ light, (weight s).toReal) ≤
          (S.card : Real) * floor.toReal :=
      hlightReal.trans
        (mul_le_mul_of_nonneg_right hlightCard ENNReal.toReal_nonneg)
    have hcancel :
        (S.card : Real) *
            (total.toReal / (2 * (S.card : Real))) =
          total.toReal / 2 := by
      field_simp
    have hlightHalf :
        (∑ s ∈ light, (weight s).toReal) ≤ total.toReal / 2 := by
      rw [hfloorReal, hcancel] at hlightReal'
      exact hlightReal'
    have hpartition :
        (∑ s ∈ heavy, (weight s).toReal) +
            (∑ s ∈ light, (weight s).toReal) =
          ∑ s ∈ S, (weight s).toReal := by
      dsimp only [heavy, light]
      simpa using
        (Finset.sum_filter_add_sum_filter_not S
          (fun s ↦ floor ≤ weight s) (fun s ↦ (weight s).toReal))
    have hfinalReal :
        total.toReal ≤ 2 * (∑ s ∈ heavy, (weight s).toReal) := by
      rw [htotalReal]
      linarith
    have hfinal : total ≤ 2 * (∑ s ∈ heavy, weight s) := by
      apply (ENNReal.toReal_le_toReal htotalTop hrightTop).mp
      rw [ENNReal.toReal_mul]
      norm_num
      simpa only [hheavyReal] using hfinalReal
    change total ≤ 2 * (∑ s ∈ heavy, weight s)
    exact hfinal
  · have hSEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, hSEmpty, heavyRetainedOwnerMass, heavyRetainedOwners,
      retainedOwnerHalfAverageFloor]

/-- Actual retained plank mass is retained by the heavy owner rows with
exact loss two. -/
theorem retainedOwnerPlankFamily_mass_le_two_mul_heavyRetainedOwnerMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (retainedOwnerPlankFamily D C q).shading.shadingMass ≤
      2 * heavyRetainedOwnerMass C q := by
  rw [retainedOwnerPlankFamily_shadingMass]
  exact selectedOwnerLogBucket_mass_le_two_mul_heavyRetainedOwnerMass C q

/-- Rowwise form with the actual retained plank mass in the numerator. -/
theorem retainedOwnerPlankFamily_halfAverage_le_ownerFiberMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {s : iota} (hs : s ∈ heavyRetainedOwners C q) :
    (retainedOwnerPlankFamily D C q).shading.shadingMass /
        (2 * ((selectedOwnerLogBucket C q).card : ENNReal)) ≤
      ownerFiberMass C s := by
  rw [retainedOwnerPlankFamily_shadingMass]
  exact retainedOwnerHalfAverageFloor_le_ownerFiberMass C q hs

theorem selectedOwnerLogBucket_nonempty_of_retainedMass_pos
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : 0 < (retainedOwnerPlankFamily D C q).shading.shadingMass) :
    (selectedOwnerLogBucket C q).Nonempty := by
  by_contra hempty
  have hS : selectedOwnerLogBucket C q = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hzero :
      (retainedOwnerPlankFamily D C q).shading.shadingMass = 0 := by
    rw [retainedOwnerPlankFamily_shadingMass, hS]
    simp
  exact hmass.ne' hzero

theorem heavyRetainedOwners_nonempty_of_retainedMass_pos
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : 0 < (retainedOwnerPlankFamily D C q).shading.shadingMass) :
    (heavyRetainedOwners C q).Nonempty := by
  by_contra hempty
  have hheavy : heavyRetainedOwners C q = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hbound :=
    retainedOwnerPlankFamily_mass_le_two_mul_heavyRetainedOwnerMass D C q
  have hzero :
      (retainedOwnerPlankFamily D C q).shading.shadingMass = 0 := by
    apply le_antisymm
    · simpa [heavyRetainedOwnerMass, hheavy] using hbound
    · exact bot_le
  exact hmass.ne' hzero

theorem selectedOwnerLogBucket_and_heavy_nonempty_of_retainedMass_pos
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : 0 < (retainedOwnerPlankFamily D C q).shading.shadingMass) :
    (selectedOwnerLogBucket C q).Nonempty ∧
      (heavyRetainedOwners C q).Nonempty :=
  ⟨selectedOwnerLogBucket_nonempty_of_retainedMass_pos D C q hmass,
    heavyRetainedOwners_nonempty_of_retainedMass_pos D C q hmass⟩

#print axioms ownerFiberMass_ne_top
#print axioms mem_heavyRetainedOwners
#print axioms retainedOwnerHalfAverageFloor_le_ownerFiberMass
#print axioms selectedOwnerLogBucket_mass_le_two_mul_heavyRetainedOwnerMass
#print axioms retainedOwnerPlankFamily_mass_le_two_mul_heavyRetainedOwnerMass
#print axioms retainedOwnerPlankFamily_halfAverage_le_ownerFiberMass
#print axioms selectedOwnerLogBucket_nonempty_of_retainedMass_pos
#print axioms heavyRetainedOwners_nonempty_of_retainedMass_pos
#print axioms
  selectedOwnerLogBucket_and_heavy_nonempty_of_retainedMass_pos

end
end Family8PlankRetainedOwnerHeavyMassSelectionV3

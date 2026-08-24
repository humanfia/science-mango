import Submission.Kakeya.ConvexFactoring.TubeSpecificLocalGrowth
import Submission.Kakeya.Uniformity.Pigeonhole
import Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open StatisticLevelRestriction

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace BallwiseLocalVolumeUniformization

/-! A packing is taken at radius `rho / 3`.  Its standard `3r` cover is
therefore a cover by the desired radius-`rho` balls. -/

theorem three_mul_div_three (rho : ℝ≥0) : 3 * (rho / 3) = rho := by
  calc
    3 * (rho / 3) = rho * (3 / 3) := by ring
    _ = rho := by norm_num

theorem PackingCertificate.subset_iUnion_rhoBalls
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho) :
    A ⊆ ⋃ x ∈ C.centers, Metric.ball x (rho : ℝ) := by
  simpa [three_mul_div_three] using
    C.subset_iUnion_largeBalls (div_pos hrho (by norm_num : (0 : ℝ≥0) < 3))

/-! Enumerating the finite centers lets us use `Nat.find` to choose the first
covering ball.  The fallback `univ` at all indices after `centers.card` makes
the owner total; it is never used on the packed set. -/

def packingCenterAt {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (j : ℕ) : Space :=
  if hj : j < C.centers.card then
    ((C.centers.equivFin).symm ⟨j, hj⟩ : C.centers).1
  else 0

def packingCoverPiece {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (j : ℕ) : Set Space :=
  if j < C.centers.card then
    Metric.ball (packingCenterAt C j) (rho : ℝ)
  else Set.univ

theorem measurableSet_packingCoverPiece
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (j : ℕ) :
    MeasurableSet (packingCoverPiece C j) := by
  unfold packingCoverPiece
  split_ifs
  · exact measurableSet_ball
  · exact MeasurableSet.univ

theorem exists_mem_packingCoverPiece
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (x : Space) :
    ∃ j, x ∈ packingCoverPiece C j := by
  refine ⟨C.centers.card, ?_⟩
  simp [packingCoverPiece]

def packingOwnerIndex {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (x : Space) : ℕ :=
  Nat.find (exists_mem_packingCoverPiece C x)

theorem measurable_packingOwnerIndex
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) :
    Measurable (packingOwnerIndex C) := by
  unfold packingOwnerIndex
  exact measurable_find (exists_mem_packingCoverPiece C)
    (measurableSet_packingCoverPiece C)

theorem exists_centerIndex_ball
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    {x : Space} (hx : x ∈ A) :
    ∃ j, j < C.centers.card ∧
      x ∈ Metric.ball (packingCenterAt C j) (rho : ℝ) := by
  have hxcover := PackingCertificate.subset_iUnion_rhoBalls C hrho hx
  obtain ⟨c, hc, hxc⟩ := by simpa only [mem_iUnion] using hxcover
  let c' : C.centers := ⟨c, hc⟩
  let j : Fin C.centers.card := C.centers.equivFin c'
  refine ⟨j.1, j.2, ?_⟩
  have hcenter : packingCenterAt C j.1 = c := by
    simp [packingCenterAt, j, c']
  simpa [hcenter] using hxc

theorem packingOwnerIndex_lt_card
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    {x : Space} (hx : x ∈ A) :
    packingOwnerIndex C x < C.centers.card := by
  obtain ⟨j, hj, hxj⟩ := exists_centerIndex_ball C hrho hx
  have hjpiece : x ∈ packingCoverPiece C j := by
    simp [packingCoverPiece, hj, hxj]
  exact lt_of_le_of_lt
    (Nat.find_min' (exists_mem_packingCoverPiece C x) hjpiece) hj

theorem mem_owner_ball
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    {x : Space} (hx : x ∈ A) :
    x ∈ Metric.ball
      (packingCenterAt C (packingOwnerIndex C x)) (rho : ℝ) := by
  have howner := Nat.find_spec (exists_mem_packingCoverPiece C x)
  change x ∈ packingCoverPiece C (packingOwnerIndex C x) at howner
  have hlt := packingOwnerIndex_lt_card C hrho hx
  simp only [packingCoverPiece, hlt, if_pos] at howner
  exact howner

/-! The actual packing cells are the intersections with the standard
`disjointed` cover.  This is the finite replacement for a false statement at
every continuously varying ball center. -/

def packingCell {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (j : ℕ) : Set Space :=
  A ∩ disjointed (packingCoverPiece C) j

theorem measurableSet_packingCell
    {A : Set Space} (hA : MeasurableSet A) {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (j : ℕ) :
    MeasurableSet (packingCell C j) :=
  hA.inter (MeasurableSet.disjointed (measurableSet_packingCoverPiece C) j)

theorem packingCell_pairwiseDisjoint
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) :
    Set.PairwiseDisjoint Set.univ (packingCell C) := by
  intro i hi j hj hij
  exact (disjoint_disjointed (packingCoverPiece C) hij).mono
    inter_subset_right inter_subset_right

theorem iUnion_packingCell_eq
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) :
    ⋃ j, packingCell C j = A := by
  simp_rw [packingCell]
  rw [← inter_iUnion, iUnion_disjointed]
  have hall : ⋃ j, packingCoverPiece C j = Set.univ := by
    apply eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨C.centers.card, by simp [packingCoverPiece]⟩
  rw [hall, inter_univ]

def localFineVolume (U : Set Space) {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (j : ℕ) : ℝ≥0∞ :=
  volume (U ∩ Metric.ball (packingCenterAt C j) (rho : ℝ))

/-- The required third-scale packing exists for any subset of one fine tube;
this invokes the aligned frame-box compactness construction rather than
assuming a finite cover. -/
theorem exists_thirdScalePacking_of_subset_tube
    {A : Set Space} {delta rho : ℝ≥0} (fine : Tube delta)
    (hAfine : A ⊆ fine.carrier) (hrho : 0 < rho) :
    Nonempty (PackingCertificate A (rho / 3)) := by
  obtain ⟨frame, hframe⟩ := fine.exists_alignedFrame
  exact exists_packingCertificate (fine.alignedFrameBox frame)
    (hAfine.trans (fine.carrier_subset_alignedFrameBox frame hframe))
    (rho / 3) (div_pos hrho (by norm_num))

/-- TubeSpecificLocalGrowth supplies an absolute local cap for the same
radius-`rho` statistic. -/
theorem localFineVolume_le_tubeCap
    (U : Set Space) {A : Set Space} {delta rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (fine : Tube delta)
    (hUfine : U ⊆ fine.carrier) (j : ℕ) :
    localFineVolume U C j ≤
      8 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞) := by
  calc
    localFineVolume U C j ≤
        volume (fine.carrier ∩
          Metric.ball (packingCenterAt C j) (rho : ℝ)) :=
      measure_mono (inter_subset_inter_left _ hUfine)
    _ ≤ 8 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞) :=
      fine.volume_carrier_inter_ball_le_eight_mul_sq_mul
        (packingCenterAt C j) rho


def inVolumeBand (base : ℝ≥0∞) (n : ℕ) (v : ℝ≥0∞) : Prop :=
  (2 : ℝ≥0∞) ^ n * base ≤ v ∧
    v < (2 : ℝ≥0∞) ^ (n + 1) * base

def volumeBucket (base : ℝ≥0∞) (M : ℕ) (v : ℝ≥0∞) : ℕ :=
  if h : ∃ n, n ≤ M ∧ inVolumeBand base n v then Nat.find h else 0

theorem volumeBucket_spec {base : ℝ≥0∞} {M : ℕ} {v : ℝ≥0∞}
    (h : ∃ n, n ≤ M ∧ inVolumeBand base n v) :
    volumeBucket base M v ≤ M ∧
      inVolumeBand base (volumeBucket base M v) v := by
  rw [volumeBucket, dif_pos h]
  exact Nat.find_spec h

/-- A magnitude between `base` and the top dyadic endpoint belongs to one
of the first `M+1` half-open bands. -/
theorem exists_volumeBand_of_bounds {base v : ℝ≥0∞} {M : ℕ}
    (hlower : base ≤ v)
    (hupper : v < (2 : ℝ≥0∞) ^ (M + 1) * base) :
    ∃ n, n ≤ M ∧ inVolumeBand base n v := by
  let p : ℕ → Prop := fun n => v < (2 : ℝ≥0∞) ^ (n + 1) * base
  have hp : ∃ n, p n := ⟨M, hupper⟩
  let n := Nat.find hp
  have hnM : n ≤ M := Nat.find_min' hp hupper
  have hnUpper : p n := Nat.find_spec hp
  refine ⟨n, hnM, ?_, hnUpper⟩
  by_cases hn0 : n = 0
  · simpa [n, hn0] using hlower
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hklt : k < n := by omega
    have hnot : ¬ p k := Nat.find_min hp (by simpa [n] using hklt)
    simpa [p, hk] using (le_of_not_gt hnot)

/-! ## Cutoff at total mass divided by twice the number of cells -/

def cutoffBase {a : Type*} (s : Finset a) (w : a → ℝ≥0) : ℝ≥0 :=
  (∑ i ∈ s, w i) / (2 * s.card)

def lowCells {a : Type*} [DecidableEq a]
    (s : Finset a) (loc : a → ℝ≥0) (base : ℝ≥0) : Finset a :=
  s.filter fun i => loc i < base

def highCells {a : Type*} [DecidableEq a]
    (s : Finset a) (loc : a → ℝ≥0) (base : ℝ≥0) : Finset a :=
  s.filter fun i => base ≤ loc i

/-- Cells whose loc quantity is below `total/(2N)` carry at most half the
total weight. -/
theorem sum_lowCells_le_half
    {a : Type*} [DecidableEq a] (s : Finset a) (w loc : a → ℝ≥0)
    (hw : ∀ i ∈ s, w i ≤ loc i) :
    ∑ i ∈ lowCells s loc (cutoffBase s w), w i ≤
      (∑ i ∈ s, w i) / 2 := by
  classical
  by_cases hs : s.card = 0
  · have hsempty : s = ∅ := Finset.card_eq_zero.mp hs
    simp [hsempty, lowCells]
  · calc
      ∑ i ∈ lowCells s loc (cutoffBase s w), w i ≤
          ∑ _i ∈ lowCells s loc (cutoffBase s w), cutoffBase s w := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hw i ((Finset.mem_filter.mp hi).1)).trans
          (Finset.mem_filter.mp hi).2.le
      _ = (lowCells s loc (cutoffBase s w)).card • cutoffBase s w := by simp
      _ ≤ s.card • cutoffBase s w := by
        exact nsmul_le_nsmul_left (show 0 ≤ cutoffBase s w from bot_le)
          (Finset.card_le_card (Finset.filter_subset _ _))
      _ = (∑ i ∈ s, w i) / 2 := by
        simp only [nsmul_eq_mul, cutoffBase]
        field_simp

/-- The complementary high cells retain at least half of the weight, in
zero-division form. -/
theorem sum_le_two_mul_sum_highCells
    {a : Type*} [DecidableEq a] (s : Finset a) (w loc : a → ℝ≥0)
    (hw : ∀ i ∈ s, w i ≤ loc i) :
    ∑ i ∈ s, w i ≤
      2 * ∑ i ∈ highCells s loc (cutoffBase s w), w i := by
  classical
  have hsplit :
      (∑ i ∈ s, w i) =
        (∑ i ∈ highCells s loc (cutoffBase s w), w i) +
        ∑ i ∈ lowCells s loc (cutoffBase s w), w i := by
    rw [highCells, lowCells]
    simpa [not_lt, add_comm] using
      (Finset.sum_filter_add_sum_filter_not
        (s := s) (p := fun i => loc i < cutoffBase s w) w).symm
  have hlow := sum_lowCells_le_half s w loc hw
  rw [hsplit] at hlow ⊢
  nlinarith


/-- The exact exponent range forced by a finite family of `N` cells. -/
def logarithmicExponent {a : Type*} (s : Finset a) : ℕ := Nat.log 2 (2 * s.card)

/-- On the high cells, `base = total/(2N)` and `local ≤ total` place every
local quantity in one of `Nat.log 2 (2N)+1` dyadic bands. -/
theorem highCell_has_logarithmicVolumeBand
    {a : Type*} [DecidableEq a] (s : Finset a) (w loc : a → ℝ≥0)
    (htotal : 0 < ∑ i ∈ s, w i)
    (hloc : ∀ i ∈ s, loc i ≤ ∑ j ∈ s, w j) :
    ∀ i ∈ highCells s loc (cutoffBase s w),
      ∃ n, n ≤ logarithmicExponent s ∧
        inVolumeBand (cutoffBase s w : ℝ≥0∞) n (loc i : ℝ≥0∞) := by
  classical
  have hspos : 0 < s.card := by
    by_contra hs
    have hzero : s.card = 0 := Nat.eq_zero_of_not_pos hs
    have hsempty : s = ∅ := Finset.card_eq_zero.mp hzero
    simp [hsempty] at htotal
  have hqpos : (0 : ℝ≥0) < 2 * (s.card : ℝ≥0) := by positivity
  have hbasepos : 0 < cutoffBase s w := by
    exact div_pos htotal hqpos
  have htotal_eq :
      (∑ i ∈ s, w i) = (2 * s.card : ℕ) * cutoffBase s w := by
    simp only [cutoffBase]
    push_cast
    field_simp
  have hpowNat :
      2 * s.card < 2 ^ (Nat.log 2 (2 * s.card)).succ :=
    Nat.lt_pow_succ_log_self (by norm_num) (2 * s.card)
  have hpow :
      (2 : ℝ≥0∞) * (s.card : ℝ≥0∞) <
        (2 : ℝ≥0∞) ^ (logarithmicExponent s + 1) := by
    exact_mod_cast hpowNat
  intro i hi
  have hiS : i ∈ s := (Finset.mem_filter.mp hi).1
  have hlowerNN : cutoffBase s w ≤ loc i := (Finset.mem_filter.mp hi).2
  have hlower : (cutoffBase s w : ℝ≥0∞) ≤ (loc i : ℝ≥0∞) := by
    exact_mod_cast hlowerNN
  have hlocTotal : (loc i : ℝ≥0∞) ≤ ((∑ j ∈ s, w j : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast hloc i hiS
  have htotalTop :
      ((∑ j ∈ s, w j : ℝ≥0) : ℝ≥0∞) <
        (2 : ℝ≥0∞) ^ (logarithmicExponent s + 1) *
          (cutoffBase s w : ℝ≥0∞) := by
    rw [htotal_eq]
    push_cast
    exact ENNReal.mul_lt_mul_left
      (ENNReal.coe_ne_zero.mpr hbasepos.ne') ENNReal.coe_ne_top hpow
  exact exists_volumeBand_of_bounds hlower (hlocTotal.trans_lt htotalTop)


/-- Cutoff followed by one weighted dyadic pigeonhole.  The loss is exactly
`2 * (Nat.log 2 (2N) + 1)` and no division occurs in the conclusion. -/
theorem exists_logarithmicWeightedVolumeLevel
    {a : Type*} [DecidableEq a] (s : Finset a) (w loc : a → ℝ≥0)
    (hw : ∀ i ∈ s, w i ≤ loc i)
    (htotal : 0 < ∑ i ∈ s, w i)
    (hloc : ∀ i ∈ s, loc i ≤ ∑ j ∈ s, w j) :
    ∃ n, n ≤ logarithmicExponent s ∧
      let selected := (highCells s loc (cutoffBase s w)).filter fun i =>
        volumeBucket (cutoffBase s w : ℝ≥0∞) (logarithmicExponent s)
          (loc i : ℝ≥0∞) = n
      (∑ i ∈ s, w i) ≤
          (2 * (logarithmicExponent s + 1)) • ∑ i ∈ selected, w i ∧
        selected ⊆ s ∧
        ∀ i ∈ selected,
          inVolumeBand (cutoffBase s w : ℝ≥0∞) n (loc i : ℝ≥0∞) := by
  classical
  let high := highCells s loc (cutoffBase s w)
  let M := logarithmicExponent s
  have hband : ∀ i ∈ high,
      ∃ n, n ≤ M ∧
        inVolumeBand (cutoffBase s w : ℝ≥0∞) n (loc i : ℝ≥0∞) := by
    simpa [high, M] using highCell_has_logarithmicVolumeBand s w loc htotal hloc
  let bucket : a → Fin (M + 1) := fun i =>
    if hi : i ∈ high then
      ⟨volumeBucket (cutoffBase s w : ℝ≥0∞) M (loc i : ℝ≥0∞),
        Nat.lt_succ_of_le (volumeBucket_spec (hband i hi)).1⟩
    else ⟨0, Nat.zero_lt_succ M⟩
  obtain ⟨b, hbWeight⟩ :=
    Submission.Kakeya.Uniformity.exists_large_weighted_fiber high bucket w
  refine ⟨b.1, Nat.le_of_lt_succ b.2, ?_⟩
  dsimp only
  let selected := high.filter fun i =>
    volumeBucket (cutoffBase s w : ℝ≥0∞) M (loc i : ℝ≥0∞) = b.1
  have hselectedEq :
      Submission.Kakeya.Uniformity.dyadicFiber high bucket b = selected := by
    ext i
    simp only [Submission.Kakeya.Uniformity.mem_dyadicFiber,
      Finset.mem_filter, selected]
    constructor
    · rintro ⟨hi, hib⟩
      refine ⟨hi, ?_⟩
      have : bucket i =
          ⟨volumeBucket (cutoffBase s w : ℝ≥0∞) M (loc i : ℝ≥0∞),
            Nat.lt_succ_of_le (volumeBucket_spec (hband i hi)).1⟩ := by
        simp [bucket, hi]
      rw [this] at hib
      exact congrArg Fin.val hib
    · rintro ⟨hi, hib⟩
      refine ⟨hi, ?_⟩
      apply Fin.ext
      simpa [bucket, hi] using hib
  have hhigh : (∑ i ∈ s, w i) ≤ 2 * ∑ i ∈ high, w i := by
    simpa [high] using sum_le_two_mul_sum_highCells s w loc hw
  have hretain :
      (∑ i ∈ s, w i) ≤
        (2 * (M + 1)) • ∑ i ∈ selected, w i := by
    rw [hselectedEq] at hbWeight
    have hbWeight' : (∑ i ∈ high, w i) ≤ (M + 1) • ∑ i ∈ selected, w i := by
      simpa using hbWeight
    calc
      (∑ i ∈ s, w i) ≤ 2 * ∑ i ∈ high, w i := hhigh
      _ ≤ 2 * ((M + 1) • ∑ i ∈ selected, w i) :=
        mul_le_mul_of_nonneg_left hbWeight' bot_le
      _ = (2 * (M + 1)) • ∑ i ∈ selected, w i := by
        simp only [nsmul_eq_mul]
        push_cast
        ring
  refine ⟨by simpa [high, M, selected] using hretain, ?_, ?_⟩
  · exact (Finset.filter_subset _ _).trans
      ((Finset.filter_subset _ _ : high ⊆ s))
  · intro i hi
    have hiHigh : i ∈ high := (Finset.mem_filter.mp hi).1
    have hiBucket := (Finset.mem_filter.mp hi).2
    have hspec := (volumeBucket_spec (hband i hiHigh)).2
    rw [hiBucket] at hspec
    exact hspec

/-- Boundary-complete wrapper: zero total mass is returned as a trivial branch;
the positive branch has the logarithmic weighted level above.  Since weights
are `NNReal`, the infinite-volume case must be discharged before conversion. -/
theorem zero_or_exists_logarithmicWeightedVolumeLevel
    {a : Type*} [DecidableEq a] (s : Finset a) (w loc : a → ℝ≥0)
    (hw : ∀ i ∈ s, w i ≤ loc i)
    (hloc : ∀ i ∈ s, loc i ≤ ∑ j ∈ s, w j) :
    (∑ i ∈ s, w i) = 0 ∨
      ∃ n, n ≤ logarithmicExponent s ∧
        let selected := (highCells s loc (cutoffBase s w)).filter fun i =>
          volumeBucket (cutoffBase s w : ℝ≥0∞) (logarithmicExponent s)
            (loc i : ℝ≥0∞) = n
        (∑ i ∈ s, w i) ≤
            (2 * (logarithmicExponent s + 1)) • ∑ i ∈ selected, w i ∧
          selected ⊆ s ∧
          ∀ i ∈ selected,
            inVolumeBand (cutoffBase s w : ℝ≥0∞) n (loc i : ℝ≥0∞) := by
  rcases eq_or_lt_of_le (show 0 ≤ ∑ i ∈ s, w i from bot_le) with hzero | hpos
  · exact Or.inl hzero.symm
  · exact Or.inr (exists_logarithmicWeightedVolumeLevel s w loc hw hpos hloc)


def validCenterIndices {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) : Finset ℕ :=
  Finset.range C.centers.card

theorem mem_disjointed_owner
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (x : Space) :
    x ∈ disjointed (packingCoverPiece C) (packingOwnerIndex C x) := by
  rw [← preimage_find_eq_disjointed (packingCoverPiece C)
    (exists_mem_packingCoverPiece C)]
  simp [packingOwnerIndex]

theorem biUnion_valid_packingCell_eq
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho) :
    ⋃ j ∈ validCenterIndices C, packingCell C j = A := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun j hj => inter_subset_left
  · intro x hx
    let j := packingOwnerIndex C x
    have hj : j < C.centers.card := packingOwnerIndex_lt_card C hrho hx
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr hj, hx, mem_disjointed_owner C x⟩⟩

def finePackingCell (U : Set Space) {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (j : ℕ) : Set Space :=
  U ∩ packingCell C j

theorem biUnion_valid_finePackingCell_eq
    (U : Set Space) {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    (hUA : U ⊆ A) :
    ⋃ j ∈ validCenterIndices C, finePackingCell U C j = U := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hj, hxcell⟩ := Set.mem_iUnion.mp hx
    exact hxcell.1
  · intro hx
    have hxA := hUA hx
    have hxcover : x ∈ ⋃ j ∈ validCenterIndices C, packingCell C j := by
      rw [biUnion_valid_packingCell_eq C hrho]
      exact hxA
    obtain ⟨j, hxcover⟩ := Set.mem_iUnion.mp hxcover
    obtain ⟨hj, hxcell⟩ := Set.mem_iUnion.mp hxcover
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hx, hxcell⟩⟩

theorem volume_eq_sum_finePackingCell
    (U : Set Space) (hU : MeasurableSet U) {A : Set Space} (hA : MeasurableSet A)
    {rho : ℝ≥0} (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    (hUA : U ⊆ A) :
    volume U = ∑ j ∈ validCenterIndices C, volume (finePackingCell U C j) := by
  calc
    volume U = volume (⋃ j ∈ validCenterIndices C, finePackingCell U C j) := by
      rw [biUnion_valid_finePackingCell_eq U C hrho hUA]
    _ = _ := by
      exact measure_biUnion_finset
        (fun i hi j hj hij =>
          (packingCell_pairwiseDisjoint C (Set.mem_univ i)
            (Set.mem_univ j) hij).mono inter_subset_right inter_subset_right)
        (fun j hj => hU.inter (measurableSet_packingCell hA C j))

def fineCellWeight (U : Set Space) {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (j : ℕ) : ℝ≥0 :=
  (volume (finePackingCell U C j)).toNNReal

def localFineWeight (U : Set Space) {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (j : ℕ) : ℝ≥0 :=
  (localFineVolume U C j).toNNReal

theorem fineCellWeight_le_localFineWeight
    (U : Set Space) {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3))
    (hUfinite : volume U ≠ ∞) {j : ℕ} (hj : j ∈ validCenterIndices C) :
    fineCellWeight U C j ≤ localFineWeight U C j := by
  apply ENNReal.toNNReal_mono
  · exact ne_top_of_le_ne_top hUfinite (measure_mono inter_subset_left)
  · apply measure_mono
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hjlt := Finset.mem_range.mp hj
    have hpiece : x ∈ packingCoverPiece C j :=
      disjointed_subset (packingCoverPiece C) j hx.2.2
    simpa [packingCoverPiece, hjlt] using hpiece

theorem sum_fineCellWeight_eq
    (U : Set Space) (hU : MeasurableSet U) {A : Set Space} (hA : MeasurableSet A)
    {rho : ℝ≥0} (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    (hUA : U ⊆ A) (hUfinite : volume U ≠ ∞) :
    ∑ j ∈ validCenterIndices C, fineCellWeight U C j = (volume U).toNNReal := by
  rw [volume_eq_sum_finePackingCell U hU hA C hrho hUA]
  rw [ENNReal.toNNReal_sum]
  · rfl
  · intro j hj
    exact ne_top_of_le_ne_top hUfinite (measure_mono inter_subset_left)

theorem localFineWeight_le_total
    (U : Set Space) (hU : MeasurableSet U) {A : Set Space} (hA : MeasurableSet A)
    {rho : ℝ≥0} (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    (hUA : U ⊆ A) (hUfinite : volume U ≠ ∞)
    {j : ℕ} ( _hj : j ∈ validCenterIndices C) :
    localFineWeight U C j ≤ ∑ q ∈ validCenterIndices C, fineCellWeight U C q := by
  rw [sum_fineCellWeight_eq U hU hA C hrho hUA hUfinite]
  exact ENNReal.toNNReal_mono hUfinite (measure_mono inter_subset_left)

/-- Fully geometric cutoff/log bridge.  `volume U = 0` covers both the empty
packing and zero-mass cases; otherwise the selected packing cells retain mass
with the stated logarithmic loss and their radius-`rho` local fine volumes are
all in one dyadic band. -/
theorem zero_or_exists_ballwiseLogarithmicLevel
    (U : Set Space) (hU : MeasurableSet U) {A : Set Space} (hA : MeasurableSet A)
    {rho : ℝ≥0} (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    (hUA : U ⊆ A) (hUfinite : volume U ≠ ∞) :
    volume U = 0 ∨
      ∃ n, n ≤ logarithmicExponent (validCenterIndices C) ∧
        let s := validCenterIndices C
        let w := fineCellWeight U C
        let loc := localFineWeight U C
        let selected := (highCells s loc (cutoffBase s w)).filter fun i =>
          volumeBucket (cutoffBase s w : ℝ≥0∞) (logarithmicExponent s)
            (loc i : ℝ≥0∞) = n
        (volume U).toNNReal ≤
            (2 * (logarithmicExponent s + 1)) • ∑ i ∈ selected, w i ∧
          selected ⊆ s ∧
          ∀ i ∈ selected,
            inVolumeBand (cutoffBase s w : ℝ≥0∞) n (loc i : ℝ≥0∞) := by
  have hbridge := zero_or_exists_logarithmicWeightedVolumeLevel
    (validCenterIndices C) (fineCellWeight U C) (localFineWeight U C)
    (fun i hi => fineCellWeight_le_localFineWeight U C hUfinite hi)
    (fun i hi => localFineWeight_le_total U hU hA C hrho hUA hUfinite hi)
  rw [sum_fineCellWeight_eq U hU hA C hrho hUA hUfinite] at hbridge
  rcases hbridge with hzero | hlevel
  · exact Or.inl ((ENNReal.toNNReal_eq_zero_iff (volume U)).mp hzero |>.resolve_right hUfinite)
  · exact Or.inr hlevel


def packingVolumeStatistic (U : Set Space) {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (base : ℝ≥0∞) (M : ℕ)
    (x : Space) : ℕ :=
  volumeBucket base M (localFineVolume U C (packingOwnerIndex C x))

theorem measurable_packingVolumeStatistic
    (U : Set Space) {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (base : ℝ≥0∞) (M : ℕ) :
    Measurable (packingVolumeStatistic U C base M) := by
  exact (measurable_of_countable
    (fun j : ℕ => volumeBucket base M (localFineVolume U C j))).comp
      (measurable_packingOwnerIndex C)

theorem exists_ballwiseLocalVolumeLevel
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι}
    (Z : Shading F) (U A : Set Space) {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    (hZA : Z.shadedUnion ⊆ A) (base : ℝ≥0∞) (M : ℕ)
    (hbands : ∀ j, j < C.centers.card →
      ∃ n, n ≤ M ∧ inVolumeBand base n (localFineVolume U C j)) :
    ∃ n ∈ Finset.range (M + 1),
      Z.shadingMass ≤ (M + 1) •
        (restrictStatisticLevel Z (packingVolumeStatistic U C base M)
          (fun q => (measurable_packingVolumeStatistic U C base M)
            (measurableSet_singleton q)) n).shadingMass ∧
      ∀ x ∈ (restrictStatisticLevel Z (packingVolumeStatistic U C base M)
          (fun q => (measurable_packingVolumeStatistic U C base M)
            (measurableSet_singleton q)) n).shadedUnion,
        let j := packingOwnerIndex C x
        j < C.centers.card ∧
          x ∈ Metric.ball (packingCenterAt C j) (rho : ℝ) ∧
          inVolumeBand base n (localFineVolume U C j) := by
  let stat : Space → ℕ := packingVolumeStatistic U C base M
  have hstat : ∀ q, MeasurableSet {x | stat x = q} := by
    intro q
    exact (measurable_packingVolumeStatistic U C base M)
      (measurableSet_singleton q)
  have hbound : ∀ x ∈ Z.shadedUnion, stat x ≤ M := by
    intro x hx
    have hlt := packingOwnerIndex_lt_card C hrho (hZA hx)
    exact (volumeBucket_spec (hbands _ hlt)).1
  obtain ⟨n, hn, hmass, hlevel⟩ :=
    exists_restrictStatisticLevel_with_large_mass Z stat M hstat hbound
  refine ⟨n, hn, ?_, ?_⟩
  · simpa [stat, hstat] using hmass
  · intro x hx
    have hxold : x ∈ Z.shadedUnion :=
      restrictStatisticLevel_shadedUnion_subset Z stat hstat n hx
    have hlt := packingOwnerIndex_lt_card C hrho (hZA hxold)
    have hball := mem_owner_ball C hrho (hZA hxold)
    have hspec := (volumeBucket_spec (hbands _ hlt)).2
    have heq : stat x = n := hlevel x hx
    refine ⟨hlt, hball, ?_⟩
    have heq' :
        volumeBucket base M (localFineVolume U C (packingOwnerIndex C x)) = n := by
      simpa [stat, packingVolumeStatistic] using heq
    rw [heq'] at hspec
    exact hspec

end BallwiseLocalVolumeUniformization

end

end Submission.Kakeya.ConvexFactoring

#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.PackingCertificate.subset_iUnion_rhoBalls
#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.exists_ballwiseLocalVolumeLevel
#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.sum_lowCells_le_half
#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.exists_logarithmicWeightedVolumeLevel
#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.zero_or_exists_logarithmicWeightedVolumeLevel
#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.biUnion_valid_packingCell_eq
#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.volume_eq_sum_finePackingCell
#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.zero_or_exists_ballwiseLogarithmicLevel
#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.exists_thirdScalePacking_of_subset_tube
#print axioms Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization.localFineVolume_le_tubeCap

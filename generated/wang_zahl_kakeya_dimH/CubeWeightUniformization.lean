import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
import Submission.Kakeya.ConvexFactoring.FrameBoxInducedCoveringGrowth
import Submission.Kakeya.Uniformity.Pigeonhole

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace CubeWeightUniformization

/-!
This scratch module formalizes only the finite packing-cell version of the
paper's final ball/cube-weight pigeonhole.  It deliberately makes no claim for
all continuously varying ball centers.

`mass q` is the multiplicity-counted fine shaded mass assigned to cell `q`,
while `loc q` is the local fine-union volume in that cell.  A pointwise
multiplicity cap `K` gives `mass q <= K * loc q`.  The cutoff

  total mass / (2 K N)

discards at most half the mass.  The remaining local volumes occupy only
`log_2 (2 K N) + 1` half-open dyadic bands.
-/

def dominanceCutoff {a : Type*} [Fintype a]
    (mass : a → ℝ≥0) (K : ℕ) : ℝ≥0 :=
  (∑ q, mass q) / (2 * K * Fintype.card a)

def lowCells {a : Type*} [Fintype a] [DecidableEq a]
    (mass loc : a → ℝ≥0) (K : ℕ) : Finset a :=
  Finset.univ.filter fun q ↦ loc q < dominanceCutoff mass K

def highCells {a : Type*} [Fintype a] [DecidableEq a]
    (mass loc : a → ℝ≥0) (K : ℕ) : Finset a :=
  Finset.univ.filter fun q ↦ dominanceCutoff mass K ≤ loc q

def cubeExponent {a : Type*} [Fintype a] (K : ℕ) : ℕ :=
  Nat.log 2 (2 * K * Fintype.card a)

def inDyadicBand (base : ℝ≥0) (n : ℕ) (v : ℝ≥0) : Prop :=
  2 ^ n * base ≤ v ∧ v < 2 ^ (n + 1) * base

def cubeBucket (base : ℝ≥0) (M : ℕ) (v : ℝ≥0) : ℕ :=
  if h : ∃ n, n ≤ M ∧ inDyadicBand base n v then Nat.find h else 0

theorem cubeBucket_spec {base : ℝ≥0} {M : ℕ} {v : ℝ≥0}
    (h : ∃ n, n ≤ M ∧ inDyadicBand base n v) :
    cubeBucket base M v ≤ M ∧
      inDyadicBand base (cubeBucket base M v) v := by
  rw [cubeBucket, dif_pos h]
  exact Nat.find_spec h

theorem exists_dyadicBand_of_bounds {base v : ℝ≥0} {M : ℕ}
    (hlower : base ≤ v) (hupper : v < 2 ^ (M + 1) * base) :
    ∃ n, n ≤ M ∧ inDyadicBand base n v := by
  let p : ℕ → Prop := fun n ↦ v < 2 ^ (n + 1) * base
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

theorem sum_lowCells_le_half
    {a : Type*} [Fintype a] [DecidableEq a]
    (mass loc : a → ℝ≥0) (K : ℕ)
    (hdom : ∀ q, mass q ≤ K * loc q) :
    ∑ q ∈ lowCells mass loc K, mass q ≤ (∑ q, mass q) / 2 := by
  classical
  by_cases hden : K * Fintype.card a = 0
  · rcases Nat.mul_eq_zero.mp hden with hK | ha
    · subst K
      have hm : ∀ q, mass q = 0 := fun q ↦
        le_antisymm (by simpa using hdom q) bot_le
      simp [hm]
    · have : IsEmpty a := Fintype.card_eq_zero_iff.mp ha
      simp [lowCells]
  · have hKpos : 0 < K := Nat.pos_of_ne_zero (fun hK => hden (by simp [hK]))
    have hcardpos : 0 < Fintype.card a :=
      Nat.pos_of_ne_zero (fun ha => hden (by simp [ha]))
    calc
      ∑ q ∈ lowCells mass loc K, mass q ≤
          ∑ _q ∈ lowCells mass loc K,
            K * dominanceCutoff mass K := by
        apply Finset.sum_le_sum
        intro q hq
        exact (hdom q).trans (mul_le_mul_of_nonneg_left
          (Finset.mem_filter.mp hq).2.le bot_le)
      _ = (lowCells mass loc K).card •
          (K * dominanceCutoff mass K) := by simp
      _ ≤ Fintype.card a • (K * dominanceCutoff mass K) := by
        exact nsmul_le_nsmul_left bot_le
          (Finset.card_le_card (Finset.filter_subset _ _))
      _ = (∑ q, mass q) / 2 := by
        simp only [nsmul_eq_mul, dominanceCutoff]
        field_simp [show (Fintype.card a : ℝ≥0) ≠ 0 by positivity, show (K : ℝ≥0) ≠ 0 by positivity]

theorem sum_le_two_mul_sum_highCells
    {a : Type*} [Fintype a] [DecidableEq a]
    (mass loc : a → ℝ≥0) (K : ℕ)
    (hdom : ∀ q, mass q ≤ K * loc q) :
    ∑ q, mass q ≤ 2 * ∑ q ∈ highCells mass loc K, mass q := by
  classical
  have hsplit :
      (∑ q, mass q) =
        (∑ q ∈ highCells mass loc K, mass q) +
          ∑ q ∈ lowCells mass loc K, mass q := by
    rw [highCells, lowCells]
    simpa [not_lt, add_comm] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset a))
        (p := fun q ↦ loc q < dominanceCutoff mass K) mass).symm
  have hlow := sum_lowCells_le_half mass loc K hdom
  rw [hsplit] at hlow ⊢
  nlinarith

theorem highCell_has_dyadicBand
    {a : Type*} [Fintype a] [DecidableEq a]
    (mass loc : a → ℝ≥0) (K : ℕ) (hK : 0 < K)
    (htotal : 0 < ∑ q, mass q)
    (hloc : ∀ q, loc q ≤ ∑ p, mass p) :
    ∀ q ∈ highCells mass loc K,
      ∃ n, n ≤ cubeExponent (a := a) K ∧
        inDyadicBand (dominanceCutoff mass K) n (loc q) := by
  classical
  have hcard : 0 < Fintype.card a := by
    by_contra ha
    have : IsEmpty a := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos ha)
    simp at htotal
  have hden : (0 : ℝ≥0) < 2 * K * Fintype.card a := by positivity
  have hbase : 0 < dominanceCutoff mass K := div_pos htotal hden
  have htotal_eq :
      (∑ q, mass q) =
        (2 * K * Fintype.card a : ℕ) * dominanceCutoff mass K := by
    simp only [dominanceCutoff]
    push_cast
    field_simp
  have hpowNat :
      2 * K * Fintype.card a <
        2 ^ (Nat.log 2 (2 * K * Fintype.card a)).succ :=
    Nat.lt_pow_succ_log_self (by norm_num)
      (2 * K * Fintype.card a)
  have hpow :
      (2 * K * Fintype.card a : ℝ≥0) <
        2 ^ (cubeExponent (a := a) K + 1) := by
    exact_mod_cast hpowNat
  intro q hq
  have hlower : dominanceCutoff mass K ≤ loc q :=
    (Finset.mem_filter.mp hq).2
  have hupper : loc q <
      2 ^ (cubeExponent (a := a) K + 1) * dominanceCutoff mass K := by
    calc
      loc q ≤ ∑ p, mass p := hloc q
      _ = (2 * K * Fintype.card a : ℕ) * dominanceCutoff mass K := htotal_eq
      _ < 2 ^ (cubeExponent (a := a) K + 1) * dominanceCutoff mass K := by
        push_cast
        exact mul_lt_mul_of_pos_right hpow hbase
  exact exists_dyadicBand_of_bounds hlower hupper

/-- Weighted dyadic selection of a finite family of packing cells.  The
retention is for `mass`, while the uniformized statistic is `loc`. -/
theorem exists_weightedCubeLevel
    {a : Type*} [Fintype a] [DecidableEq a]
    (mass loc : a → ℝ≥0) (K : ℕ) (hK : 0 < K)
    (hdom : ∀ q, mass q ≤ K * loc q)
    (htotal : 0 < ∑ q, mass q)
    (hloc : ∀ q, loc q ≤ ∑ p, mass p) :
    ∃ n, n ≤ cubeExponent (a := a) K ∧
      let selected := (highCells mass loc K).filter fun q ↦
        cubeBucket (dominanceCutoff mass K) (cubeExponent (a := a) K) (loc q) = n
      (∑ q, mass q) ≤
          (2 * (cubeExponent (a := a) K + 1)) • ∑ q ∈ selected, mass q ∧
        ∀ q ∈ selected,
          inDyadicBand (dominanceCutoff mass K) n (loc q) := by
  classical
  let high := highCells mass loc K
  let M := cubeExponent (a := a) K
  have hband : ∀ q ∈ high,
      ∃ n, n ≤ M ∧ inDyadicBand (dominanceCutoff mass K) n (loc q) := by
    simpa [high, M] using highCell_has_dyadicBand mass loc K hK htotal hloc
  let bucket : a → Fin (M + 1) := fun q ↦
    if hq : q ∈ high then
      ⟨cubeBucket (dominanceCutoff mass K) M (loc q),
        Nat.lt_succ_of_le (cubeBucket_spec (hband q hq)).1⟩
    else ⟨0, Nat.zero_lt_succ M⟩
  obtain ⟨b, hb⟩ := exists_large_weighted_fiber high bucket mass
  refine ⟨b.1, Nat.le_of_lt_succ b.2, ?_⟩
  dsimp only
  let selected := high.filter fun q ↦
    cubeBucket (dominanceCutoff mass K) M (loc q) = b.1
  have hselected : dyadicFiber high bucket b = selected := by
    ext q
    simp only [mem_dyadicFiber, Finset.mem_filter, selected]
    constructor
    · rintro ⟨hq, hqb⟩
      refine ⟨hq, ?_⟩
      have heq : bucket q =
          ⟨cubeBucket (dominanceCutoff mass K) M (loc q),
            Nat.lt_succ_of_le (cubeBucket_spec (hband q hq)).1⟩ := by
        simp [bucket, hq]
      rw [heq] at hqb
      exact congrArg Fin.val hqb
    · rintro ⟨hq, hqb⟩
      refine ⟨hq, ?_⟩
      apply Fin.ext
      simpa [bucket, hq] using hqb
  rw [hselected] at hb
  have hhigh : (∑ q, mass q) ≤ 2 * ∑ q ∈ high, mass q := by
    simpa [high] using sum_le_two_mul_sum_highCells mass loc K hdom
  have hretain : (∑ q, mass q) ≤
      (2 * (M + 1)) • ∑ q ∈ selected, mass q := by
    have hb' : (∑ q ∈ high, mass q) ≤
        (M + 1) • ∑ q ∈ selected, mass q := by simpa using hb
    calc
      (∑ q, mass q) ≤ 2 * ∑ q ∈ high, mass q := hhigh
      _ ≤ 2 * ((M + 1) • ∑ q ∈ selected, mass q) :=
        mul_le_mul_of_nonneg_left hb' bot_le
      _ = (2 * (M + 1)) • ∑ q ∈ selected, mass q := by
        simp only [nsmul_eq_mul]
        push_cast
        ring
  refine ⟨by simpa [high, M, selected] using hretain, ?_⟩
  intro q hq
  have hqHigh : q ∈ high := (Finset.mem_filter.mp hq).1
  have hqBucket := (Finset.mem_filter.mp hq).2
  have hspec := (cubeBucket_spec (hband q hqHigh)).2
  rw [hqBucket] at hspec
  exact hspec

def selectedRegion {a : Type*} (cell : a → Set Space)
    (selected : Finset a) : Set Space :=
  ⋃ q ∈ selected, cell q

theorem measurableSet_selectedRegion {a : Type*}
    (cell : a → Set Space) (hcell : ∀ q, MeasurableSet (cell q))
    (selected : Finset a) : MeasurableSet (selectedRegion cell selected) := by
  exact Finset.measurableSet_biUnion selected (fun q _ ↦ hcell q)

def restrictToCells {a ι : Type*} {F : ConvexFamily ι}
    (Y : Shading F) (cell : a → Set Space)
    (hcell : ∀ q, MeasurableSet (cell q)) (selected : Finset a) : Shading F :=
  Y.restrictSet (selectedRegion cell selected)
    (measurableSet_selectedRegion cell hcell selected)

@[simp] theorem restrictToCells_carrier {a ι : Type*}
    {F : ConvexFamily ι} (Y : Shading F) (cell : a → Set Space)
    (hcell : ∀ q, MeasurableSet (cell q)) (selected : Finset a) (i : ι) :
    (restrictToCells Y cell hcell selected).carrier i =
      Y.carrier i ∩ selectedRegion cell selected := rfl

theorem restrictToCells_shadedUnion {a ι : Type*} [Fintype ι]
    {F : ConvexFamily ι} (Y : Shading F) (cell : a → Set Space)
    (hcell : ∀ q, MeasurableSet (cell q)) (selected : Finset a) :
    (restrictToCells Y cell hcell selected).shadedUnion =
      Y.shadedUnion ∩ selectedRegion cell selected := by
  exact Shading.restrictSet_shadedUnion Y _ _

/-- The identical finite cell slice is applied to the final fine shading and
its independent frozen coarse cover; hence the cover relation survives. -/
theorem commonCellRestriction_preserves_cover
    {a ι κ : Type*} [Fintype ι] [Fintype κ]
    {F : ConvexFamily ι} {W : ConvexFamily κ}
    (fine : Shading F) (coarse : Shading W)
    (cell : a → Set Space) (hcell : ∀ q, MeasurableSet (cell q))
    (selected : Finset a)
    (hcover : fine.shadedUnion ⊆ coarse.shadedUnion) :
    (restrictToCells fine cell hcell selected).shadedUnion ⊆
      (restrictToCells coarse cell hcell selected).shadedUnion := by
  rw [restrictToCells_shadedUnion, restrictToCells_shadedUnion]
  exact inter_subset_inter_left _ hcover

theorem cell_subset_selectedRegion {a : Type*} (cell : a → Set Space)
    (selected : Finset a) {q : a} (hq : q ∈ selected) :
    cell q ⊆ selectedRegion cell selected := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, hx⟩⟩

/-- On a selected cell, recomputing the local fine union after the common
restriction gives exactly the frozen cell statistic, not merely an upper bound. -/
theorem restrictToCells_local_eq {a ι : Type*} [Fintype ι]
    {F : ConvexFamily ι} (fine : Shading F)
    (cell : a → Set Space) (hcell : ∀ q, MeasurableSet (cell q))
    (selected : Finset a) {q : a} (hq : q ∈ selected) :
    (restrictToCells fine cell hcell selected).shadedUnion ∩ cell q =
      fine.shadedUnion ∩ cell q := by
  rw [restrictToCells_shadedUnion]
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · exact fun hx ↦ ⟨hx.1.1, hx.2⟩
  · intro hx
    exact ⟨⟨hx.1, cell_subset_selectedRegion cell selected hq hx.2⟩, hx.2⟩

/-- A dyadic band is literally the requested half-open interval `[w,2w)`. -/
theorem inDyadicBand_halfOpen {base v : ℝ≥0} {n : ℕ}
    (h : inDyadicBand base n v) :
    let w := 2 ^ n * base
    w ≤ v ∧ v < 2 * w := by
  simpa [inDyadicBand, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem shadingMass_ne_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ConvexFamily ι} (Y : Shading F) : Y.shadingMass ≠ ∞ := by
  rw [shadingMass_eq_coe_sum_shadingWeight]
  exact ENNReal.coe_ne_top

def cellMass {a ι : Type*} [Fintype ι]
    {F : ConvexFamily ι} (Y : Shading F)
    (cell : a → Set Space) (hcell : ∀ q, MeasurableSet (cell q))
    (q : a) : ℝ≥0 :=
  ((Y.restrictSet (cell q) (hcell q)).shadingMass).toNNReal

def localCellVolume {a ι : Type*} [Fintype ι]
    {F : ConvexFamily ι} (Y : Shading F)
    (cell : a → Set Space) (q : a) : ℝ≥0 :=
  (volume (Y.shadedUnion ∩ cell q)).toNNReal

@[simp] theorem coe_cellMass {a ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ConvexFamily ι} (Y : Shading F)
    (cell : a → Set Space) (hcell : ∀ q, MeasurableSet (cell q)) (q : a) :
    (cellMass Y cell hcell q : ℝ≥0∞) =
      (Y.restrictSet (cell q) (hcell q)).shadingMass := by
  exact ENNReal.coe_toNNReal (shadingMass_ne_top _ )

@[simp] theorem coe_localCellVolume {a ι : Type*} [Fintype ι]
    [DecidableEq ι] {F : ConvexFamily ι} (Y : Shading F)
    (cell : a → Set Space) (q : a) :
    (localCellVolume Y cell q : ℝ≥0∞) =
      volume (Y.shadedUnion ∩ cell q) := by
  apply ENNReal.coe_toNNReal
  exact ne_top_of_le_ne_top (shadingMass_ne_top Y)
    ((measure_mono inter_subset_left).trans
      (by
        unfold Shading.shadingMass
        exact measure_iUnion_fintype_le volume _))

/-- The first requested connection: disjoint finite cells which cover the fine
shaded union split every fine carrier and hence the full shading mass. -/
theorem sum_cellMass_eq_shadingMass_toNNReal
    {a ι : Type*} [Fintype a] [DecidableEq a]
    [Fintype ι] [DecidableEq ι] {F : ConvexFamily ι}
    (Y : Shading F) (cell : a → Set Space)
    (hcell : ∀ q, MeasurableSet (cell q))
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    (hcover : Y.shadedUnion ⊆ ⋃ q, cell q) :
    ∑ q, cellMass Y cell hcell q = Y.shadingMass.toNNReal := by
  apply ENNReal.coe_injective
  rw [ENNReal.coe_toNNReal (shadingMass_ne_top Y)]
  rw [ENNReal.ofNNReal_finsetSum]
  simp_rw [coe_cellMass]
  unfold Shading.shadingMass
  simp_rw [Shading.restrictSet_carrier]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hunion : (⋃ q ∈ (Finset.univ : Finset a), Y.carrier i ∩ cell q) =
      Y.carrier i := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun q hq ↦ inter_subset_left
    · intro x hx
      have hxUnion : x ∈ Y.shadedUnion := Set.mem_iUnion.mpr ⟨i, hx⟩
      obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp (hcover hxUnion)
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr
        ⟨Finset.mem_univ q, hx, hxq⟩⟩
  calc
    ∑ q, volume (Y.carrier i ∩ cell q) =
        volume (⋃ q ∈ (Finset.univ : Finset a), Y.carrier i ∩ cell q) := by
      symm
      exact measure_biUnion_finset
        (fun q hq r hr hqr ↦
          (hdisj (Set.mem_univ q) (Set.mem_univ r) hqr).mono
            inter_subset_right inter_subset_right)
        (fun q hq ↦ (Y.measurable_carrier i).inter (hcell q))
    _ = volume (Y.carrier i) := congrArg volume hunion

/-- The second requested connection: integrate the existing pointwise
multiplicity cap on the shading restricted to one cell. -/
theorem cellMass_le_mul_localCellVolume
    {a ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ConvexFamily ι} (Y : Shading F)
    (cell : a → Set Space) (hcell : ∀ q, MeasurableSet (cell q))
    (K : ℕ) (hpoint : ∀ x, Y.pointMultiplicity x ≤ K) (q : a) :
    cellMass Y cell hcell q ≤ K * localCellVolume Y cell q := by
  let Z := Y.restrictSet (cell q) (hcell q)
  have hZpoint : ∀ x, Z.pointMultiplicity x ≤ K := by
    intro x
    rw [Shading.pointMultiplicity_restrictSet]
    split_ifs
    · exact hpoint x
    · exact Nat.zero_le _
  have htop :=
    FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
      Z K hZpoint
  have hvolFinite : volume Z.shadedUnion ≠ ∞ := by
    apply ne_top_of_le_ne_top (shadingMass_ne_top Z)
    change volume (⋃ i, Z.carrier i) ≤ ∑ i, volume (Z.carrier i)
    exact measure_iUnion_fintype_le volume _
  have htopFinite : K • volume Z.shadedUnion ≠ ∞ := by
    simp only [nsmul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hvolFinite
  have hnn := (ENNReal.toNNReal_le_toNNReal
    (shadingMass_ne_top Z) htopFinite).2 htop
  simpa [cellMass, localCellVolume, Z, Shading.restrictSet_shadedUnion,
    nsmul_eq_mul, ENNReal.toNNReal_mul] using hnn

end CubeWeightUniformization

end

end Submission.Kakeya.ConvexFactoring

#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightUniformization.exists_weightedCubeLevel
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightUniformization.measurableSet_selectedRegion
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightUniformization.commonCellRestriction_preserves_cover
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightUniformization.inDyadicBand_halfOpen
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightUniformization.restrictToCells_local_eq

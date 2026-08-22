import Submission.Kakeya.ConvexFactoring.MultiplicityPigeonhole
import Submission.Kakeya.ConvexFactoring.NeighborhoodInducedShading

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-!
# Bounded point-statistic level restriction

This file isolates the finite combinatorial core of the multiplicity
refinements in Proposition 5.1. A single measurable natural-valued statistic
is sliced on the shaded union, and every carrier is restricted by the same
slice. No selected level is stored as input data.

For exact induced shadings, common spatial restriction commutes with the fiber
union, so recomputing the induced outer point multiplicity gives an exact
equality. For neighborhood-induced shadings, recomputation is proved only
monotone nonincreasing: thickening need not commute with intersection. An
equality there still requires a neighborhood-saturation or stable-witness
hypothesis, which this module does not assume.
-/

namespace StatisticLevelRestriction

variable {ι : Type*} {F : ConvexFamily ι}

/-- The part of the shaded union on which a point statistic equals `n`. -/
def statisticSlice (Y : Shading F) (stat : Space → ℕ) (n : ℕ) : Set Space :=
  Y.shadedUnion ∩ {x | stat x = n}

theorem measurableSet_statisticSlice (Y : Shading F) (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) (n : ℕ)
    [Fintype ι] :
    MeasurableSet (statisticSlice Y stat n) :=
  Y.shadedUnion_measurableSet.inter (hstat n)

theorem statisticSlice_disjoint (Y : Shading F) (stat : Space → ℕ)
    {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (statisticSlice Y stat m) (statisticSlice Y stat n) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  exact hmn (hxm.2.symm.trans hxn.2)

/-- A bound on the shaded union makes the levels `0, ..., M` an exact cover. -/
theorem shadedUnion_eq_iUnion_statisticSlice [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ) (M : ℕ)
    (hbound : ∀ x ∈ Y.shadedUnion, stat x ≤ M) :
    Y.shadedUnion =
      ⋃ n ∈ Finset.range (M + 1), statisticSlice Y stat n := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.mpr ⟨stat x, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ?_, hx, rfl⟩
    exact Nat.lt_succ_of_le (hbound x hx)
  · intro hx
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_hn, hxn⟩ := Set.mem_iUnion.mp hx
    exact hxn.1

theorem pairwiseDisjoint_statisticSlice (Y : Shading F)
    (stat : Space → ℕ) (M : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (M + 1)) : Set ℕ)
      (statisticSlice Y stat) := by
  intro m hm n hn hmn
  exact statisticSlice_disjoint Y stat hmn

/-- Exact decomposition of the shaded-union volume by statistic level. -/
theorem volume_shadedUnion_eq_sum_statisticSlice [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ) (M : ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (hbound : ∀ x ∈ Y.shadedUnion, stat x ≤ M) :
    volume Y.shadedUnion =
      ∑ n ∈ Finset.range (M + 1), volume (statisticSlice Y stat n) := by
  rw [shadedUnion_eq_iUnion_statisticSlice Y stat M hbound]
  exact measure_biUnion_finset (pairwiseDisjoint_statisticSlice Y stat M)
    (fun n hn => measurableSet_statisticSlice Y stat hstat n)

/-- Restrict every shaded carrier by one level of a common point statistic. -/
def restrictStatisticLevel [Fintype ι] (Y : Shading F) (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) (n : ℕ) : Shading F :=
  Y.restrictSet (statisticSlice Y stat n)
    (measurableSet_statisticSlice Y stat hstat n)

@[simp] theorem restrictStatisticLevel_carrier [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) (n : ℕ) (i : ι) :
    (restrictStatisticLevel Y stat hstat n).carrier i =
      Y.carrier i ∩ statisticSlice Y stat n :=
  rfl

theorem restrictStatisticLevel_shadedUnion [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) (n : ℕ) :
    (restrictStatisticLevel Y stat hstat n).shadedUnion =
      statisticSlice Y stat n := by
  rw [restrictStatisticLevel, Shading.restrictSet_shadedUnion]
  exact Set.inter_eq_right.mpr inter_subset_left

/-- The restricted shadings themselves form an exact finite decomposition of
the original shaded union. -/
theorem shadedUnion_eq_iUnion_restrictStatisticLevel [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ) (M : ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (hbound : ∀ x ∈ Y.shadedUnion, stat x ≤ M) :
    Y.shadedUnion =
      ⋃ n ∈ Finset.range (M + 1),
        (restrictStatisticLevel Y stat hstat n).shadedUnion := by
  simpa only [restrictStatisticLevel_shadedUnion] using
    shadedUnion_eq_iUnion_statisticSlice Y stat M hbound

/-- Exact union-volume decomposition stated directly using the restricted
shadings. -/
theorem volume_shadedUnion_eq_sum_restrictStatisticLevel [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ) (M : ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (hbound : ∀ x ∈ Y.shadedUnion, stat x ≤ M) :
    volume Y.shadedUnion =
      ∑ n ∈ Finset.range (M + 1),
        volume (restrictStatisticLevel Y stat hstat n).shadedUnion := by
  simpa only [restrictStatisticLevel_shadedUnion] using
    volume_shadedUnion_eq_sum_statisticSlice Y stat M hstat hbound

theorem restrictStatisticLevel_shadedUnion_subset [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) (n : ℕ) :
    (restrictStatisticLevel Y stat hstat n).shadedUnion ⊆ Y.shadedUnion := by
  rw [restrictStatisticLevel_shadedUnion]
  exact inter_subset_left

/-- The chosen statistic is constant on the restricted shaded union. -/
theorem statistic_eq_on_restrictStatisticLevel [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) (n : ℕ)
    {x : Space} (hx : x ∈ (restrictStatisticLevel Y stat hstat n).shadedUnion) :
    stat x = n := by
  rw [restrictStatisticLevel_shadedUnion] at hx
  exact hx.2

/-- Pointwise multiplicity of the restricted shading is the old multiplicity
on the selected statistic slice and zero elsewhere. -/
theorem pointMultiplicity_restrictStatisticLevel [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) (n : ℕ) (x : Space) :
    (restrictStatisticLevel Y stat hstat n).pointMultiplicity x =
      if x ∈ statisticSlice Y stat n then Y.pointMultiplicity x else 0 := by
  exact Shading.pointMultiplicity_restrictSet Y
    (statisticSlice Y stat n) (measurableSet_statisticSlice Y stat hstat n) x

/-- Pointwise first moments split exactly over all bounded statistic levels. -/
theorem pointMultiplicity_cast_eq_sum_restrictStatisticLevel [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ) (M : ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (hbound : ∀ x ∈ Y.shadedUnion, stat x ≤ M) (x : Space) :
    (Y.pointMultiplicity x : ℝ≥0∞) =
      ∑ n ∈ Finset.range (M + 1),
        ((restrictStatisticLevel Y stat hstat n).pointMultiplicity x : ℝ≥0∞) := by
  classical
  by_cases hx : x ∈ Y.shadedUnion
  · have hn : stat x ∈ Finset.range (M + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound x hx))
    rw [Finset.sum_eq_single (stat x)]
    · rw [pointMultiplicity_restrictStatisticLevel]
      simp [statisticSlice, hx]
    · intro n hnmem hne
      have hxnot : x ∉ statisticSlice Y stat n := by
        intro hxs
        exact hne hxs.2.symm
      simp [pointMultiplicity_restrictStatisticLevel, hxnot]
    · exact fun hnot => (hnot hn).elim
  · have hmzero : Y.pointMultiplicity x = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hx ((Y.pointMultiplicity_pos_iff_mem_shadedUnion x).mp hpos)
    simp [pointMultiplicity_restrictStatisticLevel, statisticSlice, hx, hmzero]

/-- Total shaded mass, with fine-index multiplicity retained, is the exact sum
of the masses of all level restrictions. -/
theorem shadingMass_eq_sum_restrictStatisticLevel [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ) (M : ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (hbound : ∀ x ∈ Y.shadedUnion, stat x ≤ M) :
    Y.shadingMass =
      ∑ n ∈ Finset.range (M + 1),
        (restrictStatisticLevel Y stat hstat n).shadingMass := by
  rw [← Y.lintegral_pointMultiplicity]
  calc
    (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ∂volume) =
        ∫⁻ x, ∑ n ∈ Finset.range (M + 1),
          ((restrictStatisticLevel Y stat hstat n).pointMultiplicity x : ℝ≥0∞)
          ∂volume := by
      congr 1
      funext x
      exact pointMultiplicity_cast_eq_sum_restrictStatisticLevel
        Y stat M hstat hbound x
    _ = ∑ n ∈ Finset.range (M + 1),
          ∫⁻ x, ((restrictStatisticLevel Y stat hstat n).pointMultiplicity x :
            ℝ≥0∞) ∂volume := by
      apply lintegral_finsetSum
      intro n hn
      exact measurable_pointMultiplicity
        (restrictStatisticLevel Y stat hstat n)
    _ = ∑ n ∈ Finset.range (M + 1),
          (restrictStatisticLevel Y stat hstat n).shadingMass := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (restrictStatisticLevel Y stat hstat n).lintegral_pointMultiplicity

/-- An actual bounded level retains at least a `1 / (M+1)` share of total
shaded mass, stated with no division. -/
theorem exists_restrictStatisticLevel_with_large_mass [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ) (M : ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (hbound : ∀ x ∈ Y.shadedUnion, stat x ≤ M) :
    ∃ n ∈ Finset.range (M + 1),
      Y.shadingMass ≤
          (M + 1) • (restrictStatisticLevel Y stat hstat n).shadingMass ∧
        ∀ x ∈ (restrictStatisticLevel Y stat hstat n).shadedUnion,
          stat x = n := by
  classical
  have hlevels : (Finset.range (M + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ M)⟩
  let w : ℕ → ℝ≥0∞ :=
    fun n => (restrictStatisticLevel Y stat hstat n).shadingMass
  obtain ⟨n, hn, hmax⟩ :=
    Finset.exists_max_image (Finset.range (M + 1)) w hlevels
  refine ⟨n, hn, ?_, ?_⟩
  · calc
      Y.shadingMass = ∑ k ∈ Finset.range (M + 1), w k := by
        simpa [w] using
          shadingMass_eq_sum_restrictStatisticLevel Y stat M hstat hbound
      _ ≤ (Finset.range (M + 1)).card • w n :=
        Finset.sum_le_card_nsmul _ w (w n) (fun k hk => hmax k hk)
      _ = (M + 1) • (restrictStatisticLevel Y stat hstat n).shadingMass := by
        rw [Finset.card_range]
  · intro x hx
    exact statistic_eq_on_restrictStatisticLevel Y stat hstat n hx

/-- Equality levels of any finite-family point multiplicity are measurable. -/
theorem measurableSet_pointMultiplicity_eq
    {α : Type*} [Fintype α] {G : ConvexFamily α}
    (Z : Shading G) (n : ℕ) :
    MeasurableSet {x | Z.pointMultiplicity x = n} := by
  have heq :
      {x | Z.pointMultiplicity x = n} =
        (fun x => (Z.pointMultiplicity x : ℝ≥0∞)) ⁻¹' {(n : ℝ≥0∞)} := by
    ext x
    simp
  rw [heq]
  exact (measurable_pointMultiplicity Z) (measurableSet_singleton _)

/-- The generic construction specializes definitionally to the existing fine
point-multiplicity restriction. -/
theorem restrictStatisticLevel_pointMultiplicity_eq [Fintype ι]
    (Y : Shading F) (n : ℕ) :
    restrictStatisticLevel Y Y.pointMultiplicity
        (measurableSet_pointMultiplicity_eq Y) n =
      Y.restrictMultiplicitySlice n := by
  rfl

/-- Generic level pigeonholing instantiated with fine point multiplicity. -/
theorem exists_finePointMultiplicityLevel [Fintype ι] (Y : Shading F) :
    ∃ n ∈ Finset.range (Fintype.card ι + 1),
      Y.shadingMass ≤
          (Fintype.card ι + 1) •
            (restrictStatisticLevel Y Y.pointMultiplicity
              (measurableSet_pointMultiplicity_eq Y) n).shadingMass ∧
        ∀ x ∈
            (restrictStatisticLevel Y Y.pointMultiplicity
              (measurableSet_pointMultiplicity_eq Y) n).shadedUnion,
          Y.pointMultiplicity x = n := by
  exact exists_restrictStatisticLevel_with_large_mass Y Y.pointMultiplicity
    (Fintype.card ι) (measurableSet_pointMultiplicity_eq Y)
    (fun x hx => Y.pointMultiplicity_le_card x)

/-- Two successive common spatial restrictions incur the product of their
finite level counts.  The second statistic may depend on the first selected
level; constancy from the first step is preserved because the second shading
is a refinement of the first. -/
theorem exists_twoStep_restrictStatisticLevel_with_large_mass [Fintype ι]
    (Y : Shading F)
    (stat₁ : Space → ℕ) (M : ℕ)
    (hstat₁ : ∀ n, MeasurableSet {x | stat₁ x = n})
    (hbound₁ : ∀ x ∈ Y.shadedUnion, stat₁ x ≤ M)
    (stat₂ : ℕ → Space → ℕ) (N : ℕ)
    (hstat₂ : ∀ n m, MeasurableSet {x | stat₂ n x = m})
    (hbound₂ : ∀ (n : ℕ) (x : Space),
      x ∈ (restrictStatisticLevel Y stat₁ hstat₁ n).shadedUnion →
        stat₂ n x ≤ N) :
    ∃ n₁ ∈ Finset.range (M + 1), ∃ n₂ ∈ Finset.range (N + 1),
      Y.shadingMass ≤ ((M + 1) * (N + 1)) •
        (restrictStatisticLevel
          (restrictStatisticLevel Y stat₁ hstat₁ n₁)
          (stat₂ n₁) (hstat₂ n₁) n₂).shadingMass ∧
      ∀ x ∈ (restrictStatisticLevel
          (restrictStatisticLevel Y stat₁ hstat₁ n₁)
          (stat₂ n₁) (hstat₂ n₁) n₂).shadedUnion,
        stat₁ x = n₁ ∧ stat₂ n₁ x = n₂ := by
  obtain ⟨n₁, hn₁, hmass₁, hconst₁⟩ :=
    exists_restrictStatisticLevel_with_large_mass
      Y stat₁ M hstat₁ hbound₁
  let Y₁ := restrictStatisticLevel Y stat₁ hstat₁ n₁
  obtain ⟨n₂, hn₂, hmass₂, hconst₂⟩ :=
    exists_restrictStatisticLevel_with_large_mass
      Y₁ (stat₂ n₁) N (hstat₂ n₁) (hbound₂ n₁)
  let Y₂ := restrictStatisticLevel Y₁ (stat₂ n₁) (hstat₂ n₁) n₂
  refine ⟨n₁, hn₁, n₂, hn₂, ?_, ?_⟩
  · calc
      Y.shadingMass ≤ (M + 1) • Y₁.shadingMass := by
        simpa [Y₁] using hmass₁
      _ ≤ (M + 1) • ((N + 1) • Y₂.shadingMass) := by
        gcongr
      _ = ((M + 1) * (N + 1)) • Y₂.shadingMass := by
        simpa [Nat.mul_comm] using
          (mul_nsmul Y₂.shadingMass (N + 1) (M + 1)).symm
      _ = ((M + 1) * (N + 1)) •
          (restrictStatisticLevel
            (restrictStatisticLevel Y stat₁ hstat₁ n₁)
            (stat₂ n₁) (hstat₂ n₁) n₂).shadingMass := by
        rfl
  · intro x hx
    have hxY₁ : x ∈ Y₁.shadedUnion := by
      exact restrictStatisticLevel_shadedUnion_subset
        Y₁ (stat₂ n₁) (hstat₂ n₁) n₂ hx
    exact ⟨hconst₁ x hxY₁, hconst₂ x (by simpa [Y₂] using hx)⟩
/-! ## Exact-induced and neighborhood-induced outer instances -/

variable {κ : Type*} {W : ConvexFamily κ}

/-- The first restriction used in both two-step multiplicity refinements. -/
def finePointMultiplicityLevel [Fintype ι] (Y : Shading F) (n : ℕ) :
    Shading F :=
  restrictStatisticLevel Y Y.pointMultiplicity
    (measurableSet_pointMultiplicity_eq Y) n

/-- Outer point multiplicity of the exact induced shading after selecting a
fine multiplicity level. -/
def inducedOuterPointStatistic [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (n : ℕ)
    (x : Space) : ℕ :=
  (P.inducedShading (finePointMultiplicityLevel Y n)).pointMultiplicity x

theorem measurableSet_inducedOuterPointStatistic_eq
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (n m : ℕ) :
    MeasurableSet {x | inducedOuterPointStatistic P Y n x = m} :=
  measurableSet_pointMultiplicity_eq
    (P.inducedShading (finePointMultiplicityLevel Y n)) m

theorem inducedOuterPointStatistic_le_card
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (n : ℕ) (x : Space) :
    inducedOuterPointStatistic P Y n x ≤ Fintype.card κ :=
  (P.inducedShading (finePointMultiplicityLevel Y n)).pointMultiplicity_le_card x

/-- The twice-restricted fine shading for the exact induced outer statistic. -/
def fineThenInducedOuterLevel
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (n m : ℕ) :
    Shading F :=
  restrictStatisticLevel (finePointMultiplicityLevel Y n)
    (inducedOuterPointStatistic P Y n)
    (measurableSet_inducedOuterPointStatistic_eq P Y n) m

/-- Fine then exact-induced outer point-multiplicity pigeonholing has the
product level loss and preserves both selected constants. -/
theorem exists_fine_then_inducedOuterPointMultiplicityLevels
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) :
    ∃ n ∈ Finset.range (Fintype.card ι + 1),
      ∃ m ∈ Finset.range (Fintype.card κ + 1),
        Y.shadingMass ≤
          ((Fintype.card ι + 1) * (Fintype.card κ + 1)) •
            (fineThenInducedOuterLevel P Y n m).shadingMass ∧
        ∀ x ∈ (fineThenInducedOuterLevel P Y n m).shadedUnion,
          Y.pointMultiplicity x = n ∧
            (P.inducedShading (finePointMultiplicityLevel Y n)).pointMultiplicity x = m := by
  simpa [finePointMultiplicityLevel, inducedOuterPointStatistic,
    fineThenInducedOuterLevel] using
    (exists_twoStep_restrictStatisticLevel_with_large_mass
      Y Y.pointMultiplicity (Fintype.card ι)
      (measurableSet_pointMultiplicity_eq Y)
      (fun x hx => Y.pointMultiplicity_le_card x)
      (inducedOuterPointStatistic P Y)
      (Fintype.card κ)
      (measurableSet_inducedOuterPointStatistic_eq P Y)
      (fun n x hx => inducedOuterPointStatistic_le_card P Y n x))

/-- The exact-induced statistic is the existing occurrence outer
multiplicity. -/
theorem inducedOuterPointStatistic_eq_outerMultiplicity
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (n : ℕ) (x : Space) :
    inducedOuterPointStatistic P Y n x =
      P.outerMultiplicity (finePointMultiplicityLevel Y n) x :=
  P.pointMultiplicity_inducedShading_eq_outer
    (finePointMultiplicityLevel Y n) x

/-- Membership in a neighborhood-induced carrier forces its coarse index to
be active.  This also covers nonpositive radii: an inactive fiber union is
empty, hence so is its thickening. -/
theorem mem_coarse_of_mem_neighborhoodInducedShading
    [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ)
    {k : κ} {x : Space}
    (hx : x ∈ (P.neighborhoodInducedShading Y r).carrier k) :
    k ∈ P.index.coarse := by
  obtain ⟨_hxW, y, hyFiber, _hxy⟩ :=
    (P.mem_neighborhoodInducedShading_carrier_iff Y r k x).1 hx
  obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyFiber
  have hiFine : i.1 ∈ P.index.fine :=
    P.index.fiber_subset_fine k i.2
  have hiParent : P.index.parent i.1 = k :=
    (P.index.mem_fiber i.1 k).1 i.2 |>.2
  simpa [hiParent] using P.index.parent_mem i.1 hiFine

/-- With finite coarse indices, neighborhood outer multiplicity is exactly the
ordinary point multiplicity of the neighborhood-induced shading. -/
theorem pointMultiplicity_neighborhoodInducedShading_eq_outer
    [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) (x : Space) :
    (P.neighborhoodInducedShading Y r).pointMultiplicity x =
      P.neighborhoodOuterMultiplicity Y r x := by
  classical
  unfold Shading.pointMultiplicity ConvexFactorization.neighborhoodOuterMultiplicity
  apply congrArg Finset.card
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    exact ⟨mem_coarse_of_mem_neighborhoodInducedShading P Y r hx, hx⟩
  · exact fun hx => hx.2

/-- Neighborhood-induced outer point multiplicity after selecting a fine
multiplicity level. -/
def neighborhoodOuterPointStatistic
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) (n : ℕ)
    (x : Space) : ℕ :=
  (P.neighborhoodInducedShading
    (finePointMultiplicityLevel Y n) r).pointMultiplicity x

theorem measurableSet_neighborhoodOuterPointStatistic_eq
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) (n m : ℕ) :
    MeasurableSet {x | neighborhoodOuterPointStatistic P Y r n x = m} :=
  measurableSet_pointMultiplicity_eq
    (P.neighborhoodInducedShading (finePointMultiplicityLevel Y n) r) m

theorem neighborhoodOuterPointStatistic_le_card
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ)
    (n : ℕ) (x : Space) :
    neighborhoodOuterPointStatistic P Y r n x ≤ Fintype.card κ :=
  (P.neighborhoodInducedShading
    (finePointMultiplicityLevel Y n) r).pointMultiplicity_le_card x

/-- The twice-restricted fine shading for the neighborhood-induced outer
statistic. -/
def fineThenNeighborhoodOuterLevel
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ)
    (n m : ℕ) : Shading F :=
  restrictStatisticLevel (finePointMultiplicityLevel Y n)
    (neighborhoodOuterPointStatistic P Y r n)
    (measurableSet_neighborhoodOuterPointStatistic_eq P Y r n) m

/-- Fine then neighborhood-induced outer point-multiplicity pigeonholing has
the same product loss and preserves both selected constants. -/
theorem exists_fine_then_neighborhoodOuterPointMultiplicityLevels
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) :
    ∃ n ∈ Finset.range (Fintype.card ι + 1),
      ∃ m ∈ Finset.range (Fintype.card κ + 1),
        Y.shadingMass ≤
          ((Fintype.card ι + 1) * (Fintype.card κ + 1)) •
            (fineThenNeighborhoodOuterLevel P Y r n m).shadingMass ∧
        ∀ x ∈ (fineThenNeighborhoodOuterLevel P Y r n m).shadedUnion,
          Y.pointMultiplicity x = n ∧
            (P.neighborhoodInducedShading
              (finePointMultiplicityLevel Y n) r).pointMultiplicity x = m := by
  simpa [finePointMultiplicityLevel, neighborhoodOuterPointStatistic,
    fineThenNeighborhoodOuterLevel] using
    (exists_twoStep_restrictStatisticLevel_with_large_mass
      Y Y.pointMultiplicity (Fintype.card ι)
      (measurableSet_pointMultiplicity_eq Y)
      (fun x hx => Y.pointMultiplicity_le_card x)
      (neighborhoodOuterPointStatistic P Y r)
      (Fintype.card κ)
      (measurableSet_neighborhoodOuterPointStatistic_eq P Y r)
      (fun n x hx => neighborhoodOuterPointStatistic_le_card P Y r n x))

theorem neighborhoodOuterPointStatistic_eq_outerMultiplicity
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ)
    (n : ℕ) (x : Space) :
    neighborhoodOuterPointStatistic P Y r n x =
      P.neighborhoodOuterMultiplicity (finePointMultiplicityLevel Y n) r x :=
  pointMultiplicity_neighborhoodInducedShading_eq_outer
    P (finePointMultiplicityLevel Y n) r x
/-! ## Recomputing outer statistics after a common restriction -/

/-- Fiber shaded unions commute exactly with a common spatial restriction. -/
theorem fiberShadedUnion_restrictSet
    [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (k : κ) :
    P.fiberShadedUnion (Y.restrictSet Ω hΩ) k =
      P.fiberShadedUnion Y k ∩ Ω := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact ⟨Set.mem_iUnion.mpr ⟨i, hxi.1⟩, hxi.2⟩
  · rintro ⟨hxFiber, hxΩ⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxFiber
    exact Set.mem_iUnion.mpr ⟨i, hxi, hxΩ⟩

/-- Exact induced coarse carriers commute with common spatial restriction. -/
theorem inducedShading_restrictSet_carrier
    [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (k : κ) :
    (P.inducedShading (Y.restrictSet Ω hΩ)).carrier k =
      (P.inducedShading Y).carrier k ∩ Ω := by
  rw [P.inducedShading_carrier_eq_fiberShadedUnion,
    P.inducedShading_carrier_eq_fiberShadedUnion,
    fiberShadedUnion_restrictSet]

/-- Consequently exact induced point multiplicity is unchanged on the
restriction set and zero off it. -/
theorem pointMultiplicity_inducedShading_restrictSet
    [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (x : Space) :
    (P.inducedShading (Y.restrictSet Ω hΩ)).pointMultiplicity x =
      if x ∈ Ω then (P.inducedShading Y).pointMultiplicity x else 0 := by
  classical
  unfold Shading.pointMultiplicity
  by_cases hx : x ∈ Ω
  · rw [if_pos hx]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [inducedShading_restrictSet_carrier]
    simp [hx]
  · rw [if_neg hx, Finset.card_eq_zero]
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [inducedShading_restrictSet_carrier]
    simp [hx]

/-- The exact-induced outer multiplicity selected in the second step remains
the same when it is recomputed from the final twice-restricted shading. -/
theorem recomputed_inducedOuterPointMultiplicity_eq
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (n m : ℕ)
    {x : Space} (hx : x ∈ (fineThenInducedOuterLevel P Y n m).shadedUnion) :
    (P.inducedShading (fineThenInducedOuterLevel P Y n m)).pointMultiplicity x =
      inducedOuterPointStatistic P Y n x := by
  have hxLevel :
      x ∈ statisticSlice (finePointMultiplicityLevel Y n)
        (inducedOuterPointStatistic P Y n) m := by
    rw [fineThenInducedOuterLevel, restrictStatisticLevel_shadedUnion] at hx
    exact hx
  simpa [fineThenInducedOuterLevel, restrictStatisticLevel,
    inducedOuterPointStatistic, hxLevel] using
    (pointMultiplicity_inducedShading_restrictSet P
      (finePointMultiplicityLevel Y n)
      (statisticSlice (finePointMultiplicityLevel Y n)
        (inducedOuterPointStatistic P Y n) m)
      (measurableSet_statisticSlice
        (finePointMultiplicityLevel Y n)
        (inducedOuterPointStatistic P Y n)
        (measurableSet_inducedOuterPointStatistic_eq P Y n) m) x)

/-- The exact-induced two-step result can therefore state outer uniformity for
the final recomputed induced shading, not only for the frozen intermediate
statistic. -/
theorem exists_fine_then_recomputedInducedOuterPointMultiplicityLevels
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) :
    ∃ n ∈ Finset.range (Fintype.card ι + 1),
      ∃ m ∈ Finset.range (Fintype.card κ + 1),
        Y.shadingMass ≤
          ((Fintype.card ι + 1) * (Fintype.card κ + 1)) •
            (fineThenInducedOuterLevel P Y n m).shadingMass ∧
        ∀ x ∈ (fineThenInducedOuterLevel P Y n m).shadedUnion,
          Y.pointMultiplicity x = n ∧
            (P.inducedShading
              (fineThenInducedOuterLevel P Y n m)).pointMultiplicity x = m := by
  obtain ⟨n, hn, m, hm, hmass, hconst⟩ :=
    exists_fine_then_inducedOuterPointMultiplicityLevels P Y
  refine ⟨n, hn, m, hm, hmass, ?_⟩
  intro x hx
  refine ⟨(hconst x hx).1, ?_⟩
  rw [recomputed_inducedOuterPointMultiplicity_eq P Y n m hx]
  exact (hconst x hx).2

/-- Recomputing a neighborhood-induced shading after any common restriction
can only decrease each coarse carrier.  Unlike exact unions, thickening does
not in general commute with intersection. -/
theorem neighborhoodInducedShading_restrictSet_carrier_subset
    [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (r : ℝ) (k : κ) :
    (P.neighborhoodInducedShading (Y.restrictSet Ω hΩ) r).carrier k ⊆
      (P.neighborhoodInducedShading Y r).carrier k := by
  rw [P.neighborhoodInducedShading_carrier,
    P.neighborhoodInducedShading_carrier,
    fiberShadedUnion_restrictSet]
  intro x hx
  exact ⟨hx.1,
    Metric.thickening_subset_of_subset r inter_subset_left hx.2⟩

theorem pointMultiplicity_neighborhoodInducedShading_restrictSet_le
    [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (r : ℝ) (x : Space) :
    (P.neighborhoodInducedShading (Y.restrictSet Ω hΩ) r).pointMultiplicity x ≤
      (P.neighborhoodInducedShading Y r).pointMultiplicity x := by
  classical
  unfold Shading.pointMultiplicity
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1,
    neighborhoodInducedShading_restrictSet_carrier_subset
      P Y Ω hΩ r k hk.2⟩

/-- Thus the neighborhood outer statistic recomputed from the final shading is
controlled by the selected intermediate level.  Equality needs an additional
neighborhood-saturation/stable-witness hypothesis. -/
theorem recomputed_neighborhoodOuterPointMultiplicity_le
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ)
    (n m : ℕ) (x : Space) :
    (P.neighborhoodInducedShading
      (fineThenNeighborhoodOuterLevel P Y r n m) r).pointMultiplicity x ≤
        neighborhoodOuterPointStatistic P Y r n x := by
  exact pointMultiplicity_neighborhoodInducedShading_restrictSet_le
    P (finePointMultiplicityLevel Y n)
    (statisticSlice (finePointMultiplicityLevel Y n)
      (neighborhoodOuterPointStatistic P Y r n) m)
    (measurableSet_statisticSlice
      (finePointMultiplicityLevel Y n)
      (neighborhoodOuterPointStatistic P Y r n)
      (measurableSet_neighborhoodOuterPointStatistic_eq P Y r n) m)
    r x
/-! ## Carrier-indexed statistics (fiber multiplicity interface) -/

/-- A level slice whose statistic may depend on the carrier index. -/
def carrierStatisticSlice (Y : Shading F) (stat : ι → Space → ℕ)
    (i : ι) (n : ℕ) : Set Space :=
  Y.carrier i ∩ {x | stat i x = n}

theorem measurableSet_carrierStatisticSlice
    (Y : Shading F) (stat : ι → Space → ℕ)
    (hstat : ∀ i n, MeasurableSet {x | stat i x = n})
    (i : ι) (n : ℕ) :
    MeasurableSet (carrierStatisticSlice Y stat i n) :=
  (Y.measurable_carrier i).inter (hstat i n)

theorem carrierStatisticSlice_disjoint
    (Y : Shading F) (stat : ι → Space → ℕ) (i : ι)
    {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (carrierStatisticSlice Y stat i m)
      (carrierStatisticSlice Y stat i n) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  exact hmn (hxm.2.symm.trans hxn.2)

/-- Each carrier is exactly partitioned by the bounded levels of its own
index-dependent statistic. -/
theorem carrier_eq_iUnion_carrierStatisticSlice
    (Y : Shading F) (stat : ι → Space → ℕ) (M : ℕ)
    (hbound : ∀ (i : ι) (x : Space),
      x ∈ Y.carrier i → stat i x ≤ M) (i : ι) :
    Y.carrier i =
      ⋃ n ∈ Finset.range (M + 1), carrierStatisticSlice Y stat i n := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.mpr ⟨stat i x, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ?_, hx, rfl⟩
    exact Nat.lt_succ_of_le (hbound i x hx)
  · intro hx
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_hn, hxn⟩ := Set.mem_iUnion.mp hx
    exact hxn.1

theorem volume_carrier_eq_sum_carrierStatisticSlice
    (Y : Shading F) (stat : ι → Space → ℕ) (M : ℕ)
    (hstat : ∀ i n, MeasurableSet {x | stat i x = n})
    (hbound : ∀ (i : ι) (x : Space),
      x ∈ Y.carrier i → stat i x ≤ M) (i : ι) :
    volume (Y.carrier i) =
      ∑ n ∈ Finset.range (M + 1),
        volume (carrierStatisticSlice Y stat i n) := by
  rw [carrier_eq_iUnion_carrierStatisticSlice Y stat M hbound i]
  exact measure_biUnion_finset
    (fun m hm n hn hmn => carrierStatisticSlice_disjoint Y stat i hmn)
    (fun n hn => measurableSet_carrierStatisticSlice Y stat hstat i n)

/-- Restrict each carrier by the same level, while allowing the statistic
itself to depend on the carrier index. -/
def restrictCarrierStatisticLevel (Y : Shading F) (stat : ι → Space → ℕ)
    (hstat : ∀ i n, MeasurableSet {x | stat i x = n}) (n : ℕ) :
    Shading F where
  carrier i := carrierStatisticSlice Y stat i n
  measurable_carrier i :=
    measurableSet_carrierStatisticSlice Y stat hstat i n
  carrier_subset i :=
    (inter_subset_left : carrierStatisticSlice Y stat i n ⊆ Y.carrier i).trans
      (Y.carrier_subset i)

@[simp] theorem restrictCarrierStatisticLevel_carrier
    (Y : Shading F) (stat : ι → Space → ℕ)
    (hstat : ∀ i n, MeasurableSet {x | stat i x = n})
    (n : ℕ) (i : ι) :
    (restrictCarrierStatisticLevel Y stat hstat n).carrier i =
      carrierStatisticSlice Y stat i n :=
  rfl

theorem restrictCarrierStatisticLevel_shadedUnion_subset
    (Y : Shading F) (stat : ι → Space → ℕ)
    (hstat : ∀ i n, MeasurableSet {x | stat i x = n}) (n : ℕ) :
    (restrictCarrierStatisticLevel Y stat hstat n).shadedUnion ⊆
      Y.shadedUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i, hxi.1⟩

/-- Exact mass decomposition remains valid for carrier-indexed statistics. -/
theorem shadingMass_eq_sum_restrictCarrierStatisticLevel [Fintype ι]
    (Y : Shading F) (stat : ι → Space → ℕ) (M : ℕ)
    (hstat : ∀ i n, MeasurableSet {x | stat i x = n})
    (hbound : ∀ (i : ι) (x : Space),
      x ∈ Y.carrier i → stat i x ≤ M) :
    Y.shadingMass =
      ∑ n ∈ Finset.range (M + 1),
        (restrictCarrierStatisticLevel Y stat hstat n).shadingMass := by
  classical
  unfold Shading.shadingMass
  calc
    (∑ i : ι, volume (Y.carrier i)) =
        ∑ i : ι, ∑ n ∈ Finset.range (M + 1),
          volume (carrierStatisticSlice Y stat i n) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact volume_carrier_eq_sum_carrierStatisticSlice
        Y stat M hstat hbound i
    _ = ∑ n ∈ Finset.range (M + 1), ∑ i : ι,
          volume (carrierStatisticSlice Y stat i n) := by
      simpa using
        (Finset.sum_comm (s := Finset.univ)
          (t := Finset.range (M + 1))
          (f := fun i n => volume (carrierStatisticSlice Y stat i n)))
    _ = ∑ n ∈ Finset.range (M + 1),
        (restrictCarrierStatisticLevel Y stat hstat n).shadingMass := by
      rfl

/-- A genuine common level can be chosen even for carrier-indexed statistics,
with the same division-free `M+1` loss. -/
theorem exists_restrictCarrierStatisticLevel_with_large_mass [Fintype ι]
    (Y : Shading F) (stat : ι → Space → ℕ) (M : ℕ)
    (hstat : ∀ i n, MeasurableSet {x | stat i x = n})
    (hbound : ∀ (i : ι) (x : Space),
      x ∈ Y.carrier i → stat i x ≤ M) :
    ∃ n ∈ Finset.range (M + 1),
      Y.shadingMass ≤
        (M + 1) • (restrictCarrierStatisticLevel Y stat hstat n).shadingMass ∧
      ∀ (i : ι) (x : Space),
        x ∈ (restrictCarrierStatisticLevel Y stat hstat n).carrier i →
        stat i x = n := by
  classical
  have hlevels : (Finset.range (M + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ M)⟩
  let w : ℕ → ℝ≥0∞ :=
    fun n => (restrictCarrierStatisticLevel Y stat hstat n).shadingMass
  obtain ⟨n, hn, hmax⟩ :=
    Finset.exists_max_image (Finset.range (M + 1)) w hlevels
  refine ⟨n, hn, ?_, ?_⟩
  · calc
      Y.shadingMass = ∑ k ∈ Finset.range (M + 1), w k := by
        simpa [w] using
          shadingMass_eq_sum_restrictCarrierStatisticLevel
            Y stat M hstat hbound
      _ ≤ (Finset.range (M + 1)).card • w n :=
        Finset.sum_le_card_nsmul _ w (w n) (fun k hk => hmax k hk)
      _ = (M + 1) •
          (restrictCarrierStatisticLevel Y stat hstat n).shadingMass := by
        rw [Finset.card_range]
  · intro i x hx
    exact hx.2

/-- The ENNReal cast of one fiber multiplicity is measurable. -/
theorem measurable_fiberMultiplicity_cast
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    Measurable fun x => (P.fiberMultiplicity Y k x : ℝ≥0∞) := by
  classical
  have hpoint (x : Space) :
      (P.fiberMultiplicity Y k x : ℝ≥0∞) =
        ∑ i ∈ P.index.fiber k,
          (Y.carrier i).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    simp [ConvexFactorization.fiberMultiplicity, Set.indicator_apply]
  simp_rw [hpoint]
  apply Finset.measurable_fun_sum
  intro i hi
  exact measurable_const.indicator (Y.measurable_carrier i)

theorem measurableSet_fiberMultiplicity_eq
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) (n : ℕ) :
    MeasurableSet {x | P.fiberMultiplicity Y k x = n} := by
  have heq :
      {x | P.fiberMultiplicity Y k x = n} =
        (fun x => (P.fiberMultiplicity Y k x : ℝ≥0∞)) ⁻¹'
          {(n : ℝ≥0∞)} := by
    ext x
    simp
  rw [heq]
  exact (measurable_fiberMultiplicity_cast P Y k)
    (measurableSet_singleton _)

theorem fiberMultiplicity_le_card
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) (x : Space) :
    P.fiberMultiplicity Y k x ≤ Fintype.card ι := by
  classical
  unfold ConvexFactorization.fiberMultiplicity
  exact Finset.card_le_card
    ((Finset.filter_subset _ _).trans (Finset.subset_univ _))

/-- The fiber statistic relevant to a fine carrier uses that carrier's parent
coarse index. -/
def parentFiberPointStatistic
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F)
    (i : ι) (x : Space) : ℕ :=
  P.fiberMultiplicity Y (P.index.parent i) x

theorem measurableSet_parentFiberPointStatistic_eq
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) (i : ι) (n : ℕ) :
    MeasurableSet {x | parentFiberPointStatistic P Y i x = n} :=
  measurableSet_fiberMultiplicity_eq P Y (P.index.parent i) n

/-- A single actual level uniformizes parent-fiber multiplicity on every
retained carrier, losing at most `card ι + 1` in active shaded mass. -/
theorem exists_parentFiberPointMultiplicityLevel
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (P : ConvexFactorization F W) (Y : Shading F) :
    ∃ n ∈ Finset.range (Fintype.card ι + 1),
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≤
        (Fintype.card ι + 1) •
          (restrictCarrierStatisticLevel
            (IndexedShadingRefinement.restrictTo Y P.index.fine).shading
            (parentFiberPointStatistic P Y)
            (measurableSet_parentFiberPointStatistic_eq P Y) n).shadingMass ∧
      ∀ (i : ι) (x : Space),
        x ∈
          (restrictCarrierStatisticLevel
            (IndexedShadingRefinement.restrictTo Y P.index.fine).shading
            (parentFiberPointStatistic P Y)
            (measurableSet_parentFiberPointStatistic_eq P Y) n).carrier i →
        P.fiberMultiplicity Y (P.index.parent i) x = n := by
  apply exists_restrictCarrierStatisticLevel_with_large_mass
  intro i x hx
  exact fiberMultiplicity_le_card P Y (P.index.parent i) x
end StatisticLevelRestriction

end

end Submission.Kakeya.ConvexFactoring

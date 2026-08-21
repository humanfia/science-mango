import Submission.Kakeya.ConvexFactoring.Refinement
import Submission.Kakeya.Uniformity.Pigeonhole

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

/-!
# Quantitative refinements

The predicates in this file deliberately record loss by cross multiplication.
This avoids all zero and infinity side conditions associated with division in
`ENNReal`.
-/

/-- `retained` keeps at least a `1 / loss` fraction of `original`, expressed
without division. -/
def WithinFactor (loss : ℕ) (original retained : ℝ≥0∞) : Prop :=
  original ≤ loss • retained

/-- The `NNReal` form of quantitative retention, used by weighted finite
pigeonholing. -/
def RetainsBy (loss : ℕ) (original retained : ℝ≥0) : Prop :=
  original ≤ loss • retained

/-- Quantitative retention composes multiplicatively. -/
theorem WithinFactor.trans {a b c : ℝ≥0∞} {m n : ℕ}
    (hab : WithinFactor m a b) (hbc : WithinFactor n b c) :
    WithinFactor (m * n) a c := by
  unfold WithinFactor at *
  calc
    a ≤ m • b := hab
    _ ≤ m • (n • c) := nsmul_le_nsmul_right hbc m
    _ = (m * n) • c := by
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ac_rfl

/-- Every shaded piece has finite volume, since it lies in a compact convex
body. -/
theorem shadingPiece_volume_lt_top {ι : Type*} {F : ConvexFamily ι}
    (Y : Shading F) (i : ι) : volume (Y.carrier i) < ∞ :=
  (measure_mono (Y.carrier_subset i)).trans_lt (F i).isCompact.measure_lt_top

/-- The finite `NNReal` weight of one shaded piece. -/
noncomputable def shadingWeight {ι : Type*} {F : ConvexFamily ι}
    (Y : Shading F) (i : ι) : ℝ≥0 :=
  (volume (Y.carrier i)).toNNReal

@[simp]
theorem coe_shadingWeight {ι : Type*} {F : ConvexFamily ι}
    (Y : Shading F) (i : ι) :
    (shadingWeight Y i : ℝ≥0∞) = volume (Y.carrier i) := by
  exact ENNReal.coe_toNNReal (shadingPiece_volume_lt_top Y i).ne

/-- Restriction to a finite set has exactly the mass of the corresponding
finite subsum. -/
theorem shadingMass_restrictTo_eq_sum {ι : Type*} [DecidableEq ι] [Fintype ι]
    {F : ConvexFamily ι} (Y : Shading F) (s : Finset ι) :
    (IndexedShadingRefinement.restrictTo Y s).shading.shadingMass =
      ∑ i ∈ s, volume (Y.carrier i) := by
  classical
  unfold Shading.shadingMass
  calc
    (∑ i, volume
        ((IndexedShadingRefinement.restrictTo Y s).shading.carrier i)) =
        ∑ i, if i ∈ s then volume (Y.carrier i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [IndexedShadingRefinement.restrictTo_carrier]
      split_ifs <;> simp_all
    _ = ∑ i ∈ s, volume (Y.carrier i) := by
      rw [← Finset.sum_filter]
      simp

/-- Total shaded mass is the coercion of the sum of the finite piece weights. -/
theorem shadingMass_eq_coe_sum_shadingWeight
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {F : ConvexFamily ι} (Y : Shading F) :
    Y.shadingMass = (↑(∑ i, shadingWeight Y i) : ℝ≥0∞) := by
  rw [Shading.shadingMass, ENNReal.ofNNReal_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  exact (coe_shadingWeight Y i).symm

/-- The mass of a restriction is the coercion of the corresponding `NNReal`
weight subsum. -/
theorem shadingMass_restrictTo_eq_coe_sum_shadingWeight
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {F : ConvexFamily ι} (Y : Shading F) (s : Finset ι) :
    (IndexedShadingRefinement.restrictTo Y s).shading.shadingMass =
      (↑(∑ i ∈ s, shadingWeight Y i) : ℝ≥0∞) := by
  rw [shadingMass_restrictTo_eq_sum, ENNReal.ofNNReal_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  exact (coe_shadingWeight Y i).symm

/-- A pointwise quantitative subshading estimate sums to the same quantitative
estimate for total shading mass. -/
theorem shadingMass_withinFactor_of_piecewise
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {F : ConvexFamily ι} {Y : Shading F}
    (R : IndexedShadingRefinement Y) (loss : ℕ)
    (hpiece : ∀ i, volume (Y.carrier i) ≤
      loss • volume (R.shading.carrier i)) :
    WithinFactor loss Y.shadingMass R.shading.shadingMass := by
  unfold WithinFactor Shading.shadingMass
  calc
    (∑ i, volume (Y.carrier i)) ≤
        ∑ i, loss • volume (R.shading.carrier i) :=
      Finset.sum_le_sum fun i _ ↦ hpiece i
    _ = loss • ∑ i, volume (R.shading.carrier i) := by
      simp only [nsmul_eq_mul]
      exact (Finset.mul_sum Finset.univ _ _).symm

/-- Weighted finite pigeonholing, packaged using the explicit cross-multiplied
retention predicate. -/
theorem exists_weighted_bucket_retaining
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    [Fintype β] [Nonempty β]
    (s : Finset ι) (bucket : ι → β) (w : ι → ℝ≥0) :
    ∃ b : β,
      RetainsBy (Fintype.card β) (∑ i ∈ s, w i)
        (∑ i ∈ dyadicFiber s bucket b, w i) := by
  simpa [RetainsBy] using exists_large_weighted_fiber s bucket w

/-- Some bucket restriction retains at least the reciprocal of the number of
buckets of the original shading mass. The conclusion is in `ENNReal`, but the
pigeonhole argument runs through the finite `NNReal` weights of the pieces. -/
theorem exists_bucket_restriction_withinFactor
    {ι β : Type*} [DecidableEq ι] [Fintype ι]
    [DecidableEq β] [Fintype β] [Nonempty β]
    {F : ConvexFamily ι} (Y : Shading F) (bucket : ι → β) :
    ∃ b : β,
      WithinFactor (Fintype.card β) Y.shadingMass
        (IndexedShadingRefinement.restrictTo Y
          (dyadicFiber Finset.univ bucket b)).shading.shadingMass := by
  obtain ⟨b, hb⟩ := exists_weighted_bucket_retaining
    (Finset.univ : Finset ι) bucket (shadingWeight Y)
  refine ⟨b, ?_⟩
  unfold WithinFactor
  rw [shadingMass_eq_coe_sum_shadingWeight,
    shadingMass_restrictTo_eq_coe_sum_shadingWeight]
  exact_mod_cast hb

end Submission.Kakeya.ConvexFactoring

import Submission.Kakeya.ConvexFactoring.L2Union

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

/-!
# Lemma 6.9: analytic union-volume seam

This file isolates the division-free analytic implication needed after the
geometric overlap estimate in the large-`b` branch of Lemma 6.9.  It does not
assert that the geometric overlap budget itself has been proved.
-/

/-- A cross-multiplied overlap budget gives the corresponding shaded-union
volume floor.  The overlap sum is automatically finite because every shaded
piece lies in a compact convex body; its nonvanishing follows from the
nonzero shading mass and the Cordoba `L²` inequality. -/
theorem lemma69_union_of_overlapBudget
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι} (Y : Shading F)
    {L : ENNReal}
    (hMass : Y.shadingMass ≠ 0)
    (hBudget :
      L * (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
        Y.shadingMass ^ 2) :
    L ≤ volume Y.shadedUnion := by
  classical
  let overlapSum : ENNReal :=
    ∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)
  have hCordoba :
      Y.shadingMass ^ 2 ≤ volume Y.shadedUnion * overlapSum := by
    simpa [overlapSum] using
      shadingMass_sq_le_volume_shadedUnion_mul_overlapSum Y
  have hOverlapZero : overlapSum ≠ 0 := by
    intro hZero
    have hMassSqZero : Y.shadingMass ^ 2 ≤ 0 := by
      simpa [hZero] using hCordoba
    exact (pow_ne_zero 2 hMass) (bot_unique hMassSqZero)
  have hOverlapTop : overlapSum ≠ ∞ := by
    dsimp [overlapSum]
    apply ENNReal.sum_ne_top.mpr
    intro i _hi
    apply ENNReal.sum_ne_top.mpr
    intro j _hj
    exact ((measure_mono fun x hx ↦ Y.carrier_subset i hx.1).trans_lt
      (F i).isCompact.measure_lt_top).ne
  have hBudget' : L * overlapSum ≤ Y.shadingMass ^ 2 := by
    simpa [overlapSum] using hBudget
  have hProduct :
      L * overlapSum ≤ volume Y.shadedUnion * overlapSum :=
    hBudget'.trans hCordoba
  exact (ENNReal.mul_le_mul_iff_left hOverlapZero hOverlapTop).mp hProduct

end Submission.Kakeya.ConvexFactoring

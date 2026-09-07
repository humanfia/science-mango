import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import Mathlib.Tactic

/-!
# Cardinal Convex Wolff control implies mass Frostman control

The paper's Convex Wolff condition counts contained members.  If every member
has volume between a common lower and upper scale, cardinal control becomes
a Katz--Tao mass estimate.  A containing ambient body of bounded volume then
turns that estimate into the cross-multiplied Frostman condition.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CardinalCWAFrostmanInV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6CanonicalFrostmanConstantCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2

noncomputable section

universe u

/-- A cardinal-normalized CWA becomes a Frostman certificate once the
member volumes are uniformly comparable and the ambient volume is bounded.
No division by the member-volume lower bound occurs. -/
theorem isFrostmanIn_of_cwa_volume_bounds
    {index : Type u} [Fintype index]
    (F : ConvexFamily index) (ambient : ConvexBody Space)
    {C lower upper comparison ambientVolume : ENNReal}
    (hCWA : SatisfiesConvexWolffAxioms C F)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hlower : ∀ i, lower ≤ volume (F i : Set Space))
    (hupper : ∀ i, volume (F i : Set Space) ≤ upper)
    (hcomparison : upper ≤ comparison * lower)
    (hambient : volume (ambient : Set Space) ≤ ambientVolume) :
    IsFrostmanIn (C * comparison * ambientVolume) F ambient := by
  let n : ENNReal := Fintype.card index
  have hKT : IsKatzTao (C * n * upper) F := by
    intro K
    unfold IsKatzTaoAt
    calc
      containedMass F K ≤
          ((containedIndices F K).card : ENNReal) * upper := by
        classical
        unfold containedMass
        calc
          (∑ i ∈ containedIndices F K, volume (F i : Set Space)) ≤
              ∑ _i ∈ containedIndices F K, upper := by
            apply Finset.sum_le_sum
            intro i _hi
            exact hupper i
          _ = ((containedIndices F K).card : ENNReal) * upper := by
            simp
      _ ≤ (C * volume (K : Set Space) * n) * upper := by
        gcongr
        exact hCWA K
      _ = (C * n * upper) * volume (K : Set Space) := by
        ac_rfl
  have hfamilyLower : n * lower ≤ familyVolume F := by
    classical
    unfold n familyVolume
    calc
      (Fintype.card index : ENNReal) * lower =
          ∑ _i : index, lower := by simp
      _ ≤ ∑ i : index, volume (F i : Set Space) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hlower i
  apply hKT.isFrostmanIn hcontained
  rw [containedMass_eq_familyVolume_of_contained F ambient hcontained]
  calc
    (C * n * upper) * volume (ambient : Set Space) ≤
        (C * n * (comparison * lower)) * ambientVolume := by
      exact mul_le_mul'
        (mul_le_mul' le_rfl hcomparison) hambient
    _ = (C * comparison * ambientVolume) * (n * lower) := by
      ac_rfl
    _ ≤ (C * comparison * ambientVolume) * familyVolume F := by
      gcongr

#print axioms isFrostmanIn_of_cwa_volume_bounds

end
end Family8CardinalCWAFrostmanInV1

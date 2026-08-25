import Submission.Kakeya.ConvexFactoring.NonConcentration

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyFiniteFamilyMaximalConcentrationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring

noncomputable section

/-!
# Cardinal finiteness of maximal concentration

For a finite indexed convex family, every member counted inside a test body
has volume at most that body's volume.  Thus the contained mass is at most the
number of indices times the test volume.  This cross-multiplied argument also
covers zero-volume test bodies and gives a completely automatic finite bound
for `maximalConcentration`.
-/

variable {index : Type*} [Fintype index]

/-- The crude but uniform cardinal Katz--Tao estimate, written directly for
the quotient-valued concentration. -/
theorem concentration_le_card
    (F : ConvexFamily index) (K : ConvexBody Space) :
    concentration F K <= (Fintype.card index : ENNReal) := by
  rw [concentration_eq_containedMass_div]
  apply ENNReal.div_le_of_le_mul
  unfold containedMass
  calc
    (∑ i ∈ containedIndices F K, volume (F i : Set Space)) <=
        ∑ _i ∈ containedIndices F K, volume (K : Set Space) := by
      apply Finset.sum_le_sum
      intro i hi
      exact measure_mono ((mem_containedIndices F K i).1 hi)
    _ = ((containedIndices F K).card : ENNReal) *
        volume (K : Set Space) := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    _ <= (Fintype.card index : ENNReal) * volume (K : Set Space) := by
      gcongr
      exact Finset.card_le_univ _

/-- Every finite indexed convex family has maximal concentration at most its
index cardinality.  Repetitions are intentionally retained. -/
theorem maximalConcentration_le_card (F : ConvexFamily index) :
    maximalConcentration F <= (Fintype.card index : ENNReal) := by
  rw [maximalConcentration]
  exact iSup_le fun K => concentration_le_card F K

/-- The finite-cardinality bound rules out the top value automatically. -/
theorem maximalConcentration_lt_top (F : ConvexFamily index) :
    maximalConcentration F < ∞ :=
  (maximalConcentration_le_card F).trans_lt
    (ENNReal.natCast_lt_top (Fintype.card index))

#print axioms concentration_le_card
#print axioms maximalConcentration_le_card
#print axioms maximalConcentration_lt_top

end

end FamilyStickyFiniteFamilyMaximalConcentrationV1

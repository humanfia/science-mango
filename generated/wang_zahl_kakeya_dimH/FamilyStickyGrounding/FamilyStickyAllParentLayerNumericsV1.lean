import FamilyStickyGrounding.FamilyStickyAllParentLayerDataV1

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyAllParentLayerNumericsV1

open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData

noncomputable section

namespace AllParentLayerData

variable {delta : NNReal} {parent tubeIndex : Type*}
  [Fintype parent] [DecidableEq parent] [DecidableEq tubeIndex]

def positiveMeanTests
    (L : AllParentLayerData delta parent tubeIndex)
    (mean : L.Test -> Real) : Finset L.Test :=
  L.activeTests.filter fun q => 0 < mean q

/-- One repetition count shared by all parent/test pairs at the layer. -/
def paperRepetitions
    (L : AllParentLayerData delta parent tubeIndex)
    (mean : L.Test -> Real) : Nat :=
  if h : (positiveMeanTests L mean).Nonempty then
    Nat.floor ((positiveMeanTests L mean).inf' h fun q =>
      L.paperCap q / mean q)
  else 1

theorem paperRepetitions_mul_mean_le_cap
    (L : AllParentLayerData delta parent tubeIndex)
    (mean : L.Test -> Real)
    (hmean : forall q, q ∈ L.activeTests -> 0 <= mean q) :
    forall q, q ∈ L.activeTests ->
      (paperRepetitions L mean : Real) * mean q <= L.paperCap q := by
  intro q hq
  have hcap : 0 <= L.paperCap q := by
    unfold AllParentLayerData.paperCap
    unfold FamilyStickyActualTubeTestDataV1.ActualTubeTestData.canonicalPaperSingleLoadCap
    exact ENNReal.toReal_nonneg
  by_cases hmeanPos : 0 < mean q
  · have hqpos : q ∈ positiveMeanTests L mean :=
      Finset.mem_filter.mpr ⟨hq, hmeanPos⟩
    have hpositive : (positiveMeanTests L mean).Nonempty := ⟨q, hqpos⟩
    let budget : Real :=
      (positiveMeanTests L mean).inf' hpositive fun r =>
        L.paperCap r / mean r
    have hbudgetNonneg : 0 <= budget := by
      apply Finset.le_inf' hpositive
      intro r hr
      have hrpos : 0 < mean r := (Finset.mem_filter.mp hr).2
      exact div_nonneg (by
        unfold AllParentLayerData.paperCap
        unfold FamilyStickyActualTubeTestDataV1.ActualTubeTestData.canonicalPaperSingleLoadCap
        exact ENNReal.toReal_nonneg) hrpos.le
    have hfloor : (Nat.floor budget : Real) <= budget :=
      Nat.floor_le hbudgetNonneg
    have hbudgetq : budget <= L.paperCap q / mean q :=
      Finset.inf'_le (fun r => L.paperCap r / mean r) hqpos
    have hratio := hfloor.trans hbudgetq
    have hJ : (paperRepetitions L mean : Real) = Nat.floor budget := by
      simp only [paperRepetitions, dif_pos hpositive, budget]
    rw [hJ]
    exact (le_div_iff₀ hmeanPos).mp hratio
  · have hmeanZero : mean q = 0 :=
      le_antisymm (le_of_not_gt hmeanPos) (hmean q hq)
    simp [hmeanZero, hcap]

theorem one_le_paperRepetitions_of_mean_le_cap
    (L : AllParentLayerData delta parent tubeIndex)
    (mean : L.Test -> Real)
    (hunit : forall q, q ∈ L.activeTests -> mean q <= L.paperCap q) :
    1 <= paperRepetitions L mean := by
  by_cases hpositive : (positiveMeanTests L mean).Nonempty
  · rw [paperRepetitions, dif_pos hpositive]
    apply Nat.le_floor
    apply Finset.le_inf' hpositive
    intro q hq
    have hqactive : q ∈ L.activeTests := (Finset.mem_filter.mp hq).1
    have hqpos : 0 < mean q := (Finset.mem_filter.mp hq).2
    exact (le_div_iff₀ hqpos).2 (by simpa using hunit q hqactive)
  · simp [paperRepetitions, hpositive]

/-- Appendix tail parameter for the union over every active parent/test pair. -/
def sourceTailParameter
    (L : AllParentLayerData delta parent tubeIndex) : Real :=
  max 1 (Real.log ((L.activeTests.card : Real) *
    Real.exp (Real.exp 1 - 1) + 1))

theorem one_le_sourceTailParameter
    (L : AllParentLayerData delta parent tubeIndex) :
    1 <= sourceTailParameter L := le_max_left _ _

theorem sourceTailRoom
    (L : AllParentLayerData delta parent tubeIndex) :
    (L.activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
      Real.exp (sourceTailParameter L) := by
  let x : Real :=
    (L.activeTests.card : Real) * Real.exp (Real.exp 1 - 1)
  have hx : 0 <= x := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hx1 : 0 < x + 1 := by linarith
  have hxlt : x < Real.exp (Real.log (x + 1)) := by
    rw [Real.exp_log hx1]
    linarith
  have hmono : Real.exp (Real.log (x + 1)) <=
      Real.exp (max 1 (Real.log (x + 1))) :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  change x < Real.exp (max 1 (Real.log (x + 1)))
  exact hxlt.trans_le hmono

#print axioms paperRepetitions_mul_mean_le_cap
#print axioms one_le_paperRepetitions_of_mean_le_cap
#print axioms one_le_sourceTailParameter
#print axioms sourceTailRoom

end AllParentLayerData

end
end FamilyStickyAllParentLayerNumericsV1

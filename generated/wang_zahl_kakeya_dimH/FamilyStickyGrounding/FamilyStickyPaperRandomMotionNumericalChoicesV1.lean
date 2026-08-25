import FamilyStickyGrounding.FamilyStickyActualTubeTestDataV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyPaperRandomMotionNumericalChoicesV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTestDataV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData

noncomputable section

/-!
# Pure numerical choices for the paper random-motion argument

For a box with short sides `k_0,k_1` and motion radius `rho`, the proved local
packing estimate supplies the explicit paper mean

`m_K = 297 * #T * k_0 * k_1 / rho^2`.

The repetition count is the natural floor of the least positive-test ratio
`cap_K / m_K`; zero-mean tests impose no restriction.  This canonically gives
`J m_K <= cap_K` for every active test, including all zero-cap/zero-mean
branches.  Finally `A = log(#tests * exp(exp(1)-1) + 1)` makes the finite union
bound strict by construction.
-/

namespace ActualTubeTestData

variable {delta : NNReal} {tubeIndex : Type*} [DecidableEq tubeIndex]

/-- The explicit fixed-test expectation majorant produced by the local
packing/double-count estimate. -/
def paperIncidenceMean
    (D : ActualTubeTestData delta tubeIndex)
    (side : Fin D.testCard -> Fin 3 -> NNReal) (motionRadius : NNReal)
    (K : Fin D.testCard) : Real :=
  (297 * (D.tubes.card : Real) * (side K 0 : Real) *
      (side K 1 : Real)) / (motionRadius : Real) ^ 2

theorem paperIncidenceMean_nonneg
    (D : ActualTubeTestData delta tubeIndex)
    (side : Fin D.testCard -> Fin 3 -> NNReal) (motionRadius : NNReal)
    (K : Fin D.testCard) :
    0 <= paperIncidenceMean D side motionRadius K := by
  unfold paperIncidenceMean
  positivity

/-- The explicit `297` feasibility condition is an equality for the chosen
mean whenever the motion radius is positive. -/
theorem explicit_297_le_motionRadius_sq_mul_paperIncidenceMean
    (D : ActualTubeTestData delta tubeIndex)
    (side : Fin D.testCard -> Fin 3 -> NNReal) {motionRadius : NNReal}
    (hRadius : 0 < motionRadius) (K : Fin D.testCard) :
    297 * (D.tubes.card : Real) * (side K 0 : Real) *
        (side K 1 : Real) <=
      (motionRadius : Real) ^ 2 *
        paperIncidenceMean D side motionRadius K := by
  unfold paperIncidenceMean
  have hRadiusReal : (0 : Real) < (motionRadius : Real) := by exact_mod_cast hRadius
  have hsq : (motionRadius : Real) ^ 2 ≠ 0 := pow_ne_zero 2 hRadiusReal.ne'
  rw [mul_comm ((motionRadius : Real) ^ 2), div_mul_cancel₀ _ hsq]

/-- Active tests whose expectation majorant is genuinely positive. -/
def positiveMeanTests
    (D : ActualTubeTestData delta tubeIndex)
    (mean : Fin D.testCard -> Real) : Finset (Fin D.testCard) :=
  D.activeTests.filter fun K => 0 < mean K

/-- The canonical paper repetition count.  If all active means vanish, one
translation is harmless and retains the source convention `J >= 1`. -/
def paperRepetitions
    (D : ActualTubeTestData delta tubeIndex)
    (mean : Fin D.testCard -> Real) : Nat :=
  if h : (positiveMeanTests D mean).Nonempty then
    Nat.floor ((positiveMeanTests D mean).inf' h fun K =>
      D.canonicalPaperSingleLoadCap K / mean K)
  else 1

/-- The canonical repetition count satisfies the Appendix budget for every
active test. -/
theorem paperRepetitions_mul_mean_le_cap
    (D : ActualTubeTestData delta tubeIndex)
    (mean : Fin D.testCard -> Real)
    (hmean : forall K, K ∈ D.activeTests -> 0 <= mean K) :
    forall K, K ∈ D.activeTests ->
      (paperRepetitions D mean : Real) * mean K <=
        D.canonicalPaperSingleLoadCap K := by
  intro K hK
  have hcap : 0 <= D.canonicalPaperSingleLoadCap K := by
    unfold canonicalPaperSingleLoadCap
    exact ENNReal.toReal_nonneg
  by_cases hmeanPos : 0 < mean K
  · have hKpos : K ∈ positiveMeanTests D mean :=
      Finset.mem_filter.mpr ⟨hK, hmeanPos⟩
    have hpositive : (positiveMeanTests D mean).Nonempty :=
      ⟨K, hKpos⟩
    let budget : Real :=
      (positiveMeanTests D mean).inf' hpositive fun L =>
        D.canonicalPaperSingleLoadCap L / mean L
    have hbudgetNonneg : 0 <= budget := by
      apply Finset.le_inf' hpositive
      intro L hL
      have hLpos : 0 < mean L := (Finset.mem_filter.mp hL).2
      exact div_nonneg (by
        unfold canonicalPaperSingleLoadCap
        exact ENNReal.toReal_nonneg) hLpos.le
    have hfloor : (Nat.floor budget : Real) <= budget :=
      Nat.floor_le hbudgetNonneg
    have hbudgetK : budget <=
        D.canonicalPaperSingleLoadCap K / mean K := by
      exact Finset.inf'_le (fun L =>
        D.canonicalPaperSingleLoadCap L / mean L) hKpos
    have hratio : (Nat.floor budget : Real) <=
        D.canonicalPaperSingleLoadCap K / mean K :=
      hfloor.trans hbudgetK
    have hJ : (paperRepetitions D mean : Real) = Nat.floor budget := by
      simp only [paperRepetitions, dif_pos hpositive, budget]
    rw [hJ]
    exact (le_div_iff₀ hmeanPos).mp hratio
  · have hmeanZero : mean K = 0 :=
      le_antisymm (le_of_not_gt hmeanPos) (hmean K hK)
    simp [hmeanZero, hcap]

/-- The logarithmic union-bound threshold chosen with one unit of strict
slack inside the exponential. -/
def paperTailParameter (D : ActualTubeTestData delta tubeIndex) : Real :=
  Real.log ((D.activeTests.card : Real) *
    Real.exp (Real.exp 1 - 1) + 1)

theorem paperTailRoom
    (D : ActualTubeTestData delta tubeIndex) :
    (D.activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
      Real.exp (paperTailParameter D) := by
  let x : Real :=
    (D.activeTests.card : Real) * Real.exp (Real.exp 1 - 1)
  have hx : 0 <= x := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hx1 : 0 < x + 1 := by linarith
  rw [paperTailParameter, show
    (D.activeTests.card : Real) * Real.exp (Real.exp 1 - 1) = x by rfl,
    Real.exp_log hx1]
  linarith

#print axioms paperIncidenceMean_nonneg
#print axioms explicit_297_le_motionRadius_sq_mul_paperIncidenceMean
#print axioms paperRepetitions_mul_mean_le_cap
#print axioms paperTailRoom

end ActualTubeTestData

end
end FamilyStickyPaperRandomMotionNumericalChoicesV1

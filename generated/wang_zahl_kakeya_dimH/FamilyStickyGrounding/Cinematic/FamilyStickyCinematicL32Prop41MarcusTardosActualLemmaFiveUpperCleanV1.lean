import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveFinalV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveUpperCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveFinalV1
open FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1

/-! # Quotient form of the fully actual Marcus--Tardos Lemma 5 -/

theorem sum_weight_inv_pos
    {depth : Nat} (hdepth : 1 ≤ depth)
    (weight : Fin depth → Real) (hweight : ∀ level, 0 < weight level) :
    0 < ∑ level, (weight level)⁻¹ := by
  let first : Fin depth := ⟨0, hdepth⟩
  have hfirst : 0 < (weight first)⁻¹ := inv_pos.mpr (hweight first)
  have hle : (weight first)⁻¹ ≤ ∑ level, (weight level)⁻¹ := by
    exact Finset.single_le_sum
      (fun level hlevel => (inv_nonneg.mpr (hweight level).le))
      (Finset.mem_univ first)
  exact hfirst.trans_le hle

theorem actualLemmaFive_quotient
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hreverse : A.IntersectionReverse B)
    (hlength : A.order.length ≤ 2 ^ depth)
    (weight : Fin depth → Real) (hweight : ∀ level, 0 < weight level) :
    totalWeightedQ weight (actualLevelQ A B hreverse) ≤
      ((A.commonOrder B).length : Real) * ∑ level, weight level -
        ((A.commonOrder B).length : Real) ^ 2 /
          (4 * ∑ level, (weight level)⁻¹) := by
  let leaders := actualLeaders depth hdepth A B hlength
  let leaderSq := leaderWeightedSquare leaders weight (actualLevelMass A B)
  have hfive := actualLemmaFive_denominatorFree depth hdepth A B hreverse
    hlength weight hweight
  have hV : 0 < ∑ level, (weight level)⁻¹ :=
    sum_weight_inv_pos hdepth weight hweight
  have hden : 0 < 4 * ∑ level, (weight level)⁻¹ := by positivity
  have hfrac :
      ((A.commonOrder B).length : Real) ^ 2 /
          (4 * ∑ level, (weight level)⁻¹) ≤ leaderSq := by
    rw [div_le_iff₀ hden]
    calc
      ((A.commonOrder B).length : Real) ^ 2 ≤
          4 * (∑ level, (weight level)⁻¹) * leaderSq := by
        simpa [leaderSq, leaders] using hfive.2
      _ = leaderSq * (4 * ∑ level, (weight level)⁻¹) := by ring
  have hsum :
      totalWeightedQ weight (actualLevelQ A B hreverse) + leaderSq ≤
        ((A.commonOrder B).length : Real) * ∑ level, weight level := by
    simpa [leaderSq, leaders] using hfive.1
  linarith

#print axioms sum_weight_inv_pos
#print axioms actualLemmaFive_quotient

end FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveUpperCleanV1

import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualMainEstimateV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTheoremOneConstantClosureV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTheoremOneRootConstantsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosUniformCountingExplicitWeightsV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDegreeNumericsV1
open FamilyStickyCinematicL32Prop41MarcusTardosIncidenceDoubleCountV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveUpperCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualMainEstimateV1
open FamilyStickyCinematicL32Prop41MarcusTardosTheoremOneConstantClosureV1
open FamilyStickyCinematicL32Prop41MarcusTardosTheoremOneRootConstantsV1

/-!
# Uniform Marcus--Tardos counting from explicit admissible weights

The large/small incidence split and the constants `8` and `21` are closed
here.  Only the three elementary finite weight sums remain as inputs.
-/

theorem uniform_counting_eight_or_twentyone_of_weight_bounds
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (d : Nat) (huniform : ∀ i, (family i).order.length = d)
    (hdpow : d ≤ 2 ^ depth)
    (weight : Fin depth → Real) (hweight : ∀ level, 0 < weight level)
    (hweightSum : (∑ level, weight level) ≤ (depth : Real))
    (hweightedDepth :
      (∑ level : Fin depth,
        weight level / (2 : Real) ^ (level.1 + 1)) ≤ 3 / (depth : Real))
    (hreciprocal :
      (∑ level, (weight level)⁻¹) ≤ 4 * (depth : Real)) :
    (d : Real) ≤ 8 * (depth : Real) * Real.sqrt (Fintype.card symbol : Real) ∨
      (d : Real) ≤
        21 * (Fintype.card symbol : Real) /
          Real.sqrt (Fintype.card index : Real) := by
  classical
  let n : Real := Fintype.card symbol
  let m : Real := Fintype.card index
  let p : Real := orderedIntersectionSum (fun i ↦ (family i).support)
  have hnNat : 0 < Fintype.card symbol := Fintype.card_pos
  have hmNat : 0 < Fintype.card index := Fintype.card_pos
  have hn : 0 ≤ n := by positivity
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast hmNat
  have hmOne : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt hmNat))
  have hd : 0 ≤ (d : Real) := by positivity
  have hk : 0 < (depth : Real) := by exact_mod_cast hdepth
  have hp : 0 ≤ p := by positivity
  by_cases hlarge :
      2 * Fintype.card symbol < d * Fintype.card index
  · have hinc := uniform_orderedIntersectionSum_lower
      (fun i ↦ (family i).support) d
      (fun i ↦ (card_support (family i)).trans (huniform i))
      hnNat hlarge
    have hnPos : 0 < n := by
      dsimp [n]
      exact_mod_cast hnNat
    have hlower :
        (d : Real) ^ 2 * m ^ 2 ≤ 2 * n * p := by
      have hinc' : ((d : Real) * m) ^ 2 / (2 * n) ≤ p := by
        simpa [n, m, p, Nat.cast_mul] using hinc
      have hmul := (div_le_iff₀ (by positivity : 0 < 2 * n)).mp hinc'
      nlinarith
    have hmain := actual_family_main_inequality
      family hreverse depth hdepth d huniform hdpow weight hweight
    have hbounds := main_inequality_implies_constant_bounds
      hn hm hd hk hp
      (sum_weight_inv_pos hdepth weight hweight)
      hlower hweightSum hweightedDepth hreciprocal
      (by simpa [m, p] using hmain)
    simpa [n, m] using
      (constant_bounds_imply_eight_or_twentyone hn hm hd hk.le hbounds)
  · right
    have hsmallNat : d * Fintype.card index ≤
        2 * Fintype.card symbol := Nat.le_of_not_gt hlarge
    have hsmall : (d : Real) * m ≤ 2 * n := by
      dsimp [m, n]
      exact_mod_cast hsmallNat
    simpa [n, m] using
      (small_total_incidence_le_twentyone hn hmOne hd hsmall)

#print axioms uniform_counting_eight_or_twentyone_of_weight_bounds

end FamilyStickyCinematicL32Prop41MarcusTardosUniformCountingExplicitWeightsV1

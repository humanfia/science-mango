import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosUniformPaperCountingV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicPrefixRestrictionV1
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicPrefixRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosUniformPaperCountingV1

/-! Literal long-list subtype, truncation, and dyadic cardinality cap. -/

noncomputable def paperBaseline (depth : Nat) (symbol : Type*)
    [Fintype symbol] : Real :=
  8 * (depth : Real) * Real.sqrt (Fintype.card symbol : Real)

noncomputable def paperStep (index symbol : Type*)
    [Fintype index] [Fintype symbol] : Real :=
  21 * (Fintype.card symbol : Real) /
    Real.sqrt (Fintype.card index : Real)

noncomputable def paperThreshold (depth level : Nat)
    (index symbol : Type*) [Fintype index] [Fintype symbol] : Real :=
  paperBaseline depth symbol +
    (2 : Real) ^ level * paperStep index symbol

noncomputable def longIndex
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth level : Nat) : Finset index :=
  Finset.univ.filter fun i ↦
    paperThreshold depth level index symbol < (family i).order.length

theorem sequence_length_le_symbol_card
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (A : DistinctCyclicSequence symbol) :
    A.order.length ≤ Fintype.card symbol := by
  rw [← card_support]
  exact Finset.card_le_univ _

theorem longIndex_card_cap
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (hsymbolPow : Fintype.card symbol ≤ 2 ^ depth)
    (level : Nat) :
    (4 : Real) ^ level *
        (longIndex family depth level).card ≤
      (Fintype.card index : Real) := by
  classical
  let tail := longIndex family depth level
  by_cases htail0 : tail.card = 0
  · simp [tail, htail0]
  · have htail : tail.Nonempty := Finset.card_ne_zero.mp htail0
    rcases htail with ⟨i0, hi0⟩
    let active := ↥tail
    letI : Nonempty active := ⟨⟨i0, hi0⟩⟩
    let threshold : Real := paperThreshold depth level index symbol
    let d : Nat := ⌊threshold⌋₊ + 1
    let truncated : active → DistinctCyclicSequence symbol :=
      fun i ↦ prefixRestrict (family i.1) d
    have hsub : PairwiseIntersectionReverse (fun i : active ↦ family i.1) :=
      hreverse.comp_injective (fun i : active ↦ i.1) Subtype.val_injective
    have htruncated : PairwiseIntersectionReverse truncated := by
      exact pairwiseIntersectionReverse_prefixRestrict hsub (fun _ ↦ d)
    have hlong (i : active) :
        threshold < ((family i.1).order.length : Real) := by
      have hi := (Finset.mem_filter.mp i.2).2
      simpa [tail, longIndex, threshold] using hi
    have hdle (i : active) : d ≤ (family i.1).order.length := by
      have hpos : 0 < (family i.1).order.length := by
        have hi := hlong i
        have hthresholdNonneg : 0 ≤ threshold := by
          dsimp [threshold, paperThreshold, paperBaseline, paperStep]
          positivity
        exact_mod_cast lt_of_le_of_lt hthresholdNonneg hi
      have hfloor : ⌊threshold⌋₊ < (family i.1).order.length :=
        (Nat.floor_lt' (Nat.ne_of_gt hpos)).2 (hlong i)
      exact Nat.add_one_le_iff.mpr hfloor
    have huniform : ∀ i : active, (truncated i).order.length = d := by
      intro i
      exact prefixRestrict_length _ (hdle i)
    have hdpow : d ≤ 2 ^ depth := by
      calc
        d ≤ (family (⟨i0, hi0⟩ : active).1).order.length :=
          hdle ⟨i0, hi0⟩
        _ ≤ Fintype.card symbol := sequence_length_le_symbol_card _
        _ ≤ 2 ^ depth := hsymbolPow
    have hcount := uniform_counting_eight_or_twentyone
      truncated htruncated depth hdepth d huniform hdpow
    have hthresholdLtD : threshold < (d : Real) := by
      simpa [d] using (Nat.lt_floor_add_one threshold)
    have hbaselineLe : paperBaseline depth symbol ≤ threshold := by
      dsimp [threshold, paperThreshold]
      exact le_add_of_nonneg_right
        (mul_nonneg (by positivity) (by
          dsimp [paperStep]
          positivity))
    rcases hcount with hbaseline | htailBound
    · exfalso
      have hdBase : (d : Real) ≤ paperBaseline depth symbol := by
        simpa [paperBaseline] using hbaseline
      linarith
    · let n : Real := Fintype.card symbol
      let m : Real := Fintype.card index
      let r : Real := Fintype.card active
      have hn : 0 < n := by
        dsimp [n]
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card symbol)
      have hm : 0 < m := by
        dsimp [m]
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card index)
      have hr : 0 < r := by
        dsimp [r]
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card active)
      have hstepPart :
          (2 : Real) ^ level * (21 * n / Real.sqrt m) <
            21 * n / Real.sqrt r := by
        have hlowerPart :
            (2 : Real) ^ level * paperStep index symbol ≤ threshold := by
          dsimp [threshold, paperThreshold]
          have hb : 0 ≤ paperBaseline depth symbol := by
            dsimp [paperBaseline]
            positivity
          linarith
        have hdUpper : (d : Real) ≤ 21 * n / Real.sqrt r := by
          simpa [n, r, truncated, active, tail] using htailBound
        have hstrict : (2 : Real) ^ level * paperStep index symbol <
            21 * n / Real.sqrt r :=
          lt_of_le_of_lt hlowerPart (hthresholdLtD.trans_le hdUpper)
        simpa [paperStep, n, m] using hstrict
      have hN : 0 < 21 * n := by positivity
      have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
      have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
      have hroot : (2 : Real) ^ level * Real.sqrt r < Real.sqrt m := by
        have hfactored :
            (21 * n) * ((2 : Real) ^ level / Real.sqrt m) <
              (21 * n) * (1 / Real.sqrt r) := by
          convert hstepPart using 1 <;> ring
        have hcancel : (2 : Real) ^ level / Real.sqrt m <
            1 / Real.sqrt r :=
          lt_of_mul_lt_mul_left hfactored hN.le
        simpa using (div_lt_div_iff₀ hsm hsr).mp hcancel
      have hsquare :
          ((2 : Real) ^ level * Real.sqrt r) ^ 2 <
            (Real.sqrt m) ^ 2 :=
        (sq_lt_sq₀ (by positivity) (by positivity)).2 hroot
      have hpow : (4 : Real) ^ level = ((2 : Real) ^ level) ^ 2 := by
        rw [show (4 : Real) = 2 ^ 2 by norm_num]
        rw [← pow_mul, ← pow_mul]
        rw [Nat.mul_comm]
      have hcapStrict : (4 : Real) ^ level * r < m := by
        calc
          (4 : Real) ^ level * r =
              ((2 : Real) ^ level * Real.sqrt r) ^ 2 := by
            rw [hpow, mul_pow, Real.sq_sqrt hr.le]
          _ < (Real.sqrt m) ^ 2 := hsquare
          _ = m := Real.sq_sqrt hm.le
      have hcard : (Fintype.card active : Real) = tail.card := by
        simp [active]
      simpa [tail, r, hcard] using hcapStrict.le

#print axioms sequence_length_le_symbol_card
#print axioms longIndex_card_cap

end FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1

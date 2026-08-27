import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41FiniteRandomSamplingWeightedExtractionV1

open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

/-!
# Weighted finite random-sampling extraction

The original extraction uses the score `survival - c * load`.  Nothing in
that argument depends on survival being a cardinality: it applies to every
nonnegative real value bounded by a fixed total.  We first record that
generic form, then apply it to arbitrary nonnegative rectangle weights.

The final theorem accepts `ENNReal` weights.  Finite weights are transported
through `ENNReal.toReal`.  If one weight is infinite, the same real theorem is
applied to the point mass at that rectangle; forcing that rectangle to
survive makes the selected `ENNReal` weight infinite.  Thus no hidden
finiteness assumption on the weights is needed.
-/

/-- The score extraction for an arbitrary bounded nonnegative value. -/
theorem exists_sample_with_eighth_value_and_sevenfold_load
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (value load : Omega -> Real) (total sigma : Real)
    (hvalue_nonneg : forall omega, 0 <= value omega)
    (hvalue_upper : forall omega, value omega <= total)
    (hload_nonneg : forall omega, 0 <= load omega)
    (htotal : 0 <= total) (hsigma : 0 <= sigma)
    (hvalue : total / 4 <= 𝔼 omega, value omega)
    (hload : (𝔼 omega, load omega) <= sigma) :
    exists omega, total / 8 <= value omega ∧ load omega <= 7 * sigma := by
  classical
  have hOmega : (Finset.univ : Finset Omega).Nonempty := Finset.univ_nonempty
  rcases htotal.eq_or_lt with htotalZero | htotalPos
  · obtain ⟨omega, _homega, homegaLoad⟩ :=
      Finset.exists_le_of_expect_le hOmega hload
    refine ⟨omega, ?_, homegaLoad.trans ?_⟩
    · simpa [← htotalZero] using hvalue_nonneg omega
    · nlinarith
  · rcases hsigma.eq_or_lt with hsigmaZero | hsigmaPos
    · have hexpectLoadNonneg : 0 <= 𝔼 omega, load omega := by
        exact Finset.expect_nonneg fun omega _ => hload_nonneg omega
      have hexpectLoadZero : (𝔼 omega, load omega) = 0 := by
        apply le_antisymm
        · simpa [← hsigmaZero] using hload
        · exact hexpectLoadNonneg
      have hloadZero : load = 0 :=
        (Fintype.expect_eq_zero_iff_of_nonneg hload_nonneg).mp
          hexpectLoadZero
      have htarget : total / 8 <= 𝔼 omega, value omega := by
        calc
          total / 8 <= total / 4 := by nlinarith
          _ <= 𝔼 omega, value omega := hvalue
      obtain ⟨omega, _homega, homegaValue⟩ :=
        Finset.exists_le_of_le_expect hOmega htarget
      refine ⟨omega, homegaValue, ?_⟩
      have homegaLoadZero : load omega = 0 := by
        simpa using congrFun hloadZero omega
      simp [homegaLoadZero, ← hsigmaZero]
    · let coefficient : Real := total / (8 * sigma)
      have hcoefficientPos : 0 < coefficient := by
        dsimp [coefficient]
        positivity
      have hweightedLoad :
          (𝔼 omega, coefficient * load omega) <= coefficient * sigma := by
        rw [← Finset.mul_expect]
        exact mul_le_mul_of_nonneg_left hload hcoefficientPos.le
      have hcoefficientSigma : coefficient * sigma = total / 8 := by
        dsimp [coefficient]
        field_simp
      have hscore : total / 8 <=
          𝔼 omega, (value omega - coefficient * load omega) := by
        rw [Finset.expect_sub_distrib]
        calc
          total / 8 = total / 4 - coefficient * sigma := by
            rw [hcoefficientSigma]
            ring
          _ <= (𝔼 omega, value omega) -
              (𝔼 omega, coefficient * load omega) := by
            exact sub_le_sub hvalue hweightedLoad
      obtain ⟨omega, _homega, homegaScore⟩ :=
        Finset.exists_le_of_le_expect hOmega hscore
      have hweightedNonneg : 0 <= coefficient * load omega :=
        mul_nonneg hcoefficientPos.le (hload_nonneg omega)
      have homegaValue : total / 8 <= value omega := by
        linarith
      have hweightedUpper : coefficient * load omega <= 7 * total / 8 := by
        linarith [hvalue_upper omega]
      have hrightRewrite : 7 * total / 8 =
          coefficient * (7 * sigma) := by
        dsimp [coefficient]
        field_simp
      have hloadUpper : load omega <= 7 * sigma := by
        apply le_of_mul_le_mul_left _ hcoefficientPos
        rw [← hrightRewrite]
        exact hweightedUpper
      exact ⟨omega, homegaValue, hloadUpper⟩

/-- A weighted survivor sum is the sum of its weighted hit indicators. -/
theorem twoSidedZeroColorSurvivors_realWeight_eq_sum
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (weight : Rectangle -> Real)
    (omega : (alpha -> Fin k) × (beta -> Fin l)) :
    (∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
        weight R) =
      ∑ R : Rectangle,
        if omega.1 ∈ zeroColorHitEvent k (leftNeighbors R) ∧
            omega.2 ∈ zeroColorHitEvent l (rightNeighbors R)
        then weight R else 0 := by
  simp only [twoSidedZeroColorSurvivors, Finset.sum_filter]

/-- Nonnegative real rectangle weight survives in expectation by at least
one quarter. -/
theorem quarter_le_expect_twoSidedZeroColorSurvivors_realWeight
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (weight : Rectangle -> Real)
    (hweight : forall R, 0 <= weight R)
    (hleft : forall R, k <= (leftNeighbors R).card)
    (hright : forall R, l <= (rightNeighbors R).card) :
    (∑ R : Rectangle, weight R) / 4 <=
      𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        ∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
          weight R := by
  classical
  calc
    (∑ R : Rectangle, weight R) / 4 =
        ∑ R : Rectangle, weight R / 4 := by rw [Finset.sum_div]
    _ <= ∑ R : Rectangle,
        𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
          if omega.1 ∈ zeroColorHitEvent k (leftNeighbors R) ∧
              omega.2 ∈ zeroColorHitEvent l (rightNeighbors R)
          then weight R else 0 := by
      apply Finset.sum_le_sum
      intro R _hR
      let hit : ((alpha -> Fin k) × (beta -> Fin l)) -> Prop := fun omega =>
        omega.1 ∈ zeroColorHitEvent k (leftNeighbors R) ∧
          omega.2 ∈ zeroColorHitEvent l (rightNeighbors R)
      have hhit : (1 : Real) / 4 <=
          𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
            if hit omega then (1 : Real) else 0 :=
        (expect_two_zeroColor_hits_gt_quarter k l
          (leftNeighbors R) (rightNeighbors R) (hleft R) (hright R)).le
      calc
        weight R / 4 = weight R * ((1 : Real) / 4) := by ring
        _ <= weight R *
            (𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
              if hit omega then (1 : Real) else 0) :=
          mul_le_mul_of_nonneg_left hhit (hweight R)
        _ = 𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
              weight R * (if hit omega then (1 : Real) else 0) := by
          rw [← Finset.mul_expect]
        _ = 𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
              if hit omega then weight R else 0 := by
          apply Finset.expect_congr rfl
          intro omega _homega
          by_cases homega : hit omega <;> simp [homega]
    _ = 𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        ∑ R : Rectangle,
          if omega.1 ∈ zeroColorHitEvent k (leftNeighbors R) ∧
              omega.2 ∈ zeroColorHitEvent l (rightNeighbors R)
          then weight R else 0 := by
      symm
      exact Finset.expect_sum_comm _ _ _
    _ = 𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        ∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
          weight R := by
      apply Finset.expect_congr rfl
      intro omega _homega
      exact (twoSidedZeroColorSurvivors_realWeight_eq_sum
        k l leftNeighbors rightNeighbors weight omega).symm

/-- The simultaneous extraction for nonnegative real rectangle weights. -/
theorem exists_twoSidedZeroColor_sample_with_eighth_realWeight_and_sevenfold_load
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (weight : Rectangle -> Real)
    (hweight : forall R, 0 <= weight R)
    (hleft : forall R, k <= (leftNeighbors R).card)
    (hright : forall R, l <= (rightNeighbors R).card) :
    exists omega : (alpha -> Fin k) × (beta -> Fin l),
      (∑ R : Rectangle, weight R) / 8 <=
          ∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
            weight R ∧
        twoSidedZeroColorLoad k l omega <=
          7 * ((Fintype.card alpha : Real) / (k : Real) +
            (Fintype.card beta : Real) / (l : Real)) := by
  let total : Real := ∑ R : Rectangle, weight R
  let value : ((alpha -> Fin k) × (beta -> Fin l)) -> Real := fun omega =>
    ∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
      weight R
  let sigma : Real := (Fintype.card alpha : Real) / (k : Real) +
    (Fintype.card beta : Real) / (l : Real)
  apply exists_sample_with_eighth_value_and_sevenfold_load value
    (twoSidedZeroColorLoad k l) total sigma
  · intro omega
    exact Finset.sum_nonneg fun R _ => hweight R
  · intro omega
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun R _ _ => hweight R)
  · intro omega
    exact twoSidedZeroColorLoad_nonneg k l omega
  · exact Finset.sum_nonneg fun R _ => hweight R
  · dsimp only [sigma]
    positivity
  · simpa only [total, value] using
      quarter_le_expect_twoSidedZeroColorSurvivors_realWeight
        k l leftNeighbors rightNeighbors weight hweight hleft hright
  · dsimp only [sigma]
    rw [expect_twoSidedZeroColorLoad]

/-- Arbitrary `ENNReal` rectangle weight survives by one eighth at the same
outcome that obeys the sevenfold curve-load bound. -/
theorem exists_twoSidedZeroColor_sample_with_eighth_ennrealWeight_and_sevenfold_load
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (weight : Rectangle -> ENNReal)
    (hleft : forall R, k <= (leftNeighbors R).card)
    (hright : forall R, l <= (rightNeighbors R).card) :
    exists omega : (alpha -> Fin k) × (beta -> Fin l),
      (∑ R : Rectangle, weight R) / 8 <=
          ∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
            weight R ∧
        twoSidedZeroColorLoad k l omega <=
          7 * ((Fintype.card alpha : Real) / (k : Real) +
            (Fintype.card beta : Real) / (l : Real)) := by
  classical
  by_cases hfinite : forall R, weight R ≠ (⊤ : ENNReal)
  · obtain ⟨omega, hsurvival, hload⟩ :=
      exists_twoSidedZeroColor_sample_with_eighth_realWeight_and_sevenfold_load
        k l leftNeighbors rightNeighbors (fun R => (weight R).toReal)
          (fun R => ENNReal.toReal_nonneg) hleft hright
    refine ⟨omega, ?_, hload⟩
    have htotalTop : (∑ R : Rectangle, weight R) ≠ (⊤ : ENNReal) := by
      exact ENNReal.sum_ne_top.mpr fun R _ => hfinite R
    have hselectedTop :
        (∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
          weight R) ≠ (⊤ : ENNReal) := by
      exact ENNReal.sum_ne_top.mpr fun R _ => hfinite R
    apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top htotalTop (by norm_num))
      hselectedTop).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_sum (fun R _ => hfinite R)]
    rw [ENNReal.toReal_sum (fun R _ => hfinite R)]
    exact hsurvival
  · push Not at hfinite
    obtain ⟨Rtop, hRtop⟩ := hfinite
    let pointWeight : Rectangle -> Real := fun R => if R = Rtop then 1 else 0
    have hpointWeight : forall R, 0 <= pointWeight R := by
      intro R
      dsimp only [pointWeight]
      split_ifs <;> norm_num
    obtain ⟨omega, hsurvival, hload⟩ :=
      exists_twoSidedZeroColor_sample_with_eighth_realWeight_and_sevenfold_load
        k l leftNeighbors rightNeighbors pointWeight hpointWeight hleft hright
    have hRtopSurvives : Rtop ∈
        twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega := by
      by_contra hnot
      have hselectedZero :
          (∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
            pointWeight R) = 0 := by
        apply Finset.sum_eq_zero
        intro R hR
        dsimp only [pointWeight]
        split_ifs with hEq
        · subst R
          exact (hnot hR).elim
        · rfl
      have htotalOne : (∑ R : Rectangle, pointWeight R) = 1 := by
        simp [pointWeight]
      rw [htotalOne, hselectedZero] at hsurvival
      norm_num at hsurvival
    refine ⟨omega, ?_, hload⟩
    have hselectedInfinite :
        (∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
          weight R) = (⊤ : ENNReal) := by
      apply top_unique
      calc
        (⊤ : ENNReal) = weight Rtop := hRtop.symm
        _ <= ∑ R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega,
            weight R := Finset.single_le_sum (fun R _ => bot_le) hRtopSurvives
    rw [hselectedInfinite]
    exact le_top

#print axioms exists_sample_with_eighth_value_and_sevenfold_load
#print axioms quarter_le_expect_twoSidedZeroColorSurvivors_realWeight
#print axioms exists_twoSidedZeroColor_sample_with_eighth_realWeight_and_sevenfold_load
#print axioms exists_twoSidedZeroColor_sample_with_eighth_ennrealWeight_and_sevenfold_load

end

end FamilyStickyCinematicL32Prop41FiniteRandomSamplingWeightedExtractionV1

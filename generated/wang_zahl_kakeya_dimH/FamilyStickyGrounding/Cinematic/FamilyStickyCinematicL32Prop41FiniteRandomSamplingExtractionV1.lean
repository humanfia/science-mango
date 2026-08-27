import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

/-!
# The finite averaging extraction in the Prop. 4.1 sampling reduction

The paper ends the proof of Proposition 4.1 by citing a standard random
sampling argument.  This module proves the deterministic extraction step of
that argument on the literal finite sample space.  If a quarter of all
rectangles survive on average and the expected number of sampled curves is at
most `sigma`, one outcome retains at least one eighth of the rectangles while
using at most seven times `sigma` curves.

The proof uses one score, `survivors - c * load`.  Thus the two conclusions
come from the same outcome; they are not separate applications of averaging.
-/

/-- Simultaneous finite-sampling extraction with the constants used in the
`mu`/`nu` reduction.  The only inputs are the two expectation estimates that
the explicit independent-colouring count must supply. -/
theorem exists_sample_with_eighth_survival_and_sevenfold_load
    {Omega Rectangle : Type*}
    [Fintype Omega] [Nonempty Omega] [Fintype Rectangle]
    (survivors : Omega -> Finset Rectangle)
    (load : Omega -> Real) (sigma : Real)
    (hload_nonneg : forall omega, 0 <= load omega)
    (hsigma : 0 <= sigma)
    (hsurvival :
      (Fintype.card Rectangle : Real) / 4 <=
        𝔼 omega, ((survivors omega).card : Real))
    (hload : (𝔼 omega, load omega) <= sigma) :
    exists omega,
      (Fintype.card Rectangle : Real) / 8 <=
          ((survivors omega).card : Real) ∧
        load omega <= 7 * sigma := by
  classical
  let rectangleCount : Real := Fintype.card Rectangle
  have hOmega : (Finset.univ : Finset Omega).Nonempty := Finset.univ_nonempty
  by_cases hRectangleZero : Fintype.card Rectangle = 0
  · obtain ⟨omega, _homega, homegaLoad⟩ :=
      Finset.exists_le_of_expect_le hOmega hload
    refine ⟨omega, ?_, homegaLoad.trans ?_⟩
    · simp [hRectangleZero]
    · nlinarith
  have hRectanglePosNat : 0 < Fintype.card Rectangle :=
    Nat.pos_of_ne_zero hRectangleZero
  have hRectangleCastPos : (0 : Real) < Fintype.card Rectangle := by
    exact_mod_cast hRectanglePosNat
  have hRectanglePos : 0 < rectangleCount := by
    simpa [rectangleCount] using hRectangleCastPos
  rcases hsigma.eq_or_lt with hsigmaZero | hsigmaPos
  · have hexpectLoadNonneg : 0 <= 𝔼 omega, load omega := by
      exact Finset.expect_nonneg fun omega _ => hload_nonneg omega
    have hexpectLoadZero : (𝔼 omega, load omega) = 0 := by
      apply le_antisymm
      · simpa [hsigmaZero] using hload
      · exact hexpectLoadNonneg
    have hloadZero : load = 0 :=
      (Fintype.expect_eq_zero_iff_of_nonneg hload_nonneg).mp
        hexpectLoadZero
    have htarget : rectangleCount / 8 <=
        𝔼 omega, ((survivors omega).card : Real) := by
      calc
        rectangleCount / 8 <= rectangleCount / 4 := by nlinarith
        _ <= 𝔼 omega, ((survivors omega).card : Real) := by
          simpa [rectangleCount] using hsurvival
    obtain ⟨omega, _homega, homegaSurvival⟩ :=
      Finset.exists_le_of_le_expect hOmega htarget
    refine ⟨omega, by simpa [rectangleCount] using homegaSurvival, ?_⟩
    have homegaLoadZero : load omega = 0 := by
      simpa using congrFun hloadZero omega
    simp [homegaLoadZero, ← hsigmaZero]
  · let coefficient : Real := rectangleCount / (8 * sigma)
    have hcoefficientPos : 0 < coefficient := by
      dsimp [coefficient]
      positivity
    have hweightedLoad :
        (𝔼 omega, coefficient * load omega) <= coefficient * sigma := by
      rw [← Finset.mul_expect]
      exact mul_le_mul_of_nonneg_left hload hcoefficientPos.le
    have hcoefficientSigma : coefficient * sigma = rectangleCount / 8 := by
      dsimp [coefficient]
      field_simp
    have hscore : rectangleCount / 8 <=
        𝔼 omega,
          (((survivors omega).card : Real) - coefficient * load omega) := by
      rw [Finset.expect_sub_distrib]
      calc
        rectangleCount / 8 = rectangleCount / 4 - coefficient * sigma := by
          rw [hcoefficientSigma]
          ring
        _ <= (𝔼 omega, ((survivors omega).card : Real)) -
            (𝔼 omega, coefficient * load omega) := by
          exact sub_le_sub (by simpa [rectangleCount] using hsurvival)
            hweightedLoad
    obtain ⟨omega, _homega, homegaScore⟩ :=
      Finset.exists_le_of_le_expect hOmega hscore
    have hweightedNonneg : 0 <= coefficient * load omega :=
      mul_nonneg hcoefficientPos.le (hload_nonneg omega)
    have homegaSurvival : rectangleCount / 8 <=
        ((survivors omega).card : Real) := by
      linarith
    have hsurvivorUpperCast :
        ((survivors omega).card : Real) <= Fintype.card Rectangle := by
      exact_mod_cast Finset.card_le_univ (survivors omega)
    have hsurvivorUpper : ((survivors omega).card : Real) <= rectangleCount := by
      simpa [rectangleCount] using hsurvivorUpperCast
    have hweightedUpper : coefficient * load omega <=
        7 * rectangleCount / 8 := by
      linarith
    have hrightRewrite : 7 * rectangleCount / 8 =
        coefficient * (7 * sigma) := by
      dsimp [coefficient]
      field_simp
    have hloadUpper : load omega <= 7 * sigma := by
      apply le_of_mul_le_mul_left _ hcoefficientPos
      rw [← hrightRewrite]
      exact hweightedUpper
    exact ⟨omega, by simpa [rectangleCount] using homegaSurvival, hloadUpper⟩


/-- Curves assigned colour zero in a uniform `Fin k` colouring. -/
def zeroColorSample
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (omega : alpha -> Fin k) : Finset alpha :=
  Finset.univ.filter fun a => omega a = 0

/-- The finite event that one fixed curve receives colour zero. -/
noncomputable def zeroColorEvent
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (a : alpha) : Finset (alpha -> Fin k) := by
  classical
  exact Finset.univ.filter fun omega => omega a = 0

@[simp]
theorem mem_zeroColorEvent_iff
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (a : alpha) (omega : alpha -> Fin k) :
    omega ∈ zeroColorEvent k a ↔ omega a = 0 := by
  classical
  simp [zeroColorEvent]

/-- Exact cardinality of a one-coordinate zero-colour event. -/
theorem zeroColorEvent_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (a : alpha) :
    (zeroColorEvent k a).card = k ^ (Fintype.card alpha - 1) := by
  classical
  have h := Fintype.card_filter_piFinset_const_eq_of_mem
    (s := (Finset.univ : Finset (Fin k))) a
    (x := (0 : Fin k)) (Finset.mem_univ _)
  simpa [zeroColorEvent] using h


/-- A fixed curve is selected with exact probability `1 / k` in the literal
finite colouring space. -/
theorem expect_zeroColor_indicator
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (a : alpha) :
    (𝔼 omega : alpha -> Fin k,
        if omega a = 0 then (1 : Real) else 0) = 1 / (k : Real) := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Finset.sum_boole]
  change ((zeroColorEvent k a).card : Real) /
      (Fintype.card (alpha -> Fin k) : Real) = 1 / (k : Real)
  rw [zeroColorEvent_card, Fintype.card_fun, Fintype.card_fin]
  have halphaPos : 0 < Fintype.card alpha :=
    Fintype.card_pos_iff.mpr ⟨a⟩
  have honeLe : 1 <= Fintype.card alpha := halphaPos
  have hpow : k ^ Fintype.card alpha =
      k ^ (Fintype.card alpha - 1) * k := by
    conv_lhs => rw [← Nat.sub_add_cancel honeLe]
    rw [pow_succ]
  rw [hpow]
  push_cast
  have hkNat : k ≠ 0 := NeZero.ne k
  have hkReal : (k : Real) ≠ 0 := by exact_mod_cast hkNat
  have hpowReal : ((k : Real) ^ (Fintype.card alpha - 1)) ≠ 0 :=
    pow_ne_zero _ hkReal
  field_simp [hkReal, hpowReal]


/-- The selected-set cardinality is the sum of its coordinate indicators. -/
theorem zeroColorSample_card_cast_eq_sum
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (omega : alpha -> Fin k) :
    ((zeroColorSample k omega).card : Real) =
      ∑ a : alpha, if omega a = 0 then (1 : Real) else 0 := by
  simp [zeroColorSample]

/-- Exact expected number of selected curves in a uniform independent
`Fin k` colouring. -/
theorem expect_zeroColorSample_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] :
    (𝔼 omega : alpha -> Fin k, ((zeroColorSample k omega).card : Real)) =
      (Fintype.card alpha : Real) / (k : Real) := by
  classical
  calc
    (𝔼 omega : alpha -> Fin k,
        ((zeroColorSample k omega).card : Real)) =
        𝔼 omega : alpha -> Fin k,
          ∑ a : alpha, if omega a = 0 then (1 : Real) else 0 := by
            apply Finset.expect_congr rfl
            intro omega _homega
            exact zeroColorSample_card_cast_eq_sum k omega
    _ = ∑ a : alpha,
          𝔼 omega : alpha -> Fin k,
            if omega a = 0 then (1 : Real) else 0 := by
          exact Finset.expect_sum_comm _ _ _
    _ = ∑ _a : alpha, 1 / (k : Real) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact expect_zeroColor_indicator k a
    _ = (Fintype.card alpha : Real) / (k : Real) := by
          simp [div_eq_mul_inv]


/-- Nonzero colours available at a coordinate that must miss the sample. -/
def nonzeroFinColors (k : Nat) [NeZero k] : Finset (Fin k) :=
  Finset.univ.erase 0

/-- Coordinate-wise allowed colours for missing every member of `neighbors`. -/
def zeroColorMissAllowed
    {alpha : Type*} [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha) (a : alpha) :
    Finset (Fin k) :=
  if a ∈ neighbors then nonzeroFinColors k else Finset.univ

/-- Literal finite event that no neighbour receives colour zero. -/
noncomputable def zeroColorMissEvent
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha) :
    Finset (alpha -> Fin k) :=
  Fintype.piFinset (zeroColorMissAllowed k neighbors)

@[simp]
theorem mem_zeroColorMissEvent_iff
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha)
    (omega : alpha -> Fin k) :
    omega ∈ zeroColorMissEvent k neighbors ↔
      forall a, a ∈ neighbors -> omega a ≠ 0 := by
  classical
  simp only [zeroColorMissEvent, Fintype.mem_piFinset]
  constructor
  · intro h a ha
    have haAllowed := h a
    simpa [zeroColorMissAllowed, nonzeroFinColors, ha] using haAllowed
  · intro h a
    by_cases ha : a ∈ neighbors
    · simpa [zeroColorMissAllowed, nonzeroFinColors, ha] using h a ha
    · simp [zeroColorMissAllowed, ha]

/-- Exact product count of colourings missing a prescribed neighbour set. -/
theorem zeroColorMissEvent_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha) :
    (zeroColorMissEvent k neighbors).card =
      (k - 1) ^ neighbors.card *
        k ^ (Fintype.card alpha - neighbors.card) := by
  classical
  rw [zeroColorMissEvent, Fintype.card_piFinset]
  simp only [zeroColorMissAllowed, apply_ite]
  rw [Finset.prod_ite]
  have hpos :
      (Finset.univ.filter fun a : alpha => a ∈ neighbors) = neighbors := by
    ext a
    simp
  have hneg :
      (Finset.univ.filter fun a : alpha => ¬a ∈ neighbors) =
        Finset.univ \ neighbors := by
    ext a
    simp
  rw [hpos, hneg]
  simp [nonzeroFinColors,
    Finset.card_sdiff_of_subset (Finset.subset_univ neighbors)]


/-- Exact probability of missing every member of a prescribed neighbour set. -/
theorem expect_zeroColorMiss_indicator
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha) :
    (𝔼 omega : alpha -> Fin k,
        if omega ∈ zeroColorMissEvent k neighbors then (1 : Real) else 0) =
      (((k - 1 : Nat) : Real) / (k : Real)) ^ neighbors.card := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  change ((zeroColorMissEvent k neighbors).card : Real) /
      (Fintype.card (alpha -> Fin k) : Real) =
        (((k - 1 : Nat) : Real) / (k : Real)) ^ neighbors.card
  rw [zeroColorMissEvent_card, Fintype.card_fun, Fintype.card_fin]
  have hkNat : k ≠ 0 := NeZero.ne k
  have hkReal : (k : Real) ≠ 0 := by exact_mod_cast hkNat
  have hcard : neighbors.card ≤ Fintype.card alpha :=
    Finset.card_le_univ neighbors
  have hpowNat : k ^ Fintype.card alpha =
      k ^ (Fintype.card alpha - neighbors.card) * k ^ neighbors.card := by
    calc
      k ^ Fintype.card alpha =
          k ^ ((Fintype.card alpha - neighbors.card) + neighbors.card) := by
            congr 1
            omega
      _ = k ^ (Fintype.card alpha - neighbors.card) *
          k ^ neighbors.card := by rw [pow_add]
  rw [hpowNat]
  push_cast
  rw [div_pow]
  field_simp [hkReal]

/-- If there are at least `k` neighbours, the exact miss probability is
strictly below one half. -/
theorem expect_zeroColorMiss_indicator_lt_half
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha)
    (hkLe : k ≤ neighbors.card) :
    (𝔼 omega : alpha -> Fin k,
        if omega ∈ zeroColorMissEvent k neighbors then (1 : Real) else 0) <
      (1 : Real) / 2 := by
  rw [expect_zeroColorMiss_indicator]
  have hkPosNat : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkOne : 1 ≤ k := hkPosNat
  have hkRealPos : (0 : Real) < k := by exact_mod_cast hkPosNat
  have hkRealOne : (1 : Real) ≤ k := by exact_mod_cast hkOne
  have hbaseEq :
      (((k - 1 : Nat) : Real) / (k : Real)) =
        1 - 1 / (k : Real) := by
    rw [Nat.cast_sub hkOne, Nat.cast_one]
    field_simp
  rw [hbaseEq]
  have hbaseNonneg : (0 : Real) ≤ 1 - 1 / (k : Real) := by
    rw [sub_nonneg]
    exact (div_le_iff₀ hkRealPos).2 (by simpa using hkRealOne)
  have hbaseLeOne : 1 - 1 / (k : Real) ≤ (1 : Real) := by
    exact sub_le_self _ (by positivity)
  calc
    (1 - 1 / (k : Real)) ^ neighbors.card ≤
        (1 - 1 / (k : Real)) ^ k :=
      pow_le_pow_of_le_one hbaseNonneg hbaseLeOne hkLe
    _ ≤ Real.exp (-1) := by
      exact Real.one_sub_div_pow_le_exp_neg hkRealOne
    _ < (1 : Real) / 2 := Real.exp_neg_one_lt_half

/-- The complementary event: at least one neighbour receives colour zero. -/
noncomputable def zeroColorHitEvent
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha) :
    Finset (alpha -> Fin k) :=
  Finset.univ \ zeroColorMissEvent k neighbors

@[simp]
theorem mem_zeroColorHitEvent_iff
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha)
    (omega : alpha -> Fin k) :
    omega ∈ zeroColorHitEvent k neighbors ↔
      exists a, a ∈ neighbors ∧ omega a = 0 := by
  classical
  simp [zeroColorHitEvent, mem_zeroColorMissEvent_iff]

/-- Exact hit probability, obtained as the literal complement of the miss event. -/
theorem expect_zeroColorHit_indicator
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha) :
    (𝔼 omega : alpha -> Fin k,
        if omega ∈ zeroColorHitEvent k neighbors then (1 : Real) else 0) =
      1 - (((k - 1 : Nat) : Real) / (k : Real)) ^ neighbors.card := by
  classical
  calc
    (𝔼 omega : alpha -> Fin k,
        if omega ∈ zeroColorHitEvent k neighbors then (1 : Real) else 0) =
        𝔼 omega : alpha -> Fin k,
          ((1 : Real) -
            (if omega ∈ zeroColorMissEvent k neighbors then 1 else 0)) := by
              apply Finset.expect_congr rfl
              intro omega _homega
              by_cases hmiss : omega ∈ zeroColorMissEvent k neighbors
              · simp [zeroColorHitEvent, hmiss]
              · simp [zeroColorHitEvent, hmiss]
    _ = (𝔼 _omega : alpha -> Fin k, (1 : Real)) -
        (𝔼 omega : alpha -> Fin k,
          if omega ∈ zeroColorMissEvent k neighbors then (1 : Real) else 0) := by
            rw [Finset.expect_sub_distrib]
    _ = 1 - (((k - 1 : Nat) : Real) / (k : Real)) ^ neighbors.card := by
          rw [expect_zeroColorMiss_indicator]
          simp

/-- With at least `k` neighbours, the hit probability is strictly above one half. -/
theorem expect_zeroColorHit_indicator_gt_half
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (k : Nat) [NeZero k] (neighbors : Finset alpha)
    (hkLe : k ≤ neighbors.card) :
    (1 : Real) / 2 <
      𝔼 omega : alpha -> Fin k,
        if omega ∈ zeroColorHitEvent k neighbors then (1 : Real) else 0 := by
  rw [expect_zeroColorHit_indicator]
  have hmiss := expect_zeroColorMiss_indicator_lt_half k neighbors hkLe
  rw [expect_zeroColorMiss_indicator] at hmiss
  linarith

/-- Expectations of factors on a literal product sample space multiply. -/
theorem expect_independent_product
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A -> Real) (g : B -> Real) :
    (𝔼 z : A × B, f z.1 * g z.2) =
      (𝔼 a : A, f a) * (𝔼 b : B, g b) := by
  calc
    (𝔼 z : A × B, f z.1 * g z.2) =
        𝔼 a : A, 𝔼 b : B, f a * g b := by
          rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = (𝔼 a : A, f a) * (𝔼 b : B, g b) :=
      (Fintype.expect_mul_expect f g).symm


/-- Independent zero-colour samples hit both prescribed neighbour sets with
probability strictly greater than one quarter. -/
theorem expect_two_zeroColor_hits_gt_quarter
    {alpha beta : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Finset alpha) (rightNeighbors : Finset beta)
    (hkLe : k ≤ leftNeighbors.card) (hlLe : l ≤ rightNeighbors.card) :
    (𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        if omega.1 ∈ zeroColorHitEvent k leftNeighbors ∧
            omega.2 ∈ zeroColorHitEvent l rightNeighbors
        then (1 : Real) else 0) > (1 : Real) / 4 := by
  classical
  calc
    (𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        if omega.1 ∈ zeroColorHitEvent k leftNeighbors ∧
            omega.2 ∈ zeroColorHitEvent l rightNeighbors
        then (1 : Real) else 0) =
        𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
          (if omega.1 ∈ zeroColorHitEvent k leftNeighbors then (1 : Real) else 0) *
            (if omega.2 ∈ zeroColorHitEvent l rightNeighbors then (1 : Real) else 0) := by
              apply Finset.expect_congr rfl
              intro omega _homega
              by_cases hleft : omega.1 ∈ zeroColorHitEvent k leftNeighbors <;>
                by_cases hright : omega.2 ∈ zeroColorHitEvent l rightNeighbors <;>
                  simp [hleft, hright]
    _ = (𝔼 omega : alpha -> Fin k,
          if omega ∈ zeroColorHitEvent k leftNeighbors then (1 : Real) else 0) *
        (𝔼 omega : beta -> Fin l,
          if omega ∈ zeroColorHitEvent l rightNeighbors then (1 : Real) else 0) := by
            exact expect_independent_product
              (fun omega : alpha -> Fin k =>
                if omega ∈ zeroColorHitEvent k leftNeighbors then (1 : Real) else 0)
              (fun omega : beta -> Fin l =>
                if omega ∈ zeroColorHitEvent l rightNeighbors then (1 : Real) else 0)
    _ > (1 : Real) / 4 := by
      have hleft := expect_zeroColorHit_indicator_gt_half k leftNeighbors hkLe
      have hright := expect_zeroColorHit_indicator_gt_half l rightNeighbors hlLe
      have hmul := mul_lt_mul hleft hright.le (by norm_num) (by linarith)
      nlinarith


/-- Rectangles hit by both independent zero-colour samples. -/
noncomputable def twoSidedZeroColorSurvivors
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l)) : Finset Rectangle :=
  Finset.univ.filter fun R =>
    omega.1 ∈ zeroColorHitEvent k (leftNeighbors R) ∧
      omega.2 ∈ zeroColorHitEvent l (rightNeighbors R)

@[simp]
theorem mem_twoSidedZeroColorSurvivors_iff
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l)) (R : Rectangle) :
    R ∈ twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega ↔
      omega.1 ∈ zeroColorHitEvent k (leftNeighbors R) ∧
        omega.2 ∈ zeroColorHitEvent l (rightNeighbors R) := by
  simp [twoSidedZeroColorSurvivors]

/-- Survivor cardinality is the sum of the two-sided hit indicators. -/
theorem twoSidedZeroColorSurvivors_card_cast_eq_sum
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin k) × (beta -> Fin l)) :
    ((twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega).card : Real) =
      ∑ R : Rectangle,
        if omega.1 ∈ zeroColorHitEvent k (leftNeighbors R) ∧
            omega.2 ∈ zeroColorHitEvent l (rightNeighbors R)
        then (1 : Real) else 0 := by
  simp [twoSidedZeroColorSurvivors]

/-- If each rectangle has at least the sampling modulus many neighbours on
both sides, at least one quarter of all rectangles survive on average. -/
theorem quarter_le_expect_twoSidedZeroColorSurvivors_card
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (hleft : forall R, k ≤ (leftNeighbors R).card)
    (hright : forall R, l ≤ (rightNeighbors R).card) :
    (Fintype.card Rectangle : Real) / 4 ≤
      𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        ((twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega).card : Real) := by
  classical
  calc
    (Fintype.card Rectangle : Real) / 4 =
        ∑ _R : Rectangle, (1 : Real) / 4 := by
          simp [div_eq_mul_inv]
    _ ≤ ∑ R : Rectangle,
        𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
          if omega.1 ∈ zeroColorHitEvent k (leftNeighbors R) ∧
              omega.2 ∈ zeroColorHitEvent l (rightNeighbors R)
          then (1 : Real) else 0 := by
            apply Finset.sum_le_sum
            intro R _hR
            exact (expect_two_zeroColor_hits_gt_quarter k l
              (leftNeighbors R) (rightNeighbors R) (hleft R) (hright R)).le
    _ = 𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        ∑ R : Rectangle,
          if omega.1 ∈ zeroColorHitEvent k (leftNeighbors R) ∧
              omega.2 ∈ zeroColorHitEvent l (rightNeighbors R)
          then (1 : Real) else 0 := by
            symm
            exact Finset.expect_sum_comm _ _ _
    _ = 𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        ((twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega).card : Real) := by
          apply Finset.expect_congr rfl
          intro omega _homega
          exact (twoSidedZeroColorSurvivors_card_cast_eq_sum
            k l leftNeighbors rightNeighbors omega).symm


/-- Expectations of a left-only and a right-only load add on a product sample
space. -/
theorem expect_sum_on_product
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A -> Real) (g : B -> Real) :
    (𝔼 z : A × B, (f z.1 + g z.2)) =
      (𝔼 a : A, f a) + (𝔼 b : B, g b) := by
  have hfirst : (𝔼 z : A × B, f z.1) = 𝔼 a : A, f a := by
    calc
      (𝔼 z : A × B, f z.1) =
          𝔼 z : A × B, f z.1 * (1 : Real) := by
            apply Finset.expect_congr rfl
            intro z _hz
            simp
      _ = (𝔼 a : A, f a) * (𝔼 _b : B, (1 : Real)) :=
        expect_independent_product f (fun _b : B => (1 : Real))
      _ = 𝔼 a : A, f a := by simp
  have hsecond : (𝔼 z : A × B, g z.2) = 𝔼 b : B, g b := by
    calc
      (𝔼 z : A × B, g z.2) =
          𝔼 z : A × B, (1 : Real) * g z.2 := by
            apply Finset.expect_congr rfl
            intro z _hz
            simp
      _ = (𝔼 _a : A, (1 : Real)) * (𝔼 b : B, g b) :=
        expect_independent_product (fun _a : A => (1 : Real)) g
      _ = 𝔼 b : B, g b := by simp
  rw [Finset.expect_add_distrib, hfirst, hsecond]

/-- Total number of sampled curves in the two independent colourings. -/
def twoSidedZeroColorLoad
    {alpha beta : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (omega : (alpha -> Fin k) × (beta -> Fin l)) : Real :=
  ((zeroColorSample k omega.1).card : Real) +
    ((zeroColorSample l omega.2).card : Real)

theorem twoSidedZeroColorLoad_nonneg
    {alpha beta : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (omega : (alpha -> Fin k) × (beta -> Fin l)) :
    0 ≤ twoSidedZeroColorLoad k l omega := by
  unfold twoSidedZeroColorLoad
  exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Exact expected total number of sampled curves. -/
theorem expect_twoSidedZeroColorLoad
    {alpha beta : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l] :
    (𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        twoSidedZeroColorLoad k l omega) =
      (Fintype.card alpha : Real) / (k : Real) +
        (Fintype.card beta : Real) / (l : Real) := by
  calc
    (𝔼 omega : (alpha -> Fin k) × (beta -> Fin l),
        twoSidedZeroColorLoad k l omega) =
        (𝔼 omega : alpha -> Fin k,
          ((zeroColorSample k omega).card : Real)) +
        (𝔼 omega : beta -> Fin l,
          ((zeroColorSample l omega).card : Real)) := by
            exact expect_sum_on_product
              (fun omega : alpha -> Fin k =>
                ((zeroColorSample k omega).card : Real))
              (fun omega : beta -> Fin l =>
                ((zeroColorSample l omega).card : Real))
    _ = _ := by rw [expect_zeroColorSample_card, expect_zeroColorSample_card]

/-- Fully explicit deterministic endpoint of the two-colouring sampling
argument: one and the same outcome retains at least one eighth of the
rectangles and samples at most seven times the expected curve load. -/
theorem exists_twoSidedZeroColor_sample_with_eighth_survival_and_sevenfold_load
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (k l : Nat) [NeZero k] [NeZero l]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (hleft : forall R, k ≤ (leftNeighbors R).card)
    (hright : forall R, l ≤ (rightNeighbors R).card) :
    exists omega : (alpha -> Fin k) × (beta -> Fin l),
      (Fintype.card Rectangle : Real) / 8 ≤
          ((twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors omega).card : Real) ∧
        twoSidedZeroColorLoad k l omega ≤
          7 * ((Fintype.card alpha : Real) / (k : Real) +
            (Fintype.card beta : Real) / (l : Real)) := by
  apply exists_sample_with_eighth_survival_and_sevenfold_load
    (survivors := twoSidedZeroColorSurvivors k l leftNeighbors rightNeighbors)
    (load := twoSidedZeroColorLoad k l)
    (sigma := (Fintype.card alpha : Real) / (k : Real) +
      (Fintype.card beta : Real) / (l : Real))
  · intro omega
    exact twoSidedZeroColorLoad_nonneg k l omega
  · positivity
  · exact quarter_le_expect_twoSidedZeroColorSurvivors_card
      k l leftNeighbors rightNeighbors hleft hright
  · rw [expect_twoSidedZeroColorLoad]

#print axioms exists_sample_with_eighth_survival_and_sevenfold_load
#print axioms expect_zeroColorMiss_indicator
#print axioms expect_zeroColorMiss_indicator_lt_half
#print axioms expect_zeroColorHit_indicator
#print axioms expect_zeroColorHit_indicator_gt_half
#print axioms expect_independent_product
#print axioms expect_two_zeroColor_hits_gt_quarter
#print axioms quarter_le_expect_twoSidedZeroColorSurvivors_card
#print axioms expect_twoSidedZeroColorLoad
#print axioms exists_twoSidedZeroColor_sample_with_eighth_survival_and_sevenfold_load

end

end FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

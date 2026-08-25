import FamilyStickyGrounding.FamilyStickyScaleSequenceRatioTelescopeV2
import FamilyStickyGrounding.FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
import FamilyStickyGrounding.FamilyStickyScaleSequenceInsertionTransportV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainLastStageCountingBoundV2

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
open FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence
open FamilyStickyScaleSequenceRatioTelescopeV2
open FamilyStickyScaleSequenceRatioTelescopeV2.FiniteScaleSequence
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
open Submission.Kakeya.Uniformity
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainTwoParameterTerminalNoSplitV2
open FamilyStickyScaleChainBoundedRecursiveStoppingV2

noncomputable section

/-!
# Last-stage scale-factor counting

For `0 < delta < 1` and a positive scale-gap exponent, every literal bad
buffered split creates two child intervals whose adjacent ratios exceed the
fixed floor `delta ^ (-(gapEpsilon^2))`.  Counting intervals above this floor
is therefore a nonnegative integer potential which rises by at least one per
successful split.  Exact adjacent-ratio telescoping bounds that count.

The recursive driver's state does not record its construction history, and
`NoBadAtStageBound` quantifies over every structurally valid state, not only
states reachable from an initial state.  Consequently the final adapter below
keeps the quantitative stage-to-factor invariant explicit.  A proof-relevant
reachability relation then shows how certified literal scale refinements preserve
the invariant.  The concrete hierarchy realization/transport successor remains
an explicit input; no coarse-value deficit is used as a scale-separation
premise.
-/

variable {delta : NNReal} {depth : Nat} {gapEpsilon : Real}

/-- Uniform child-factor floor forced by one non-large buffered split. -/
def lastStageRatioFloor (delta : NNReal) (gapEpsilon : Real) : ENNReal :=
  (delta : ENNReal) ^ (-(gapEpsilon * gapEpsilon))

/-- The factor floor is genuinely greater than one under the scale-gap
hypotheses used by the counting argument. -/
theorem one_lt_lastStageRatioFloor
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon) :
    1 < lastStageRatioFloor delta gapEpsilon := by
  unfold lastStageRatioFloor
  apply ENNReal.one_lt_rpow_of_pos_of_lt_one_of_neg
  · exact ENNReal.coe_pos.mpr delta_pos
  · exact_mod_cast delta_lt_one
  · nlinarith

/-- Every adjacent ratio is at least one. -/
theorem one_le_adjacentRatio_ennreal
    (S : FiniteScaleSequence delta depth) (delta_pos : 0 < delta)
    (m : Fin depth) :
    1 <= (adjacentRatio S m : ENNReal) := by
  have htau_pos : 0 < S.tau m :=
    FamilyStickyScaleSequenceRatioTelescopeV2.FiniteScaleSequence.radius_pos
      S delta_pos m.succ
  have hratio : 1 <= adjacentRatio S m := by
    exact (one_le_div htau_pos).2 (S.tau_le_theta m)
  exact_mod_cast hratio

/-- The buffered upper cutoff forces the upper child ratio to dominate the
old ratio raised to the gap exponent. -/
theorem bufferedFloor_le_upperChildRatio
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (T : FiniteScaleSequence delta (depth + 1))
    (delta_pos : 0 < delta) (buffered : S.IsBuffered gapEpsilon m rho)
    (href : ScaleSequenceRefinesAt S m rho T) :
    (adjacentRatio S m : ENNReal) ^ gapEpsilon <=
      (adjacentRatio T m.castSucc : ENNReal) := by
  let a : ENNReal := (adjacentRatio S m : ENNReal)
  let b : ENNReal := ((S.tau m / S.theta m : NNReal) : ENNReal)
  have htau_pos : 0 < S.tau m :=
    FamilyStickyScaleSequenceRatioTelescopeV2.FiniteScaleSequence.radius_pos
      S delta_pos m.succ
  have htheta_pos : 0 < S.theta m :=
    htau_pos.trans_le (S.tau_le_theta m)
  have hratio_pos : 0 < S.theta m / S.tau m :=
    div_pos htheta_pos htau_pos
  have ha_pos : 0 < a := ENNReal.coe_pos.mpr hratio_pos
  have ha_top : a ≠ ∞ := ENNReal.coe_ne_top
  have hbuffer_pos : 0 <
      (S.tau m : ENNReal) * a ^ gapEpsilon := by
    exact ENNReal.mul_pos (ENNReal.coe_pos.mpr htau_pos).ne'
      (ENNReal.rpow_pos ha_pos ha_top).ne'
  have hrho_pos : 0 < rho := by
    have : (0 : ENNReal) < (rho : ENNReal) :=
      hbuffer_pos.trans_le (by simpa [a, adjacentRatio] using buffered.1)
    exact_mod_cast this
  have hab : a * b = 1 := by
    change ((S.theta m / S.tau m : NNReal) : ENNReal) *
        ((S.tau m / S.theta m : NNReal) : ENNReal) = 1
    rw [← ENNReal.coe_mul, div_mul_div_cancel₀ htau_pos.ne',
      div_self htheta_pos.ne']
    rfl
  have hscaled : a ^ gapEpsilon * (rho : ENNReal) <=
      (S.theta m : ENNReal) := by
    calc
      a ^ gapEpsilon * (rho : ENNReal) <=
          a ^ gapEpsilon *
            ((S.theta m : ENNReal) * b ^ gapEpsilon) := by
        exact mul_le_mul' le_rfl (by simpa [b] using buffered.2)
      _ = (S.theta m : ENNReal) *
          (a ^ gapEpsilon * b ^ gapEpsilon) := by ac_rfl
      _ = (S.theta m : ENNReal) * (a * b) ^ gapEpsilon := by
        rw [ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top
          ENNReal.coe_ne_top gapEpsilon]
      _ = (S.theta m : ENNReal) := by rw [hab]; simp
  have hgap : a ^ gapEpsilon <=
      ((S.theta m / rho : NNReal) : ENNReal) := by
    rw [ENNReal.coe_div hrho_pos.ne']
    exact (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.coe_ne_zero.mpr hrho_pos.ne'))
      (Or.inl ENNReal.coe_ne_top)).2 hscaled
  unfold adjacentRatio
  rw [theta_upperChild_of_refinesAt S m rho T href,
    tau_upperChild_of_refinesAt S m rho T href]
  simpa [a, adjacentRatio] using hgap

/-- The buffered lower cutoff forces the lower child ratio to dominate the
same old-ratio power. -/
theorem bufferedFloor_le_lowerChildRatio
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (T : FiniteScaleSequence delta (depth + 1))
    (delta_pos : 0 < delta) (buffered : S.IsBuffered gapEpsilon m rho)
    (href : ScaleSequenceRefinesAt S m rho T) :
    (adjacentRatio S m : ENNReal) ^ gapEpsilon <=
      (adjacentRatio T m.succ : ENNReal) := by
  let a : ENNReal := (adjacentRatio S m : ENNReal)
  have htau_pos : 0 < S.tau m :=
    FamilyStickyScaleSequenceRatioTelescopeV2.FiniteScaleSequence.radius_pos
      S delta_pos m.succ
  have htheta_pos : 0 < S.theta m :=
    htau_pos.trans_le (S.tau_le_theta m)
  have hratio_pos : 0 < S.theta m / S.tau m :=
    div_pos htheta_pos htau_pos
  have ha_pos : 0 < a := ENNReal.coe_pos.mpr hratio_pos
  have hbuffer_pos : 0 <
      (S.tau m : ENNReal) * a ^ gapEpsilon := by
    exact ENNReal.mul_pos (ENNReal.coe_pos.mpr htau_pos).ne'
      (ENNReal.rpow_pos ha_pos ENNReal.coe_ne_top).ne'
  have hrho_pos : 0 < rho := by
    have : (0 : ENNReal) < (rho : ENNReal) :=
      hbuffer_pos.trans_le (by simpa [a, adjacentRatio] using buffered.1)
    exact_mod_cast this
  have hgap : a ^ gapEpsilon <=
      ((rho / S.tau m : NNReal) : ENNReal) := by
    rw [ENNReal.coe_div htau_pos.ne']
    exact (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.coe_ne_zero.mpr htau_pos.ne'))
      (Or.inl ENNReal.coe_ne_top)).2
        (by simpa [a, adjacentRatio, mul_comm] using buffered.1)
  unfold adjacentRatio
  rw [theta_lowerChild_of_refinesAt S m rho T href,
    tau_lowerChild_of_refinesAt S m rho T href]
  simpa [a, adjacentRatio] using hgap

/-- Non-largeness alone gives the strict uniform old-factor gap which,
after buffering, becomes the child-factor floor. -/
theorem lastStageRatioFloor_lt_bufferedFloor_of_notLarge
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (not_large : Not (S.IsLarge gapEpsilon m)) :
    lastStageRatioFloor delta gapEpsilon <
      (adjacentRatio S m : ENNReal) ^ gapEpsilon := by
  let d : ENNReal := (delta : ENNReal)
  let a : ENNReal := (adjacentRatio S m : ENNReal)
  have htau_pos : 0 < S.tau m :=
    FamilyStickyScaleSequenceRatioTelescopeV2.FiniteScaleSequence.radius_pos
      S delta_pos m.succ
  have htheta_pos : 0 < S.theta m :=
    htau_pos.trans_le (S.tau_le_theta m)
  have hd_pos : 0 < d := ENNReal.coe_pos.mpr delta_pos
  have hd_top : d ≠ ∞ := ENNReal.coe_ne_top
  have hdpow_pos : 0 < d ^ gapEpsilon :=
    ENNReal.rpow_pos hd_pos hd_top
  have hdpow_top : d ^ gapEpsilon ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg gap_pos.le hd_top
  have ha_eq : a =
      (S.theta m : ENNReal) / (S.tau m : ENNReal) := by
    dsimp only [a]
    unfold adjacentRatio
    rw [ENNReal.coe_div htau_pos.ne']
  have hnot : (S.tau m : ENNReal) <
      d ^ gapEpsilon * (S.theta m : ENNReal) := by
    change Not
      (d ^ gapEpsilon * (S.theta m : ENNReal) <=
        (S.tau m : ENNReal)) at not_large
    exact lt_of_not_ge not_large
  have hone_lt_mul : 1 < d ^ gapEpsilon * a := by
    have hdiv : (1 : ENNReal) <
        (d ^ gapEpsilon * (S.theta m : ENNReal)) /
          (S.tau m : ENNReal) := by
      exact (ENNReal.lt_div_iff_mul_lt
        (Or.inl (ENNReal.coe_ne_zero.mpr htau_pos.ne'))
        (Or.inl ENNReal.coe_ne_top)).2 (by simpa using hnot)
    calc
      (1 : ENNReal) <
          (d ^ gapEpsilon * (S.theta m : ENNReal)) /
            (S.tau m : ENNReal) := hdiv
      _ = d ^ gapEpsilon * a := by
        rw [mul_div_assoc, ha_eq]
  have hinv_lt : (d ^ gapEpsilon)⁻¹ < a := by
    have : (1 : ENNReal) / (d ^ gapEpsilon) < a :=
      (ENNReal.div_lt_iff (Or.inl hdpow_pos.ne')
        (Or.inl hdpow_top)).2 (by simpa [mul_comm] using hone_lt_mul)
    simpa [one_div] using this
  have hbase : d ^ (-gapEpsilon) < a := by
    rw [ENNReal.rpow_neg]
    exact hinv_lt
  change d ^ (-(gapEpsilon * gapEpsilon)) < a ^ gapEpsilon
  calc
    d ^ (-(gapEpsilon * gapEpsilon)) =
        (d ^ (-gapEpsilon)) ^ gapEpsilon := by
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    _ < a ^ gapEpsilon := ENNReal.rpow_lt_rpow hbase gap_pos

/-- Combining the two literal scale predicates gives the fixed lower bound
on both child ratios of any certified insertion. -/
theorem lastStageRatioFloor_le_childRatios
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (T : FiniteScaleSequence delta (depth + 1))
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (not_large : Not (S.IsLarge gapEpsilon m))
    (buffered : S.IsBuffered gapEpsilon m rho)
    (href : ScaleSequenceRefinesAt S m rho T) :
    lastStageRatioFloor delta gapEpsilon <=
        (adjacentRatio T m.castSucc : ENNReal) /\
      lastStageRatioFloor delta gapEpsilon <=
        (adjacentRatio T m.succ : ENNReal) := by
  have floor_le_old :=
    (lastStageRatioFloor_lt_bufferedFloor_of_notLarge
      S m delta_pos gap_pos not_large).le
  exact
    ⟨floor_le_old.trans
        (bufferedFloor_le_upperChildRatio
          S m rho T delta_pos buffered href),
      floor_le_old.trans
        (bufferedFloor_le_lowerChildRatio
          S m rho T delta_pos buffered href)⟩

/-- Unsplit ratios before the inserted coordinate are preserved. -/
theorem adjacentRatio_before_eq
    (S : FiniteScaleSequence delta depth) (m j : Fin depth) (rho : NNReal)
    (T : FiniteScaleSequence delta (depth + 1))
    (href : ScaleSequenceRefinesAt S m rho T) (hjm : j < m) :
    adjacentRatio T j.castSucc = adjacentRatio S j := by
  change T.theta (beforeIntervalEmbedding depth j) /
    T.tau (beforeIntervalEmbedding depth j) = S.theta j / S.tau j
  rw [theta_before_eq href hjm, tau_before_eq href hjm]

/-- Unsplit ratios after the inserted coordinate are preserved. -/
theorem adjacentRatio_after_eq
    (S : FiniteScaleSequence delta depth) (m j : Fin depth) (rho : NNReal)
    (T : FiniteScaleSequence delta (depth + 1))
    (href : ScaleSequenceRefinesAt S m rho T) (hmj : m < j) :
    adjacentRatio T j.succ = adjacentRatio S j := by
  change T.theta (afterIntervalEmbedding depth j) /
    T.tau (afterIntervalEmbedding depth j) = S.theta j / S.tau j
  rw [theta_after_eq href hmj, tau_after_eq href hmj]

/-- The finite set of intervals whose adjacent ratio is at least `q`. -/
noncomputable def separatedFactors
    (q : ENNReal) (S : FiniteScaleSequence delta depth) : Finset (Fin depth) := by
  classical
  exact Finset.univ.filter fun m => q <= (adjacentRatio S m : ENNReal)

@[simp]
theorem mem_separatedFactors
    (q : ENNReal) (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    m ∈ separatedFactors q S <-> q <= (adjacentRatio S m : ENNReal) := by
  classical
  simp [separatedFactors]

/-- Nonnegative integer potential: the number of uniformly separated
adjacent factors. -/
noncomputable def separatedFactorCount
    (q : ENNReal) (S : FiniteScaleSequence delta depth) : Nat :=
  (separatedFactors q S).card

/-- Replacing one interval by two `q`-separated children raises the separated
factor potential by at least one.  All other good factors inject through the
canonical interval embedding which skips the lower child. -/
theorem separatedFactorCount_succ_le_of_refinesAt
    (q : ENNReal) (S : FiniteScaleSequence delta depth)
    (m : Fin depth) (rho : NNReal)
    (T : FiniteScaleSequence delta (depth + 1))
    (href : ScaleSequenceRefinesAt S m rho T)
    (upper_good : q <= (adjacentRatio T m.castSucc : ENNReal))
    (lower_good : q <= (adjacentRatio T m.succ : ENNReal)) :
    separatedFactorCount q S + 1 <= separatedFactorCount q T := by
  classical
  let oldGood := separatedFactors q S
  let newGood := separatedFactors q T
  let transport : ↥oldGood -> ↥newGood := fun j => by
    refine ⟨m.succ.succAbove j.1, ?_⟩
    apply (mem_separatedFactors q T _).2
    have hj_good : q <= (adjacentRatio S j.1 : ENNReal) :=
      (mem_separatedFactors q S j.1).1 j.2
    rcases lt_trichotomy j.1 m with hjm | hjm | hmj
    · rw [Fin.succAbove_succ_of_le m j.1 hjm.le,
        adjacentRatio_before_eq S m j.1 rho T href hjm]
      exact hj_good
    · rw [hjm, Fin.succAbove_succ_self]
      exact upper_good
    · rw [Fin.succAbove_succ_of_lt m j.1 hmj,
        adjacentRatio_after_eq S m j.1 rho T href hmj]
      exact hj_good
  have transport_injective : Function.Injective transport := by
    intro x y hxy
    apply Subtype.ext
    apply Fin.succAbove_right_injective
    exact congrArg Subtype.val hxy
  let extra : ↥newGood :=
    ⟨m.succ, (mem_separatedFactors q T m.succ).2 lower_good⟩
  have extra_not_range : extra ∉ Set.range transport := by
    rintro ⟨j, hj⟩
    have hvalue := congrArg Subtype.val hj
    exact (Fin.succAbove_ne m.succ j.1) hvalue
  have hcard : Fintype.card ↥oldGood < Fintype.card ↥newGood :=
    Fintype.card_lt_of_injective_of_notMem transport transport_injective
      extra_not_range
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  dsimp only [oldGood, newGood] at hcard
  have hcount : separatedFactorCount q S < separatedFactorCount q T := by
    simpa only [separatedFactorCount] using hcard
  omega

/-- The exact telescope bounds the contribution of all factors above `q`. -/
theorem pow_separatedFactorCount_le_endpoint
    (q : ENNReal) (S : FiniteScaleSequence delta depth)
    (delta_pos : 0 < delta) :
    q ^ separatedFactorCount q S <= 1 / (delta : ENNReal) := by
  classical
  let good := separatedFactors q S
  calc
    q ^ separatedFactorCount q S = (∏ m ∈ good, q) := by
      simp [separatedFactorCount, good]
    _ <= (∏ m ∈ good, (adjacentRatio S m : ENNReal)) := by
      apply Finset.prod_le_prod'
      intro m hm
      exact (mem_separatedFactors q S m).1 (by simpa [good] using hm)
    _ <= (∏ m : Fin depth, (adjacentRatio S m : ENNReal)) := by
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · exact Finset.subset_univ good
      · intro m _ _
        exact one_le_adjacentRatio_ennreal S delta_pos m
    _ = 1 / (delta : ENNReal) := prod_adjacentRatio_ennreal S delta_pos

/-- A transparent exponent budget implies that `N` floor factors would
already exceed the full endpoint product. -/
theorem endpoint_lt_lastStageRatioFloor_pow
    (N : Nat) (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real)) :
    1 / (delta : ENNReal) < lastStageRatioFloor delta gapEpsilon ^ N := by
  let d : ENNReal := (delta : ENNReal)
  have d_pos : 0 < d := ENNReal.coe_pos.mpr delta_pos
  have d_lt_one : d < 1 := by
    change (delta : ENNReal) < 1
    exact_mod_cast delta_lt_one
  have exponent_lt :
      -(gapEpsilon * gapEpsilon) * (N : Real) < (-1 : Real) := by
    nlinarith
  calc
    1 / (delta : ENNReal) = d ^ (-1 : Real) := by
      simp only [ENNReal.rpow_neg_one, one_div, d]
    _ < d ^ (-(gapEpsilon * gapEpsilon) * (N : Real)) :=
      ENNReal.rpow_lt_rpow_of_exponent_gt d_pos d_lt_one exponent_lt
    _ = lastStageRatioFloor delta gapEpsilon ^ N := by
      change d ^ (-(gapEpsilon * gapEpsilon) * (N : Real)) =
        (d ^ (-(gapEpsilon * gapEpsilon))) ^ N
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]

/-- Therefore every finite scale sequence has strictly fewer than `N`
uniformly separated factors. -/
theorem separatedFactorCount_lt_stageBudget
    (N : Nat) (S : FiniteScaleSequence delta depth)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real)) :
    separatedFactorCount (lastStageRatioFloor delta gapEpsilon) S < N := by
  have endpoint_lt := endpoint_lt_lastStageRatioFloor_pow
    (gapEpsilon := gapEpsilon) N delta_pos delta_lt_one exponent_budget
  have count_le := pow_separatedFactorCount_le_endpoint
    (lastStageRatioFloor delta gapEpsilon) S delta_pos
  have floor_one_le : 1 <= lastStageRatioFloor delta gapEpsilon :=
    (one_lt_lastStageRatioFloor delta_pos delta_lt_one gap_pos).le
  by_contra not_lt
  have N_le_count : N <=
      separatedFactorCount (lastStageRatioFloor delta gapEpsilon) S := by omega
  have hpow := pow_le_pow_right₀ floor_one_le N_le_count
  exact (not_lt_of_ge (hpow.trans count_le)) endpoint_lt

/-! ## Literal bad splits increase the potential -/

universe u

variable {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A literal buffered bad split raises the separated-factor potential by at
least one.  The strict coarse-value deficit in `bad` is not needed for this
purely scale-theoretic conclusion. -/
theorem badSplit_separatedFactorCount_succ_le
    (C : CoherentStickyMultiscaleCover fine)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (gap_pos : 0 < gapEpsilon) :
    separatedFactorCount (lastStageRatioFloor delta gapEpsilon) X.scales + 1 <=
      separatedFactorCount (lastStageRatioFloor delta gapEpsilon)
        (bad.refinedScales C X gap_nonneg delta_pos) := by
  have not_large : Not (X.scales.IsLarge gapEpsilon bad.selectedStep) := by
    exact firstNonLargeStep_not_large
      X.scales gapEpsilon bad.not_all_large
  have href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  have children := lastStageRatioFloor_le_childRatios
    X.scales bad.selectedStep bad.rho
      (bad.refinedScales C X gap_nonneg delta_pos)
      delta_pos gap_pos not_large bad.rho_buffered href
  exact separatedFactorCount_succ_le_of_refinesAt
    (lastStageRatioFloor delta gapEpsilon) X.scales bad.selectedStep bad.rho
      (bad.refinedScales C X gap_nonneg delta_pos) href children.1 children.2

/-! ## Quantitative history invariant -/

/-- A state carries enough separated factors to account for every successful
refinement after stage one.  This is the missing history information not
present in the unrestricted structural driver state. -/
def FactorCountInvariant
    (X : HierarchyStoppingState delta N gapEpsilon eta) : Prop :=
  X.stage - 1 <=
    separatedFactorCount (lastStageRatioFloor delta gapEpsilon) X.scales

/-- Every stage-one state satisfies the factor-count history invariant. -/
theorem factorCountInvariant_of_stage_eq_one
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (stage_eq : X.stage = 1) :
    FactorCountInvariant X := by
  unfold FactorCountInvariant
  omega

/-- A certified literal bad refinement preserves the quantitative history
invariant because both stage and factor count rise by one. -/
theorem factorCountInvariant_toState
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (gap_pos : 0 < gapEpsilon)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (R : OneStepRefinementCertificate C gap_nonneg delta_pos X bad)
    (stage_lt : X.stage < N) (hX : FactorCountInvariant X) :
    FactorCountInvariant
      (R.toState C gap_nonneg delta_pos X bad stage_lt) := by
  have growth := badSplit_separatedFactorCount_succ_le
    C X bad gap_nonneg delta_pos gap_pos
  unfold FactorCountInvariant at hX ⊢
  simp only [OneStepRefinementCertificate.toState_stage,
    OneStepRefinementCertificate.toState_scales, Nat.add_sub_cancel]
  calc
    X.stage = X.stage - 1 + 1 := (Nat.sub_add_cancel X.stage_pos).symm
    _ <= separatedFactorCount (lastStageRatioFloor delta gapEpsilon) X.scales + 1 :=
      Nat.add_le_add_right hX 1
    _ <= separatedFactorCount (lastStageRatioFloor delta gapEpsilon)
        (bad.refinedScales C X gap_nonneg delta_pos) := growth

/-- At the stage bound, a factor-count-valid state cannot contain a literal bad
split: inserting its buffered radius would create at least `N` separated
factors, contradicting the exact telescope bound.  This is an explicit
contradiction adapter, not a renamed no-bad assumption. -/
theorem no_bad_of_factorCountInvariant_at_bound
    (C : CoherentStickyMultiscaleCover fine)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (hX : FactorCountInvariant X) (stage_eq : X.stage = N)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real)) :
    Not (Nonempty (SelectedActualBadSplit C X)) := by
  rintro ⟨bad⟩
  have growth := badSplit_separatedFactorCount_succ_le
    C X bad gap_pos.le delta_pos gap_pos
  have count_lt := separatedFactorCount_lt_stageBudget
    (gapEpsilon := gapEpsilon) N
      (bad.refinedScales C X gap_pos.le delta_pos)
      delta_pos delta_lt_one gap_pos exponent_budget
  unfold FactorCountInvariant at hX
  have N_pos : 1 <= N := by
    rw [← stage_eq]
    exact X.stage_pos
  omega

/-- Invariant-bearing states are precisely the honest state space for the
counting-backed recursive driver. -/
def FactorCountState
    (delta : NNReal) (N : Nat) (gapEpsilon : Real) (eta : Nat -> Real) :=
  {X : HierarchyStoppingState delta N gapEpsilon eta // FactorCountInvariant X}

/-- Embed any stage-one structural state into the counting-backed state
space. -/
def factorCountInitialState
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (stage_eq : X.stage = 1) :
    FactorCountState delta N gapEpsilon eta :=
  ⟨X, factorCountInvariant_of_stage_eq_one X stage_eq⟩


/-! ## Counting-backed bounded recursion -/

/-- Select a literal bad split on the invariant-bearing state space.  At the
last stage, the quantitative contradiction theorem proves there is no split;
below it, the existing analytic hierarchy successor supplies the structural
transition. -/
def countingNext
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (X : FactorCountState delta N gapEpsilon eta) :
    Option (FactorCountState delta N gapEpsilon eta) := by
  classical
  by_cases hbad : Nonempty (SelectedActualBadSplit C X.1)
  · have stage_lt : X.1.stage < N := by
      have stage_le := X.1.stage_le
      by_contra not_lt
      have stage_eq : X.1.stage = N := by omega
      exact (no_bad_of_factorCountInvariant_at_bound
        C X.1 X.2 stage_eq delta_pos delta_lt_one gap_pos exponent_budget) hbad
    let bad : SelectedActualBadSplit C X.1 := Classical.choice hbad
    let R := successor X.1 stage_lt bad
    exact some ⟨R.toState C gap_pos.le delta_pos X.1 bad stage_lt,
      factorCountInvariant_toState
        C gap_pos.le delta_pos gap_pos X.1 bad R stage_lt X.2⟩
  · exact none

/-- The counting-backed successor stops exactly when no literal bad split
exists. -/
theorem countingNext_eq_none_iff_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (X : FactorCountState delta N gapEpsilon eta) :
    countingNext C delta_pos delta_lt_one gap_pos exponent_budget successor X = none
      <-> Not (Nonempty (SelectedActualBadSplit C X.1)) := by
  classical
  simp [countingNext]

/-- Every successful counting-backed transition raises the stage exactly
once. -/
theorem countingNext_stage
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    {X Y : FactorCountState delta N gapEpsilon eta}
    (hnext : countingNext C delta_pos delta_lt_one gap_pos exponent_budget
      successor X = some Y) :
    Y.1.stage = X.1.stage + 1 := by
  classical
  unfold countingNext at hnext
  split at hnext
  next hbad =>
    have state_eq := Option.some.inj hnext
    rw [← state_eq]
    rfl
  next hbad =>
    simp at hnext

/-- The invariant-bearing hierarchy driver is a bounded successor system. -/
def countingBoundedSystem
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos) :
    BoundedSuccessorSystem (FactorCountState delta N gapEpsilon eta) N where
  stage := fun X => X.1.stage
  stage_le := fun X => X.1.stage_le
  next := countingNext C delta_pos delta_lt_one gap_pos exponent_budget successor
  stage_next := countingNext_stage
    C delta_pos delta_lt_one gap_pos exponent_budget successor

/-- The canonical terminal state of the counting-backed hierarchy driver. -/
def countingTerminalState
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    FactorCountState delta N gapEpsilon eta :=
  (countingBoundedSystem C delta_pos delta_lt_one gap_pos
    exponent_budget successor).terminalState initial

/-- The computed counting-backed state is terminal. -/
theorem countingNext_terminalState_eq_none
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    countingNext C delta_pos delta_lt_one gap_pos exponent_budget successor
      (countingTerminalState C delta_pos delta_lt_one gap_pos
        exponent_budget successor initial) = none := by
  exact (countingBoundedSystem C delta_pos delta_lt_one gap_pos
    exponent_budget successor).next_terminalState_eq_none initial

/-- The terminal state is reached in no more than the initial remaining stage
budget.  Every state on this run carries `FactorCountInvariant` by its type. -/
theorem countingTerminalState_reachesIn
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    exists steps, steps <= N - initial.1.stage /\
      (countingBoundedSystem C delta_pos delta_lt_one gap_pos
        exponent_budget successor).ReachesIn steps initial
          (countingTerminalState C delta_pos delta_lt_one gap_pos
            exponent_budget successor initial) := by
  exact (countingBoundedSystem C delta_pos delta_lt_one gap_pos
    exponent_budget successor).terminalState_reachesIn initial

/-- The computed terminal state has no literal bad split, with no separate
`NoBadAtStageBound` input. -/
theorem countingTerminalState_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    Not (Nonempty (SelectedActualBadSplit C
      (countingTerminalState C delta_pos delta_lt_one gap_pos
        exponent_budget successor initial).1)) := by
  exact (countingNext_eq_none_iff_no_bad C delta_pos delta_lt_one gap_pos
    exponent_budget successor _).1
      (countingNext_terminalState_eq_none C delta_pos delta_lt_one gap_pos
        exponent_budget successor initial)


/-- On every non-all-large branch, the computed state satisfies the literal
selected actual terminal no-split predicate. -/
theorem countingTerminalState_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    forall not_all_large : Not
        ((countingTerminalState C delta_pos delta_lt_one gap_pos
          exponent_budget successor initial).1.scales.AllStepsLarge gapEpsilon),
      SelectedActualTerminalNoSplit
        (C.toActualIntervalCovers
          (countingTerminalState C delta_pos delta_lt_one gap_pos
            exponent_budget successor initial).1.scales)
        gapEpsilon eta
        (countingTerminalState C delta_pos delta_lt_one gap_pos
          exponent_budget successor initial).1.stage
        (firstNonLargeStep
          (countingTerminalState C delta_pos delta_lt_one gap_pos
            exponent_budget successor initial).1.scales
          gapEpsilon not_all_large) := by
  exact (no_bad_iff_terminalNoSplit C _).1
    (countingTerminalState_no_bad C delta_pos delta_lt_one gap_pos
      exponent_budget successor initial)


#print axioms one_lt_lastStageRatioFloor
#print axioms lastStageRatioFloor_le_childRatios
#print axioms separatedFactorCount_succ_le_of_refinesAt
#print axioms badSplit_separatedFactorCount_succ_le
#print axioms factorCountInvariant_toState
#print axioms no_bad_of_factorCountInvariant_at_bound
#print axioms countingNext_terminalState_eq_none
#print axioms countingTerminalState_terminalNoSplit
#print axioms pow_separatedFactorCount_le_endpoint
#print axioms endpoint_lt_lastStageRatioFloor_pow
#print axioms separatedFactorCount_lt_stageBudget

end
end FamilyStickyScaleChainLastStageCountingBoundV2

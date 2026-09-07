import Family8Grounding.Family8FiniteTestSimultaneousZeroColorCanonicalResidualV1
import FamilyStickyGrounding.FamilyStickyRandomTestDependentChernoffV1

open scoped BigOperators

namespace Family8ZeroColorHeterogeneousChernoffV1

open Family8GeneralizedKatzTaoMultiplicityV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyRandomFiniteChernoffV3
open FamilyStickyRandomTranslationIncidenceV1
open FamilyStickyRandomTranslationIncidenceV1.TranslationIncidenceModel

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# Heterogeneous Bernoulli tails for one zero-colour sample

A zero-colour sample has one independent coordinate for each original tube.
The load contributed by coordinate i depends on i, so it is not an iid
repetition of one choice-space load.  This file proves the finite product
moment identity directly for coordinate-dependent loads and specializes it to
nonnegative weighted zero-colour sampling.

The final finite union bound costs log of the number of tests through the
condition M * exp(exp(1)-1) < exp(A).  It does not pay the linear-in-M
first-moment penalty of the canonical residual module.
-/

/-- Sum of coordinate-dependent loads on a finite product outcome. -/
def heterogeneousProductLoad
    {coordinate choice : Type} [Fintype coordinate]
    (load : coordinate → choice → Real)
    (omega : coordinate → choice) : Real :=
  ∑ i, load i (omega i)

/-- Exact factorization of the exponential moment for heterogeneous finite
product coordinates. -/
theorem sum_exp_heterogeneousProductLoad
    {coordinate choice : Type} [Fintype coordinate] [DecidableEq coordinate]
    [Fintype choice] [DecidableEq choice]
    (load : coordinate → choice → Real) (lambda : Real) :
    (∑ omega : coordinate → choice,
        Real.exp (lambda * heterogeneousProductLoad load omega)) =
      ∏ i : coordinate,
        ∑ g : choice, Real.exp (lambda * load i g) := by
  unfold heterogeneousProductLoad
  simp_rw [Finset.mul_sum, Real.exp_sum]
  exact
    (Fintype.prod_sum
      (fun i : coordinate =>
        fun g : choice => Real.exp (lambda * load i g))).symm

/-- One coordinate contributes its weight exactly when its colour is zero. -/
def zeroColorCoordinateLoad
    {iota : Type} (k : Nat) [NeZero k]
    (weight : iota → Real) (i : iota) (g : Fin k) : Real :=
  if g = 0 then weight i else 0

theorem heterogeneousProductLoad_zeroColorCoordinateLoad
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (k : Nat) [NeZero k] (weight : iota → Real)
    (omega : iota → Fin k) :
    heterogeneousProductLoad
        (zeroColorCoordinateLoad k weight) omega =
      zeroColorSampleRealWeight k weight omega := by
  rw [zeroColorSampleRealWeight_eq_sum_indicator]
  rfl

/-- Exact heterogeneous product factorization for a weighted zero-colour
sample. -/
theorem sum_exp_zeroColorSampleRealWeight
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (k : Nat) [NeZero k] (weight : iota → Real) (lambda : Real) :
    (∑ omega : iota → Fin k,
        Real.exp (lambda * zeroColorSampleRealWeight k weight omega)) =
      ∏ i : iota,
        ∑ g : Fin k,
          Real.exp (lambda * zeroColorCoordinateLoad k weight i g) := by
  calc
    (∑ omega : iota → Fin k,
        Real.exp (lambda * zeroColorSampleRealWeight k weight omega)) =
      ∑ omega : iota → Fin k,
        Real.exp (lambda *
          heterogeneousProductLoad
            (zeroColorCoordinateLoad k weight) omega) := by
              apply Finset.sum_congr rfl
              intro omega _homega
              rw [heterogeneousProductLoad_zeroColorCoordinateLoad]
    _ = _ := sum_exp_heterogeneousProductLoad
      (zeroColorCoordinateLoad k weight) lambda

/-- Product moment bound for coordinate-dependent weights in the interval
from zero to cap. -/
theorem sum_exp_zeroColorSampleRealWeight_le
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (k : Nat) [NeZero k] (weight : iota → Real)
    {cap lambda : Real}
    (hcap : 0 < cap) (hlambda : 0 ≤ lambda)
    (hweight0 : ∀ i, 0 ≤ weight i)
    (hweightCap : ∀ i, weight i ≤ cap) :
    (∑ omega : iota → Fin k,
        Real.exp (lambda * zeroColorSampleRealWeight k weight omega)) ≤
      (k : Real) ^ Fintype.card iota *
        Real.exp
          (∑ i : iota,
            ((weight i / (k : Real)) / cap) *
              (Real.exp (lambda * cap) - 1)) := by
  classical
  have hkReal : 0 < (k : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne k))
  let f : iota → Real := fun i =>
    ((weight i / (k : Real)) / cap) *
      (Real.exp (lambda * cap) - 1)
  have hcost : 0 ≤ Real.exp (lambda * cap) - 1 := by
    exact sub_nonneg.mpr
      (Real.one_le_exp_iff.mpr (mul_nonneg hlambda hcap.le))
  have hf0 : ∀ i, 0 ≤ f i := by
    intro i
    exact mul_nonneg
      (div_nonneg (div_nonneg (hweight0 i) hkReal.le) hcap.le) hcost
  have hone : ∀ i,
      (∑ g : Fin k,
        Real.exp (lambda * zeroColorCoordinateLoad k weight i g)) ≤
          (k : Real) * (1 + f i) := by
    intro i
    have hsum :
        (∑ g : Fin k, zeroColorCoordinateLoad k weight i g) ≤
          (Fintype.card (Fin k) : Real) *
            (weight i / (k : Real)) := by
      calc
        (∑ g : Fin k, zeroColorCoordinateLoad k weight i g) =
            weight i := by simp [zeroColorCoordinateLoad]
        _ ≤ (Fintype.card (Fin k) : Real) *
            (weight i / (k : Real)) := by
          simp only [Fintype.card_fin]
          rw [show (k : Real) * (weight i / (k : Real)) = weight i by
            field_simp [hkReal.ne']]
    simpa [f] using
      sum_exp_load_le_card_mul_chord
        (zeroColorCoordinateLoad k weight i) hcap hlambda
        (fun g => by
          simp only [zeroColorCoordinateLoad]
          split_ifs
          · exact hweight0 i
          · exact le_rfl)
        (fun g => by
          simp only [zeroColorCoordinateLoad]
          split_ifs
          · exact hweightCap i
          · exact hcap.le)
        hsum
  calc
    (∑ omega : iota → Fin k,
        Real.exp (lambda * zeroColorSampleRealWeight k weight omega)) =
      ∏ i : iota,
        ∑ g : Fin k,
          Real.exp (lambda * zeroColorCoordinateLoad k weight i g) :=
        sum_exp_zeroColorSampleRealWeight k weight lambda
    _ ≤ ∏ i : iota, ((k : Real) * (1 + f i)) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact Finset.sum_nonneg fun g _hg =>
          (Real.exp_pos _).le
      · intro i _hi
        exact hone i
    _ = (k : Real) ^ Fintype.card iota *
        ∏ i : iota, (1 + f i) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ (k : Real) ^ Fintype.card iota *
        Real.exp (∑ i : iota, f i) := by
      apply mul_le_mul_of_nonneg_left
        (Real.prod_one_add_le_exp_sum Finset.univ hf0)
      exact pow_nonneg hkReal.le _
    _ = _ := rfl

/-- Outcomes whose selected weighted load exceeds a fixed threshold. -/
def zeroColorWeightedBadOutcomes
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (k : Nat) [NeZero k] (weight : iota → Real)
    (threshold : Real) : Finset (iota → Fin k) :=
  Finset.univ.filter fun omega =>
    threshold < zeroColorSampleRealWeight k weight omega

/-- Exponential Markov inequality for the literal heterogeneous colouring
space. -/
theorem card_zeroColorWeightedBadOutcomes_mul_exp_le_sum
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (k : Nat) [NeZero k] (weight : iota → Real)
    {lambda threshold : Real} (hlambda : 0 ≤ lambda) :
    ((zeroColorWeightedBadOutcomes k weight threshold).card : Real) *
        Real.exp (lambda * threshold) ≤
      ∑ omega : iota → Fin k,
        Real.exp (lambda * zeroColorSampleRealWeight k weight omega) := by
  classical
  calc
    ((zeroColorWeightedBadOutcomes k weight threshold).card : Real) *
        Real.exp (lambda * threshold) =
      ∑ omega ∈ zeroColorWeightedBadOutcomes k weight threshold,
        Real.exp (lambda * threshold) := by simp
    _ ≤ ∑ omega ∈ zeroColorWeightedBadOutcomes k weight threshold,
        Real.exp (lambda * zeroColorSampleRealWeight k weight omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      rw [zeroColorWeightedBadOutcomes, Finset.mem_filter] at homega
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left homega.2.le hlambda)
    _ ≤ ∑ omega : iota → Fin k,
        Real.exp (lambda * zeroColorSampleRealWeight k weight omega) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun _omega _huniv _hnot => (Real.exp_pos _).le)

/-- Fixed-test weighted Bernoulli tail.  The total expected load is at most
cap, and the threshold is A times cap. -/
theorem card_zeroColorWeightedBadOutcomes_mul_exp_le_fixed
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (k : Nat) [NeZero k] (weight : iota → Real)
    {cap A : Real}
    (hcap : 0 < cap)
    (hweight0 : ∀ i, 0 ≤ weight i)
    (hweightCap : ∀ i, weight i ≤ cap)
    (hscale : (∑ i : iota, weight i) / (k : Real) ≤ cap) :
    ((zeroColorWeightedBadOutcomes k weight (A * cap)).card : Real) *
        Real.exp A ≤
      (k : Real) ^ Fintype.card iota *
        Real.exp (Real.exp 1 - 1) := by
  have hkReal : 0 < (k : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne k))
  have hcost : 0 ≤ Real.exp 1 - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr zero_le_one)
  have hmeanRatio :
      ((∑ i : iota, weight i) / (k : Real)) / cap ≤ 1 :=
    (div_le_one hcap).mpr hscale
  have hsumFactor :
      (∑ i : iota,
        ((weight i / (k : Real)) / cap) * (Real.exp 1 - 1)) ≤
          Real.exp 1 - 1 := by
    calc
      (∑ i : iota,
          ((weight i / (k : Real)) / cap) * (Real.exp 1 - 1)) =
        (((∑ i : iota, weight i) / (k : Real)) / cap) *
          (Real.exp 1 - 1) := by
            rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_div]
      _ ≤ 1 * (Real.exp 1 - 1) :=
        mul_le_mul_of_nonneg_right hmeanRatio hcost
      _ = Real.exp 1 - 1 := one_mul _
  have hmoment :
      (∑ omega : iota → Fin k,
          Real.exp (cap⁻¹ *
            zeroColorSampleRealWeight k weight omega)) ≤
        (k : Real) ^ Fintype.card iota *
          Real.exp (Real.exp 1 - 1) := by
    calc
      (∑ omega : iota → Fin k,
          Real.exp (cap⁻¹ *
            zeroColorSampleRealWeight k weight omega)) ≤
        (k : Real) ^ Fintype.card iota *
          Real.exp
            (∑ i : iota,
              ((weight i / (k : Real)) / cap) *
                (Real.exp (cap⁻¹ * cap) - 1)) :=
        sum_exp_zeroColorSampleRealWeight_le k weight hcap
          (inv_nonneg.mpr hcap.le) hweight0 hweightCap
      _ = (k : Real) ^ Fintype.card iota *
          Real.exp
            (∑ i : iota,
              ((weight i / (k : Real)) / cap) *
                (Real.exp 1 - 1)) := by
            rw [inv_mul_cancel₀ hcap.ne']
      _ ≤ (k : Real) ^ Fintype.card iota *
          Real.exp (Real.exp 1 - 1) := by
            gcongr
  have hmarkov :=
    card_zeroColorWeightedBadOutcomes_mul_exp_le_sum
      k weight (lambda := cap⁻¹) (threshold := A * cap)
      (inv_nonneg.mpr hcap.le)
  have harg : cap⁻¹ * (A * cap) = A := by
    field_simp [hcap.ne']
  rw [harg] at hmarkov
  exact hmarkov.trans hmoment

/-- A logarithmic-cost finite union bound over coordinate-dependent weighted
loads. -/
theorem exists_zeroColorSample_all_weightedLoads_le
    {iota test : Type} [Fintype iota] [DecidableEq iota]
    [Fintype test] [DecidableEq test]
    (tests : Finset test) (k : Nat) [NeZero k]
    (weight : test → iota → Real) (cap : test → Real) (A : Real)
    (hcap : ∀ K ∈ tests, 0 < cap K)
    (hweight0 : ∀ K ∈ tests, ∀ i, 0 ≤ weight K i)
    (hweightCap : ∀ K ∈ tests, ∀ i, weight K i ≤ cap K)
    (hscale : ∀ K ∈ tests,
      (∑ i : iota, weight K i) / (k : Real) ≤ cap K)
    (htailRoom :
      (tests.card : Real) * Real.exp (Real.exp 1 - 1) < Real.exp A) :
    ∃ omega : iota → Fin k,
      ∀ K ∈ tests,
        zeroColorSampleRealWeight k (weight K) omega ≤ A * cap K := by
  classical
  let bad : Finset (iota → Fin k) :=
    tests.biUnion fun K =>
      zeroColorWeightedBadOutcomes k (weight K) (A * cap K)
  have htail :
      (bad.card : Real) * Real.exp A ≤
        (tests.card : Real) *
          ((k : Real) ^ Fintype.card iota *
            Real.exp (Real.exp 1 - 1)) := by
    calc
      (bad.card : Real) * Real.exp A ≤
        ((∑ K ∈ tests,
          (zeroColorWeightedBadOutcomes k
            (weight K) (A * cap K)).card : Nat) : Real) *
              Real.exp A := by
        gcongr
        exact Finset.card_biUnion_le
      _ = ∑ K ∈ tests,
          ((zeroColorWeightedBadOutcomes k
            (weight K) (A * cap K)).card : Real) *
              Real.exp A := by
        push_cast
        rw [Finset.sum_mul]
      _ ≤ ∑ _K ∈ tests,
          (k : Real) ^ Fintype.card iota *
            Real.exp (Real.exp 1 - 1) := by
        apply Finset.sum_le_sum
        intro K hK
        exact card_zeroColorWeightedBadOutcomes_mul_exp_le_fixed
          k (weight K) (hcap K hK) (hweight0 K hK)
          (hweightCap K hK) (hscale K hK)
      _ = (tests.card : Real) *
          ((k : Real) ^ Fintype.card iota *
            Real.exp (Real.exp 1 - 1)) := by simp
  have hkReal : 0 < (k : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne k))
  have hspacePos : 0 < (k : Real) ^ Fintype.card iota :=
    pow_pos hkReal _
  have hbadMul :
      (bad.card : Real) * Real.exp A <
        (k : Real) ^ Fintype.card iota * Real.exp A := by
    calc
      (bad.card : Real) * Real.exp A ≤
        (tests.card : Real) *
          ((k : Real) ^ Fintype.card iota *
            Real.exp (Real.exp 1 - 1)) := htail
      _ = (k : Real) ^ Fintype.card iota *
          ((tests.card : Real) * Real.exp (Real.exp 1 - 1)) := by ring
      _ < (k : Real) ^ Fintype.card iota * Real.exp A :=
        mul_lt_mul_of_pos_left htailRoom hspacePos
  have hbadCardReal :
      (bad.card : Real) < (k : Real) ^ Fintype.card iota :=
    lt_of_mul_lt_mul_right hbadMul (Real.exp_pos A).le
  have hspaceCard :
      ((Finset.univ : Finset (iota → Fin k)).card : Real) =
        (k : Real) ^ Fintype.card iota := by simp
  have hbadCard :
      bad.card < (Finset.univ : Finset (iota → Fin k)).card := by
    exact_mod_cast (show (bad.card : Real) <
      ((Finset.univ : Finset (iota → Fin k)).card : Real) by
        rw [hspaceCard]
        exact hbadCardReal)
  have hproper : bad ⊂
      (Finset.univ : Finset (iota → Fin k)) :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ bad, fun heq =>
        (ne_of_lt hbadCard) (congrArg Finset.card heq)⟩
  obtain ⟨omega, _homega, homegaBad⟩ :=
    Finset.exists_of_ssubset hproper
  refine ⟨omega, ?_⟩
  intro K hK
  have hnot : omega ∉
      zeroColorWeightedBadOutcomes k (weight K) (A * cap K) := by
    intro homegaK
    exact homegaBad
      (Finset.mem_biUnion.mpr ⟨K, hK, homegaK⟩)
  simpa [zeroColorWeightedBadOutcomes] using hnot

#print axioms sum_exp_heterogeneousProductLoad
#print axioms sum_exp_zeroColorSampleRealWeight
#print axioms sum_exp_zeroColorSampleRealWeight_le
#print axioms card_zeroColorWeightedBadOutcomes_mul_exp_le_sum
#print axioms card_zeroColorWeightedBadOutcomes_mul_exp_le_fixed
#print axioms exists_zeroColorSample_all_weightedLoads_le

end

end Family8ZeroColorHeterogeneousChernoffV1

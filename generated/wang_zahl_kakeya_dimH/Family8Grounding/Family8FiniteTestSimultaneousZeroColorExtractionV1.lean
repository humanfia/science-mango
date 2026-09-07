import Family8Grounding.Family8GeneralizedKatzTaoMultiplicityV1
import FamilyStickyGrounding.FamilyStickyHierarchyFiniteHullAllConvexAdapterV1

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8FiniteTestSimultaneousZeroColorExtractionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyHierarchyFiniteHullAllConvexAdapterV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# One zero-colour outcome for a finite family of concentration tests

The score below is the elementary finite-union-bound argument in a form that
does not postulate a good subfamily.  A single outcome is selected by averaging
the retained value minus a normalized sum of all bad loads.  Therefore the
same outcome retains the prescribed value, obeys the cardinality cap, and
obeys every test-body cap.

The exact normalized budget is exposed.  For the canonical-hull catalogue its
number of summands can be exponential in the original family cardinality, so
this lemma alone does not claim the polynomial-loss generalized Katz--Tao
estimate.
-/

/-- The sum of the normalized cardinality load and all finite test loads. -/
def finiteTestNormalizedLoad
    {Omega test : Type} [Fintype test] [DecidableEq test]
    (tests : Finset test)
    (cardinalLoad : Omega → Real) (testLoad : test → Omega → Real)
    (cardinalThreshold : Real) (testThreshold : test → Real)
    (omega : Omega) : Real :=
  cardinalLoad omega / cardinalThreshold +
    ∑ K ∈ tests, testLoad K omega / testThreshold K

/-- Expectation commutes with the finite normalized-load sum. -/
theorem expect_finiteTestNormalizedLoad
    {Omega test : Type} [Fintype Omega] [Fintype test]
    [DecidableEq test]
    (tests : Finset test)
    (cardinalLoad : Omega → Real) (testLoad : test → Omega → Real)
    (cardinalThreshold : Real) (testThreshold : test → Real) :
    (𝔼 omega : Omega,
        finiteTestNormalizedLoad tests cardinalLoad testLoad
          cardinalThreshold testThreshold omega) =
      (𝔼 omega : Omega, cardinalLoad omega) / cardinalThreshold +
        ∑ K ∈ tests,
          (𝔼 omega : Omega, testLoad K omega) / testThreshold K := by
  classical
  unfold finiteTestNormalizedLoad
  rw [Finset.expect_add_distrib]
  congr 1
  · exact (Finset.expect_div Finset.univ cardinalLoad cardinalThreshold).symm
  · calc
      (𝔼 omega : Omega,
          ∑ K ∈ tests, testLoad K omega / testThreshold K) =
          ∑ K ∈ tests,
            𝔼 omega : Omega, testLoad K omega / testThreshold K := by
              exact Finset.expect_sum_comm Finset.univ tests _
      _ = ∑ K ∈ tests,
          (𝔼 omega : Omega, testLoad K omega) / testThreshold K := by
            apply Finset.sum_congr rfl
            intro K _hK
            exact
              (Finset.expect_div Finset.univ (testLoad K)
                (testThreshold K)).symm

/-- The penalized score used to select one simultaneous good outcome. -/
def finiteTestScore
    {Omega test : Type} [Fintype test] [DecidableEq test]
    (tests : Finset test)
    (value cardinalLoad : Omega → Real)
    (testLoad : test → Omega → Real)
    (valuePenalty cardinalThreshold : Real)
    (testThreshold : test → Real) (omega : Omega) : Real :=
  value omega -
    valuePenalty *
      finiteTestNormalizedLoad tests cardinalLoad testLoad
        cardinalThreshold testThreshold omega

/-- Exact first moment of the penalized score. -/
theorem expect_finiteTestScore
    {Omega test : Type} [Fintype Omega] [Fintype test]
    [DecidableEq test]
    (tests : Finset test)
    (value cardinalLoad : Omega → Real)
    (testLoad : test → Omega → Real)
    (valuePenalty cardinalThreshold : Real)
    (testThreshold : test → Real) :
    (𝔼 omega : Omega,
        finiteTestScore tests value cardinalLoad testLoad
          valuePenalty cardinalThreshold testThreshold omega) =
      (𝔼 omega : Omega, value omega) -
        valuePenalty *
          ((𝔼 omega : Omega, cardinalLoad omega) / cardinalThreshold +
            ∑ K ∈ tests,
              (𝔼 omega : Omega, testLoad K omega) /
                testThreshold K) := by
  classical
  unfold finiteTestScore
  rw [Finset.expect_sub_distrib]
  rw [← Finset.mul_expect]
  rw [expect_finiteTestNormalizedLoad]

/-- A genuine simultaneous finite-test extraction.

The strict inequality valueCap < valuePenalty makes every violation have
negative score, while the selected score is nonnegative.  No good outcome or
final concentration conclusion is supplied as an input. -/
theorem exists_finiteTest_simultaneous_of_expectation_room
    {Omega test : Type} [Fintype Omega] [Nonempty Omega]
    [Fintype test] [DecidableEq test]
    (tests : Finset test)
    (value cardinalLoad : Omega → Real)
    (testLoad : test → Omega → Real)
    (valueCap valuePenalty retainedTarget cardinalThreshold : Real)
    (testThreshold : test → Real)
    (hvalueCap0 : 0 ≤ valueCap)
    (hvalueCap : ∀ omega, value omega ≤ valueCap)
    (hcardinalLoad : ∀ omega, 0 ≤ cardinalLoad omega)
    (htestLoad : ∀ K omega, 0 ≤ testLoad K omega)
    (hretainedTarget : 0 ≤ retainedTarget)
    (hcardinalThreshold : 0 < cardinalThreshold)
    (htestThreshold : ∀ K ∈ tests, 0 < testThreshold K)
    (hvaluePenalty : valueCap < valuePenalty)
    (hroom :
      retainedTarget ≤
        (𝔼 omega : Omega, value omega) -
          valuePenalty *
            ((𝔼 omega : Omega, cardinalLoad omega) /
                cardinalThreshold +
              ∑ K ∈ tests,
                (𝔼 omega : Omega, testLoad K omega) /
                  testThreshold K)) :
    ∃ omega : Omega,
      retainedTarget ≤ value omega ∧
        cardinalLoad omega ≤ cardinalThreshold ∧
          ∀ K ∈ tests, testLoad K omega ≤ testThreshold K := by
  classical
  let score : Omega → Real :=
    finiteTestScore tests value cardinalLoad testLoad
      valuePenalty cardinalThreshold testThreshold
  have hOmega : (Finset.univ : Finset Omega).Nonempty := by
    let omega : Omega := Classical.choice inferInstance
    exact ⟨omega, Finset.mem_univ omega⟩
  obtain ⟨omega, _homega, homega⟩ :=
    Finset.exists_le_of_le_expect hOmega
      (show (𝔼 omega : Omega, score omega) ≤
          𝔼 omega : Omega, score omega from le_rfl)
  have hscoreExpectation :
      (𝔼 omega : Omega, score omega) =
        (𝔼 omega : Omega, value omega) -
          valuePenalty *
            ((𝔼 omega : Omega, cardinalLoad omega) /
                cardinalThreshold +
              ∑ K ∈ tests,
                (𝔼 omega : Omega, testLoad K omega) /
                  testThreshold K) := by
    exact expect_finiteTestScore tests value cardinalLoad testLoad
      valuePenalty cardinalThreshold testThreshold
  have hscore : retainedTarget ≤ score omega :=
    (hroom.trans_eq hscoreExpectation.symm).trans homega
  have hvaluePenalty_pos : 0 < valuePenalty :=
    lt_of_le_of_lt hvalueCap0 hvaluePenalty
  have hnormalized_nonneg :
      0 ≤ finiteTestNormalizedLoad tests cardinalLoad testLoad
        cardinalThreshold testThreshold omega := by
    apply add_nonneg
    · exact div_nonneg (hcardinalLoad omega) hcardinalThreshold.le
    · exact Finset.sum_nonneg fun K hK =>
        div_nonneg (htestLoad K omega) (htestThreshold K hK).le
  have hvalue : retainedTarget ≤ value omega := by
    exact hscore.trans (sub_le_self _
      (mul_nonneg hvaluePenalty_pos.le hnormalized_nonneg))
  have no_normalized_violation
      (hviolation :
        1 < finiteTestNormalizedLoad tests cardinalLoad testLoad
          cardinalThreshold testThreshold omega) : False := by
    have hscore_neg : score omega < 0 := by
      dsimp [score]
      unfold finiteTestScore
      have hvalue_le := hvalueCap omega
      nlinarith
    exact (not_lt_of_ge hretainedTarget) (hscore.trans_lt hscore_neg)
  have hcardinal : cardinalLoad omega ≤ cardinalThreshold := by
    by_contra hnot
    have hratio :
        1 < cardinalLoad omega / cardinalThreshold := by
      apply (lt_div_iff₀ hcardinalThreshold).2
      simpa using (lt_of_not_ge hnot)
    have htestSum_nonneg :
        0 ≤ ∑ K ∈ tests, testLoad K omega / testThreshold K :=
      Finset.sum_nonneg fun K hK =>
        div_nonneg (htestLoad K omega) (htestThreshold K hK).le
    apply no_normalized_violation
    exact hratio.trans_le (le_add_of_nonneg_right htestSum_nonneg)
  refine ⟨omega, hvalue, hcardinal, ?_⟩
  intro K hK
  by_contra hnot
  have hratio : 1 < testLoad K omega / testThreshold K := by
    apply (lt_div_iff₀ (htestThreshold K hK)).2
    simpa using (lt_of_not_ge hnot)
  have hterm_le :
      testLoad K omega / testThreshold K ≤
        ∑ L ∈ tests, testLoad L omega / testThreshold L := by
    exact Finset.single_le_sum
      (fun L hL => div_nonneg (htestLoad L omega)
        (htestThreshold L hL).le) hK
  have hcardRatio_nonneg :
      0 ≤ cardinalLoad omega / cardinalThreshold :=
    div_nonneg (hcardinalLoad omega) hcardinalThreshold.le
  apply no_normalized_violation
  exact hratio.trans_le (hterm_le.trans (le_add_of_nonneg_left hcardRatio_nonneg))

/-- Canonical hull tests also reduce active-subfamily Katz--Tao control to a
fixed finite catalogue built before the random sample is chosen. -/
theorem isKatzTaoOn_of_canonicalHullTests
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (F : ConvexFamily iota) (selected : Finset iota) (A : ENNReal)
    (hfinite :
      ∀ q : Fin (Fintype.card
          (CanonicalHullTests.Index F)),
        containedMassOn F selected (CanonicalHullTests.body F q) ≤
          A * volume (CanonicalHullTests.body F q : Set Space)) :
    IsKatzTaoOn A F selected := by
  classical
  let _ : DecidableEq iota := Classical.decEq iota
  intro K
  let activeInside : Finset iota :=
    selected ∩ containedIndices F K
  by_cases hactive : activeInside.Nonempty
  · have hcandidate :
        activeInside ∈ hullCandidates (Finset.univ : Finset iota) := by
      exact mem_hullCandidates.mpr
        ⟨Finset.subset_univ activeInside, hactive⟩
    let q : Fin (Fintype.card (CanonicalHullTests.Index F)) :=
      CanonicalHullTests.indexEquivFin F ⟨activeInside, hcandidate⟩
    have hq : CanonicalHullTests.subsetAt F q = activeInside := by
      exact CanonicalHullTests.subsetAt_indexEquivFin
        F activeInside hcandidate
    have hbody :
        (CanonicalHullTests.body F q : Set Space) ⊆ (K : Set Space) := by
      rw [CanonicalHullTests.body, hq]
      apply hullContainer_subset F hactive
      intro i hi
      have hi' : i ∈ selected ∩ containedIndices F K := by
        simpa only [activeInside] using hi
      exact (mem_containedIndices F K i).mp (Finset.mem_inter.mp hi').2
    have hindices :
        selected ∩ containedIndices F (CanonicalHullTests.body F q) =
          selected ∩ containedIndices F K := by
      ext i
      simp only [Finset.mem_inter, mem_containedIndices]
      constructor
      · intro hi
        exact ⟨hi.1, hi.2.trans hbody⟩
      · intro hi
        refine ⟨hi.1, ?_⟩
        rw [CanonicalHullTests.body, hq]
        have hiActive : i ∈ activeInside := by
          simp only [activeInside, Finset.mem_inter, mem_containedIndices]
          exact hi
        exact body_subset_hullContainer F
          hiActive hactive
    calc
      containedMassOn F selected K =
          containedMassOn F selected (CanonicalHullTests.body F q) := by
            unfold containedMassOn
            apply Finset.sum_congr hindices.symm
            intro i _hi
            rfl
      _ ≤ A * volume (CanonicalHullTests.body F q : Set Space) :=
        hfinite q
      _ ≤ A * volume (K : Set Space) := by
        gcongr
  · have hempty : activeInside = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    have hempty' : selected ∩ containedIndices F K = ∅ := by
      simpa only [activeInside] using hempty
    unfold containedMassOn
    rw [hempty']
    simp

#print axioms expect_finiteTestNormalizedLoad
#print axioms expect_finiteTestScore
#print axioms exists_finiteTest_simultaneous_of_expectation_room
#print axioms isKatzTaoOn_of_canonicalHullTests

end

end Family8FiniteTestSimultaneousZeroColorExtractionV1

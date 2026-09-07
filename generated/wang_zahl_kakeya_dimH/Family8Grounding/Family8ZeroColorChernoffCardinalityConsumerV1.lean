import Family8Grounding.Family8ZeroColorChernoffSimultaneousSelectionV1

open scoped BigOperators

namespace Family8ZeroColorChernoffCardinalityConsumerV1

open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorChernoffSimultaneousSelectionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# Cardinality as one distinguished Chernoff test

The unit coordinate weight has zero-colour load equal to the sampled
cardinality.  Adding it as the `none` member of an `Option test` catalogue
therefore produces retention, a cardinal cap, and every geometric test cap for
one and the same colouring.
-/

def withCardinalityTests
    {test : Type} [DecidableEq test]
    (tests : Finset test) : Finset (Option test) :=
  insert none (tests.image some)

def withCardinalityWeight
    {iota test : Type} (weight : test → iota → Real) :
    Option test → iota → Real
  | none => fun _ => 1
  | some K => weight K

def withCardinalityCap
    {test : Type} (cardinalCap : Real) (cap : test → Real) :
    Option test → Real
  | none => cardinalCap
  | some K => cap K

theorem card_withCardinalityTests
    {test : Type} [DecidableEq test] (tests : Finset test) :
    (withCardinalityTests tests).card = tests.card + 1 := by
  rw [withCardinalityTests, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ (Option.some_injective test)]
  · simp

/-- Simultaneous retention, sampled-cardinality control, and all finite test
caps.  The catalogue cost is exactly `tests.card + 1`. -/
theorem exists_zeroColorSample_retention_card_and_all_weightedLoads_le
    {iota test : Type} [Fintype iota] [DecidableEq iota]
    [Fintype test] [DecidableEq test]
    (tests : Finset test) (k : Nat) [NeZero k]
    (retainedWeight : iota → Real)
    (weight : test → iota → Real)
    (cardinalCap : Real) (cap : test → Real) (A : Real)
    (hretained0 : ∀ i, 0 ≤ retainedWeight i)
    (hcardinalCap : 0 < cardinalCap)
    (honeCardinalCap : 1 ≤ cardinalCap)
    (hcardinalScale :
      (Fintype.card iota : Real) / (k : Real) ≤ cardinalCap)
    (hcap : ∀ K ∈ tests, 0 < cap K)
    (hweight0 : ∀ K ∈ tests, ∀ i, 0 ≤ weight K i)
    (hweightCap : ∀ K ∈ tests, ∀ i, weight K i ≤ cap K)
    (hscale : ∀ K ∈ tests,
      (∑ i : iota, weight K i) / (k : Real) ≤ cap K)
    (htailRoom :
      (2 * (k : Real)) *
          (((tests.card + 1 : Nat) : Real) *
            Real.exp (Real.exp 1 - 1)) <
        Real.exp A) :
    ∃ omega : iota → Fin k,
      (∑ i : iota, retainedWeight i) / (2 * (k : Real)) ≤
          zeroColorSampleRealWeight k retainedWeight omega ∧
        ((zeroColorSample k omega).card : Real) ≤ A * cardinalCap ∧
        ∀ K ∈ tests,
          zeroColorSampleRealWeight k (weight K) omega ≤ A * cap K := by
  classical
  let allTests : Finset (Option test) := withCardinalityTests tests
  let allWeight : Option test → iota → Real :=
    withCardinalityWeight weight
  let allCap : Option test → Real :=
    withCardinalityCap cardinalCap cap
  have hAllCap : ∀ q ∈ allTests, 0 < allCap q := by
    intro q hq
    cases q with
    | none => exact hcardinalCap
    | some K =>
        apply hcap K
        simpa [allTests, withCardinalityTests] using hq
  have hAllWeight0 : ∀ q ∈ allTests, ∀ i, 0 ≤ allWeight q i := by
    intro q hq i
    cases q with
    | none => simp [allWeight, withCardinalityWeight]
    | some K =>
        apply hweight0 K
        simpa [allTests, withCardinalityTests] using hq
  have hAllWeightCap : ∀ q ∈ allTests, ∀ i,
      allWeight q i ≤ allCap q := by
    intro q hq i
    cases q with
    | none => simpa [allWeight, allCap, withCardinalityWeight,
        withCardinalityCap] using honeCardinalCap
    | some K =>
        apply hweightCap K
        simpa [allTests, withCardinalityTests] using hq
  have hAllScale : ∀ q ∈ allTests,
      (∑ i : iota, allWeight q i) / (k : Real) ≤ allCap q := by
    intro q hq
    cases q with
    | none =>
        simpa [allWeight, allCap, withCardinalityWeight,
          withCardinalityCap] using hcardinalScale
    | some K =>
        apply hscale K
        simpa [allTests, withCardinalityTests] using hq
  have hAllRoom :
      (2 * (k : Real)) *
          ((allTests.card : Real) * Real.exp (Real.exp 1 - 1)) <
        Real.exp A := by
    simpa [allTests, card_withCardinalityTests] using htailRoom
  obtain ⟨omega, hretained, hall⟩ :=
    exists_zeroColorSample_retention_and_all_weightedLoads_le
      allTests k retainedWeight allWeight allCap A hretained0
      hAllCap hAllWeight0 hAllWeightCap hAllScale hAllRoom
  refine ⟨omega, hretained, ?_, ?_⟩
  · have hcard := hall none (by simp [allTests, withCardinalityTests])
    have hunit :
        zeroColorSampleRealWeight k (fun _ : iota => (1 : Real)) omega =
          ((zeroColorSample k omega).card : Real) := by
      rw [zeroColorSampleRealWeight_eq_sum_indicator]
      exact (zeroColorSample_card_cast_eq_sum k omega).symm
    simpa [allWeight, allCap, withCardinalityWeight,
      withCardinalityCap, hunit] using hcard
  · intro K hK
    have htest := hall (some K)
      (by simp [allTests, withCardinalityTests, hK])
    simpa [allWeight, allCap, withCardinalityWeight,
      withCardinalityCap] using htest

#print axioms card_withCardinalityTests
#print axioms exists_zeroColorSample_retention_card_and_all_weightedLoads_le

end

end Family8ZeroColorChernoffCardinalityConsumerV1

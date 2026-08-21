import Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open StatisticLevelRestriction

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace ComparableMultiplicityBuckets

variable {ι : Type*} {F : ConvexFamily ι}

/-!
# Zero/dyadic comparable multiplicity buckets

The label `0` is reserved for actual zero multiplicity. Positive natural
values are grouped into half-open bands `[B, 2 * B)`, where `B` is a power of
two. Consequently a statistic bounded by `M` has only `log₂ M + 2` buckets.
-/

def comparableLabel (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.log 2 n + 1

def comparableBase (b : ℕ) : ℕ :=
  if b = 0 then 0 else 2 ^ (b - 1)

def ZeroOrComparable (B n : ℕ) : Prop :=
  (B = 0 ∧ n = 0) ∨
    (0 < B ∧ B ≤ n ∧ n < 2 * B)

theorem comparableLabel_le_of_le {n M : ℕ} (hnM : n ≤ M) :
    comparableLabel n ≤ Nat.log 2 M + 1 := by
  unfold comparableLabel
  split_ifs with hn
  · omega
  · exact Nat.add_le_add_right (Nat.log_mono_right hnM) 1

theorem zeroOrComparable_of_comparableLabel_eq {n b : ℕ}
    (hlabel : comparableLabel n = b) :
    ZeroOrComparable (comparableBase b) n := by
  by_cases hn : n = 0
  · subst n
    have hb : b = 0 := by simpa [comparableLabel] using hlabel.symm
    left
    simp [hb, comparableBase]
  · have hb0 : b ≠ 0 := by
      intro hb
      rw [hb] at hlabel
      simp [comparableLabel, hn] at hlabel
    right
    have hlog : Nat.log 2 n + 1 = b := by
      simpa [comparableLabel, hn] using hlabel
    have hbase : comparableBase b = 2 ^ Nat.log 2 n := by
      simp [comparableBase, ← hlog]
    refine ⟨?_, ?_, ?_⟩
    · rw [hbase]
      positivity
    · rw [hbase]
      exact Nat.pow_log_le_self 2 hn
    · rw [hbase]
      have hupper := Nat.lt_pow_succ_log_self Nat.one_lt_two n
      simpa [pow_succ, Nat.mul_comm] using hupper

theorem ZeroOrComparable.le_twice {B n : ℕ}
    (h : ZeroOrComparable B n) : n ≤ 2 * B := by
  rcases h with hzero | hpos
  · simp [hzero.1, hzero.2]
  · exact Nat.le_of_lt hpos.2.2

theorem ZeroOrComparable.recompute
    {B frozen recomputed : ℕ}
    (hfrozen : ZeroOrComparable B frozen)
    (hle : recomputed ≤ frozen)
    (hlower : 0 < B → B ≤ recomputed) :
    ZeroOrComparable B recomputed := by
  rcases hfrozen with hzero | hpos
  · left
    refine ⟨hzero.1, ?_⟩
    omega
  · right
    exact ⟨hpos.1, hlower hpos.1, lt_of_le_of_lt hle hpos.2.2⟩

theorem measurable_nat_of_measurableSet_eq
    (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) :
    Measurable stat := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet {x | stat x = n}
  exact hstat n

theorem measurableSet_comparableLabel_eq
    (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) (b : ℕ) :
    MeasurableSet {x | comparableLabel (stat x) = b} := by
  have hm : Measurable (fun x ↦ comparableLabel (stat x)) :=
    (measurable_of_countable comparableLabel).comp
      (measurable_nat_of_measurableSet_eq stat hstat)
  exact hm (measurableSet_singleton b)

def restrictComparableStatisticBucket [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n}) (b : ℕ) : Shading F :=
  restrictStatisticLevel Y (fun x ↦ comparableLabel (stat x))
    (measurableSet_comparableLabel_eq stat hstat) b

theorem exists_restrictComparableStatisticBucket_with_large_mass [Fintype ι]
    (Y : Shading F) (stat : Space → ℕ) (M : ℕ)
    (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (hbound : ∀ x ∈ Y.shadedUnion, stat x ≤ M) :
    ∃ b ∈ Finset.range (Nat.log 2 M + 2),
      Y.shadingMass ≤
        (Nat.log 2 M + 2) •
          (restrictComparableStatisticBucket Y stat hstat b).shadingMass ∧
      ∀ x ∈ (restrictComparableStatisticBucket Y stat hstat b).shadedUnion,
        ZeroOrComparable (comparableBase b) (stat x) := by
  obtain ⟨b, hb, hmass, hconstant⟩ :=
    exists_restrictStatisticLevel_with_large_mass Y
      (fun x ↦ comparableLabel (stat x)) (Nat.log 2 M + 1)
      (measurableSet_comparableLabel_eq stat hstat)
      (fun x hx ↦ comparableLabel_le_of_le (hbound x hx))
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hb
  · simpa [restrictComparableStatisticBucket, Nat.add_assoc] using hmass
  · intro x hx
    apply zeroOrComparable_of_comparableLabel_eq
    exact hconstant x (by simpa [restrictComparableStatisticBucket] using hx)

def restrictComparableCarrierStatisticBucket
    (Y : Shading F) (stat : ι → Space → ℕ)
    (hstat : ∀ i n, MeasurableSet {x | stat i x = n}) (b : ℕ) : Shading F :=
  restrictCarrierStatisticLevel Y
    (fun i x ↦ comparableLabel (stat i x))
    (fun i ↦ measurableSet_comparableLabel_eq (stat i) (hstat i)) b

theorem exists_restrictComparableCarrierStatisticBucket_with_large_mass
    [Fintype ι]
    (Y : Shading F) (stat : ι → Space → ℕ) (M : ℕ)
    (hstat : ∀ i n, MeasurableSet {x | stat i x = n})
    (hbound : ∀ i x, x ∈ Y.carrier i → stat i x ≤ M) :
    ∃ b ∈ Finset.range (Nat.log 2 M + 2),
      Y.shadingMass ≤
        (Nat.log 2 M + 2) •
          (restrictComparableCarrierStatisticBucket Y stat hstat b).shadingMass ∧
      ∀ i x,
        x ∈ (restrictComparableCarrierStatisticBucket Y stat hstat b).carrier i →
          ZeroOrComparable (comparableBase b) (stat i x) := by
  obtain ⟨b, hb, hmass, hconstant⟩ :=
    exists_restrictCarrierStatisticLevel_with_large_mass Y
      (fun i x ↦ comparableLabel (stat i x)) (Nat.log 2 M + 1)
      (fun i ↦ measurableSet_comparableLabel_eq (stat i) (hstat i))
      (fun i x hx ↦ comparableLabel_le_of_le (hbound i x hx))
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hb
  · simpa [restrictComparableCarrierStatisticBucket, Nat.add_assoc] using hmass
  · intro i x hx
    apply zeroOrComparable_of_comparableLabel_eq
    exact hconstant i x
      (by simpa [restrictComparableCarrierStatisticBucket] using hx)

end ComparableMultiplicityBuckets

end

end Submission.Kakeya.ConvexFactoring

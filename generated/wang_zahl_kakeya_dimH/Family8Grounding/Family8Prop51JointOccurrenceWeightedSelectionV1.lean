import Family8Grounding.Family8SelectedOccurrenceAverageRetentionV1
import Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
import Mathlib.Tactic

/-!
# A joint weighted occurrence selection for Proposition 5.1

The density bucket already present in the convex-factoring library is
weighted by `blockMass`.  That is not enough for the use of Proposition 5.1
inside Proposition 6.6(A): the refined family `W'` has to retain the mass of
the *induced outer shading*.

Here a single bucket simultaneously records

* the actual base-two logarithm of the occurrence-fibre cardinality, and
* a finite base-two band for the actual `blockDensity`.

The pigeonhole weight is the literal shaded mass of the occurrence carrier.
Consequently the selected set has all three conclusions needed later: full
shaded-mass retention, dyadic fibre-cardinality uniformity, and two-sided
`blockMass` density bounds.  The loss is the explicit product

`(log_2 (card iota) + 1) * (densityExponentBound + 1)`.

The finite density-range hypotheses are kept explicit.  Without such a range
there is no finite logarithmic pigeonhole principle for arbitrary `ENNReal`
densities (which may include both zero and ∞).
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51JointOccurrenceWeightedSelectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8GreedyOccurrenceOuterDatumV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceAverageRetentionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-! ## The two literal logarithmic labels -/

/-- Half-open base-two band `[2^n base, 2^(n+1) base)` for an `ENNReal`
quantity. -/
def InENNRealDyadicBand (base : ENNReal) (n : Nat) (v : ENNReal) : Prop :=
  (2 : ENNReal) ^ n * base ≤ v ∧
    v < (2 : ENNReal) ^ (n + 1) * base

/-- Every value in a prescribed finite dyadic range belongs to one of its
half-open bands. -/
theorem exists_ennrealDyadicBand_of_bounds
    {base v : ENNReal} {M : Nat}
    (hlower : base ≤ v)
    (hupper : v < (2 : ENNReal) ^ (M + 1) * base) :
    ∃ n, n ≤ M ∧ InENNRealDyadicBand base n v := by
  let p : Nat -> Prop := fun n =>
    v < (2 : ENNReal) ^ (n + 1) * base
  have hp : ∃ n, p n := by
    exact ⟨M, hupper⟩
  let n := Nat.find hp
  have hnM : n ≤ M := Nat.find_min' hp hupper
  have hnUpper : p n := Nat.find_spec hp
  refine ⟨n, hnM, ?_, hnUpper⟩
  by_cases hn0 : n = 0
  · simpa [n, hn0] using hlower
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hjlt : j < n := by omega
    have hnot : ¬ (p j) := Nat.find_min hp (by simpa [n] using hjlt)
    simpa [p, hj] using (le_of_not_gt hnot)

/-- A total label into the `M+1` available density bands.  Values outside the
prescribed range receive the harmless default label zero; the theorem below
uses a range proof to recover the genuine band specification. -/
def ennrealDyadicLabel (base : ENNReal) (M : Nat) (v : ENNReal) :
    Fin (M + 1) :=
  if h : ∃ n, n ≤ M ∧ InENNRealDyadicBand base n v then
    ⟨Nat.find h, Nat.lt_succ_of_le (Nat.find_spec h).1⟩
  else
    ⟨0, Nat.zero_lt_succ M⟩

theorem ennrealDyadicLabel_spec
    {base v : ENNReal} {M : Nat}
    (h : ∃ n, n ≤ M ∧ InENNRealDyadicBand base n v) :
    InENNRealDyadicBand base (ennrealDyadicLabel base M v).1 v := by
  rw [ennrealDyadicLabel, dif_pos h]
  exact (Nat.find_spec h).2

/-- The true logarithmic label of a greedy occurrence's fine-fibre
cardinality. -/
def occurrenceFiberLogCardLabel
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    Fin (Nat.log 2 (Fintype.card iota) + 1) :=
  ⟨Nat.log 2 (blockAt F P k).fiber.card, by
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    exact Finset.card_le_card (Finset.subset_univ _)⟩

/-- The true finite density-band label of a greedy occurrence. -/
def occurrenceDensityDyadicLabel
    (P : GreedyDensityPartition F candidates container active)
    (base : ENNReal) (M : Nat)
    (k : Fin (blocks F P).length) : Fin (M + 1) :=
  ennrealDyadicLabel base M (blockDensity F (blockAt F P k))

/-- The joint label used for the one-shot selection. -/
def occurrenceJointDyadicLabel
    (P : GreedyDensityPartition F candidates container active)
    (base : ENNReal) (M : Nat)
    (k : Fin (blocks F P).length) :
    Fin (Nat.log 2 (Fintype.card iota) + 1) × Fin (M + 1) :=
  (occurrenceFiberLogCardLabel P k,
    occurrenceDensityDyadicLabel P base M k)

/-- The one selected set `S`: a literal fibre of the joint label. -/
def selectedJointOccurrenceBucket
    (P : GreedyDensityPartition F candidates container active)
    (base : ENNReal) (M : Nat)
    (b : Fin (Nat.log 2 (Fintype.card iota) + 1) × Fin (M + 1)) :
    Finset (Fin (blocks F P).length) :=
  dyadicFiber Finset.univ (occurrenceJointDyadicLabel P base M) b

/-- The exact number of available joint labels, hence the exact logarithmic
selection loss. -/
def prop51JointOccurrenceLoss (iota : Type*) [Fintype iota] (M : Nat) : Nat :=
  (Nat.log 2 (Fintype.card iota) + 1) * (M + 1)

/-- The weight used by the selection is outer shaded mass, not `blockMass`. -/
def occurrenceOuterShadedMass
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (k : Fin (blocks F P).length) : ENNReal :=
  volume (((convexFactorization F P).inducedShading Y).carrier (some k))

/-! ## Exact mass identities -/

/-- Summing the actual occurrence weights gives the full induced shaded
mass, including the proof that the inactive `none` carrier contributes zero. -/
theorem fullOccurrenceInducedShading_mass_eq_sum_occurrenceOuterShadedMass
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    (fullOccurrenceInducedShading P Y).shadingMass =
      ∑ k : Fin (blocks F P).length, occurrenceOuterShadedMass P Y k := by
  rw [← greedyOccurrenceOuterShading_shadingMass_eq_induced P Y]
  rfl

/-- The selected occurrence shading is the sum of exactly the same weights
over exactly the chosen joint bucket. -/
theorem selectedOccurrenceOuterShading_mass_eq_sum_occurrenceOuterShadedMass
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceOuterShading P Y S).shadingMass =
      ∑ k ∈ S, occurrenceOuterShadedMass P Y k := by
  simpa [occurrenceOuterShadedMass] using
    selectedOccurrenceOuterShading_mass P Y S

/-! ## The three simultaneous consequences on the same `S` -/

/-- Equality of actual fibre-log labels forces two-uniformity of actual fibre
cardinalities.  Greedy blocks are nonempty, so no zero bucket is needed. -/
theorem occurrenceFiberCard_le_two_mul_of_logLabel_eq
    (P : GreedyDensityPartition F candidates container active)
    (k l : Fin (blocks F P).length)
    (hlabel : occurrenceFiberLogCardLabel P k =
      occurrenceFiberLogCardLabel P l) :
    (((blockAt F P k).fiber.card : Nat) : ENNReal) ≤
      2 * (((blockAt F P l).fiber.card : Nat) : ENNReal) := by
  let nk := (blockAt F P k).fiber.card
  let nl := (blockAt F P l).fiber.card
  have hnk0 : nk ≠ 0 := by
    exact Finset.card_ne_zero.mpr (blockAt F P k).fiber_nonempty
  have hnl0 : nl ≠ 0 := by
    exact Finset.card_ne_zero.mpr (blockAt F P l).fiber_nonempty
  have hlog : Nat.log 2 nk = Nat.log 2 nl := by
    exact congrArg Fin.val hlabel
  have hkUpper : nk < 2 * (2 ^ Nat.log 2 nk) := by
    have h := Nat.lt_pow_succ_log_self Nat.one_lt_two nk
    simpa [pow_succ, Nat.mul_comm] using h
  have hlLower : 2 ^ Nat.log 2 nl ≤ nl :=
    Nat.pow_log_le_self 2 hnl0
  have hnat : nk ≤ 2 * nl := by
    calc
      nk ≤ 2 * (2 ^ Nat.log 2 nk) := Nat.le_of_lt hkUpper
      _ = 2 * (2 ^ Nat.log 2 nl) := by rw [hlog]
      _ ≤ 2 * nl := Nat.mul_le_mul_left 2 hlLower
  exact_mod_cast hnat

/-- The same selected joint bucket is fibre-cardinality dyadic-uniform. -/
theorem selectedJointOccurrenceBucket_fiberCard_dyadicUniform
    (P : GreedyDensityPartition F candidates container active)
    (base : ENNReal) (M : Nat)
    (b : Fin (Nat.log 2 (Fintype.card iota) + 1) × Fin (M + 1))
    (k : Fin (blocks F P).length)
    (hk : k ∈ selectedJointOccurrenceBucket P base M b)
    (l : Fin (blocks F P).length)
    (hl : l ∈ selectedJointOccurrenceBucket P base M b) :
    (((blockAt F P k).fiber.card : Nat) : ENNReal) ≤
      2 * (((blockAt F P l).fiber.card : Nat) : ENNReal) := by
  apply occurrenceFiberCard_le_two_mul_of_logLabel_eq P k l
  have hkLabel :=
    (mem_dyadicFiber Finset.univ
      (occurrenceJointDyadicLabel P base M) b k).1 hk |>.2
  have hlLabel :=
    (mem_dyadicFiber Finset.univ
      (occurrenceJointDyadicLabel P base M) b l).1 hl |>.2
  exact (congrArg Prod.fst hkLabel).trans (congrArg Prod.fst hlLabel).symm

/-- Membership in the joint bucket gives its literal density band. -/
theorem selectedJointOccurrenceBucket_densityBand
    (P : GreedyDensityPartition F candidates container active)
    (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧
        InENNRealDyadicBand base n
          (blockDensity F (blockAt F P k)))
    (b : Fin (Nat.log 2 (Fintype.card iota) + 1) × Fin (M + 1))
    (k : Fin (blocks F P).length)
    (hk : k ∈ selectedJointOccurrenceBucket P base M b) :
    InENNRealDyadicBand base b.2.1
      (blockDensity F (blockAt F P k)) := by
  have hspec := ennrealDyadicLabel_spec (hcovered k)
  have hkLabel :=
    (mem_dyadicFiber Finset.univ
      (occurrenceJointDyadicLabel P base M) b k).1 hk |>.2
  have hdensityLabel : occurrenceDensityDyadicLabel P base M k = b.2 :=
    congrArg Prod.snd hkLabel
  have hdensityVal :
      (ennrealDyadicLabel base M
        (blockDensity F (blockAt F P k))).1 = b.2.1 := by
    simpa [occurrenceDensityDyadicLabel] using congrArg Fin.val hdensityLabel
  rw [hdensityVal] at hspec
  exact hspec

/-- The lower half of the density band is already a literal lower
`blockMass` bound; no division needs to be cleared. -/
theorem selectedJointOccurrenceBucket_blockMass_lower
    (P : GreedyDensityPartition F candidates container active)
    (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧
        InENNRealDyadicBand base n
          (blockDensity F (blockAt F P k)))
    (b : Fin (Nat.log 2 (Fintype.card iota) + 1) × Fin (M + 1))
    (k : Fin (blocks F P).length)
    (hk : k ∈ selectedJointOccurrenceBucket P base M b) :
    ((2 : ENNReal) ^ b.2.1 * base) *
        volume ((blockAt F P k).body : Set Space) ≤
      blockMass F (blockAt F P k) := by
  exact lower_mul_volume_le_blockMass F (blockAt F P k)
    ((2 : ENNReal) ^ b.2.1 * base)
    (selectedJointOccurrenceBucket_densityBand P base M hcovered b k hk).1

/-- Clearing the density quotient gives the upper `blockMass` bound.  The
winning body has finite measure by compactness; its nonzero volume is the
only additional geometric premise. -/
theorem selectedJointOccurrenceBucket_blockMass_upper
    (P : GreedyDensityPartition F candidates container active)
    (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧
        InENNRealDyadicBand base n
          (blockDensity F (blockAt F P k)))
    (hvolume0 : ∀ k : Fin (blocks F P).length,
      volume ((blockAt F P k).body : Set Space) ≠ 0)
    (b : Fin (Nat.log 2 (Fintype.card iota) + 1) × Fin (M + 1))
    (k : Fin (blocks F P).length)
    (hk : k ∈ selectedJointOccurrenceBucket P base M b) :
    blockMass F (blockAt F P k) ≤
      ((2 : ENNReal) ^ (b.2.1 + 1) * base) *
        volume ((blockAt F P k).body : Set Space) := by
  have hdensity : blockDensity F (blockAt F P k) ≤
      (2 : ENNReal) ^ (b.2.1 + 1) * base :=
    (selectedJointOccurrenceBucket_densityBand
      P base M hcovered b k hk).2.le
  exact (ENNReal.div_le_iff_le_mul
    (Or.inl (hvolume0 k))
    (Or.inl (blockAt F P k).body.isCompact.measure_lt_top.ne)).1 hdensity

/-- Weighted selection by the actual outer shaded mass.  This is the part
that the pre-existing block-mass density bucket does not supply. -/
theorem exists_selectedJointOccurrenceBucket_shadedMass_retention
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) :
    ∃ b : Fin (Nat.log 2 (Fintype.card iota) + 1) × Fin (M + 1),
      (fullOccurrenceInducedShading P Y).shadingMass ≤
        (prop51JointOccurrenceLoss iota M : ENNReal) *
          (selectedOccurrenceOuterShading P Y
            (selectedJointOccurrenceBucket P base M b)).shadingMass := by
  obtain ⟨b, hb⟩ := exists_large_ennreal_finiteBucket
    (Finset.univ : Finset (Fin (blocks F P).length))
    (occurrenceJointDyadicLabel P base M)
    (occurrenceOuterShadedMass P Y)
  refine ⟨b, ?_⟩
  rw [fullOccurrenceInducedShading_mass_eq_sum_occurrenceOuterShadedMass,
    selectedOccurrenceOuterShading_mass_eq_sum_occurrenceOuterShadedMass]
  simpa [selectedJointOccurrenceBucket, prop51JointOccurrenceLoss] using hb

/-- **Exact minimal Prop. 5.1 occurrence producer.**  One explicitly
constructed `S` simultaneously has the full outer shaded-mass retention,
selected-fibre dyadic uniformity, and the two `blockMass` density inequalities
needed by the Eq. (45) input bundle.  None of these conclusions is supplied as
a callback or stored in an input structure. -/
theorem exists_prop51SelectedOccurrences
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (hbase0 : base ≠ 0) (hbaseTop : base ≠ ∞)
    (hdensityLower : ∀ k : Fin (blocks F P).length,
      base ≤ blockDensity F (blockAt F P k))
    (hdensityUpper : ∀ k : Fin (blocks F P).length,
      blockDensity F (blockAt F P k) <
        (2 : ENNReal) ^ (M + 1) * base)
    (hvolume0 : ∀ k : Fin (blocks F P).length,
      volume ((blockAt F P k).body : Set Space) ≠ 0) :
    ∃ b : Fin (Nat.log 2 (Fintype.card iota) + 1) × Fin (M + 1),
      let S := selectedJointOccurrenceBucket P base M b
      let lower := (2 : ENNReal) ^ b.2.1 * base
      let upper := (2 : ENNReal) ^ (b.2.1 + 1) * base
      (fullOccurrenceInducedShading P Y).shadingMass ≤
          (prop51JointOccurrenceLoss iota M : ENNReal) *
            (selectedOccurrenceOuterShading P Y S).shadingMass ∧
        (∀ k ∈ S, ∀ l ∈ S,
          (((blockAt F P k).fiber.card : Nat) : ENNReal) ≤
            2 * (((blockAt F P l).fiber.card : Nat) : ENNReal)) ∧
        lower ≠ 0 ∧
        lower ≠ ∞ ∧
        (∀ k ∈ S,
          lower * volume ((blockAt F P k).body : Set Space) ≤
            blockMass F (blockAt F P k)) ∧
        (∀ k ∈ S,
          blockMass F (blockAt F P k) ≤
            upper * volume ((blockAt F P k).body : Set Space)) := by
  have hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧
        InENNRealDyadicBand base n
          (blockDensity F (blockAt F P k)) := by
    intro k
    exact exists_ennrealDyadicBand_of_bounds
      (hdensityLower k) (hdensityUpper k)
  obtain ⟨b, hretention⟩ :=
    exists_selectedJointOccurrenceBucket_shadedMass_retention P Y base M
  refine ⟨b, hretention, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk l hl
    exact selectedJointOccurrenceBucket_fiberCard_dyadicUniform
      P base M b k hk l hl
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hbase0
  · exact ENNReal.mul_ne_top (by simp) hbaseTop
  · intro k hk
    exact selectedJointOccurrenceBucket_blockMass_lower
      P base M hcovered b k hk
  · intro k hk
    exact selectedJointOccurrenceBucket_blockMass_upper
      P base M hcovered hvolume0 b k hk

#print axioms exists_ennrealDyadicBand_of_bounds
#print axioms ennrealDyadicLabel_spec
#print axioms fullOccurrenceInducedShading_mass_eq_sum_occurrenceOuterShadedMass
#print axioms selectedOccurrenceOuterShading_mass_eq_sum_occurrenceOuterShadedMass
#print axioms occurrenceFiberCard_le_two_mul_of_logLabel_eq
#print axioms selectedJointOccurrenceBucket_fiberCard_dyadicUniform
#print axioms selectedJointOccurrenceBucket_densityBand
#print axioms selectedJointOccurrenceBucket_blockMass_lower
#print axioms selectedJointOccurrenceBucket_blockMass_upper
#print axioms exists_selectedJointOccurrenceBucket_shadedMass_retention
#print axioms exists_prop51SelectedOccurrences

end

end Family8Prop51JointOccurrenceWeightedSelectionV1

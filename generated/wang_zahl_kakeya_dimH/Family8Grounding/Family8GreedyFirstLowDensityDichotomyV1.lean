import Family8Grounding.Family8SharpKatzTaoOrGreedyHighConcentrationV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyFirstLowDensityDichotomyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.GreedyLateTailRestart
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumMassBridgeV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

/-!
# First-low greedy density dichotomy with actual mass transport

The ordered full-convex greedy densities are nonincreasing.  At the first
occurrence whose density is at most `A`, the remaining active fine family is
already Katz--Tao with coefficient `A`.  Splitting the source shading mass
between this literal tail and its literal complement shows that one branch
retains at least half of the source mass.  Thus the low branch is an actual
sharp-Katz--Tao restricted datum, while the high branch is an actual restricted
prefix carrying factor-two mass and average-multiplicity transport.  Every
occurrence before the cut is certified to have density strictly larger than
`A`.

No source Katz--Tao hypothesis, target RHS, or synonymous scalar callback is
assumed.
-/

/-- Occurrences whose exact winning density is at most the target coefficient. -/
def lowDensityOccurrences
    {index : Type} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (base : Finset index)
    {active : Finset index}
    (P : GreedyDensityPartition F (hullCandidates base)
      (hullContainer F) active) (A : ENNReal) :
    Finset (Fin (blocks F P).length) :=
  Finset.univ.filter fun k => blockDensity F (blockAt F P k) <= A

@[simp] theorem mem_lowDensityOccurrences
    {index : Type} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (base : Finset index)
    {active : Finset index}
    (P : GreedyDensityPartition F (hullCandidates base)
      (hullContainer F) active) (A : ENNReal)
    (k : Fin (blocks F P).length) :
    k ∈ lowDensityOccurrences F base P A ↔
      blockDensity F (blockAt F P k) <= A := by
  simp [lowDensityOccurrences]

/-- Once an actual restart winner has density at most `A`, its entire active
fine tail is Katz--Tao at `A`. -/
theorem activeAt_isKatzTaoOn_of_blockDensity_le
    {index : Type} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (base : Finset index)
    {active : Finset index}
    (P : GreedyDensityPartition F (hullCandidates base)
      (hullContainer F) active) (hactive : active ⊆ base)
    (k : Fin (blocks F P).length) (A : ENNReal)
    (hlow : blockDensity F (blockAt F P k) <= A) :
    IsKatzTaoOn A F (activeAt F P k) := by
  intro K
  rw [← massInside_eq_containedMassOn]
  calc
    massInside F (activeAt F P k) K <=
        initialDensity F base (partitionAt F P k) *
          volume (K : Set Space) :=
      activeMassInside_le_initialDensity F base (partitionAt F P k)
        (activeAt_subset F P k hactive) K
    _ = blockDensity F (blockAt F P k) *
          volume (K : Set Space) := by
      rw [initialDensity_partitionAt_eq_blockDensity F base P k]
    _ <= A * volume (K : Set Space) :=
      mul_le_mul' hlow le_rfl

/-- Exact source shading-mass split at a genuine greedy restart. -/
theorem shadingMass_eq_restrict_activeAt_add_restrict_prefix
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (k : Fin (blocks D.family.bodyFamily P).length) :
    D.shading.shadingMass =
      (restrictActualTubeDatum D
        (activeAt D.family.bodyFamily P k)).shading.shadingMass +
      (restrictActualTubeDatum D
        (Finset.univ \ activeAt D.family.bodyFamily P k)).shading.shadingMass := by
  classical
  rw [restrictActualTubeDatum_shadingMass,
    restrictActualTubeDatum_shadingMass]
  unfold Shading.shadingMass
  let tail := activeAt D.family.bodyFamily P k
  have hsub : tail ⊆ (Finset.univ : Finset index) := fun _ _ =>
    Finset.mem_univ _
  calc
    (∑ i : index, volume (D.shading.carrier i)) =
        ∑ i ∈ tail ∪ (Finset.univ \ tail),
          volume (D.shading.carrier i) := by
      rw [Finset.union_sdiff_of_subset hsub]
    _ = (∑ i ∈ tail, volume (D.shading.carrier i)) +
          ∑ i ∈ Finset.univ \ tail, volume (D.shading.carrier i) := by
      exact Finset.sum_union Finset.disjoint_sdiff

/-- One of the literal first-low tail and its literal high prefix retains at
least half of the source shading mass. -/
theorem source_shadingMass_le_two_mul_tail_or_prefix
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (k : Fin (blocks D.family.bodyFamily P).length) :
    D.shading.shadingMass <= 2 *
        (restrictActualTubeDatum D
          (activeAt D.family.bodyFamily P k)).shading.shadingMass ∨
      D.shading.shadingMass <= 2 *
        (restrictActualTubeDatum D
          (Finset.univ \ activeAt D.family.bodyFamily P k)).shading.shadingMass := by
  let tailMass := (restrictActualTubeDatum D
    (activeAt D.family.bodyFamily P k)).shading.shadingMass
  let prefixMass := (restrictActualTubeDatum D
    (Finset.univ \ activeAt D.family.bodyFamily P k)).shading.shadingMass
  have hsplit : D.shading.shadingMass = tailMass + prefixMass := by
    simpa only [tailMass, prefixMass] using
      shadingMass_eq_restrict_activeAt_add_restrict_prefix D P k
  by_cases htailPrefix : tailMass <= prefixMass
  · right
    calc
      D.shading.shadingMass = tailMass + prefixMass := hsplit
      _ <= prefixMass + prefixMass := add_le_add htailPrefix le_rfl
      _ = 2 * prefixMass := by simp [two_mul]
  · left
    have hprefixTail : prefixMass <= tailMass :=
      le_of_lt (lt_of_not_ge htailPrefix)
    calc
      D.shading.shadingMass = tailMass + prefixMass := hsplit
      _ <= tailMass + tailMass := add_le_add le_rfl hprefixTail
      _ = 2 * tailMass := by simp [two_mul]

/-- Callback-free first-low threshold dichotomy.  The low result is an actual
restricted datum with sharp Katz--Tao coefficient `A`; the high result is an
actual factor-two-mass restriction together with either all-high occurrences
or an explicit first-low cut whose entire earlier prefix is high. -/
theorem exists_factorTwo_lowKatzTaoRestriction_or_highConcentrationPrefix
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible) (A : ENNReal) :
    (∃ selected : Finset index,
        D.shading.shadingMass <= 2 *
          (restrictActualTubeDatum D selected).shading.shadingMass ∧
        D.shading.averageMultiplicity <= 2 *
          (restrictActualTubeDatum D selected).shading.averageMultiplicity ∧
        (restrictActualTubeDatum D selected).IsAdmissible ∧
        IsKatzTao A
          (restrictActualTubeDatum D selected).family.bodyFamily) ∨
      ∃ P : GreedyDensityPartition D.family.bodyFamily
          (hullCandidates (Finset.univ : Finset index))
          (hullContainer D.family.bodyFamily) Finset.univ,
        ∃ selected : Finset index,
          D.shading.shadingMass <= 2 *
            (restrictActualTubeDatum D selected).shading.shadingMass ∧
          D.shading.averageMultiplicity <= 2 *
            (restrictActualTubeDatum D selected).shading.averageMultiplicity ∧
          (restrictActualTubeDatum D selected).IsAdmissible ∧
          ((selected = Finset.univ ∧
              ∀ q : Fin (blocks D.family.bodyFamily P).length,
                A < blockDensity D.family.bodyFamily
                  (blockAt D.family.bodyFamily P q)) ∨
            ∃ k0 : Fin (blocks D.family.bodyFamily P).length,
              selected = Finset.univ \
                activeAt D.family.bodyFamily P k0 ∧
              blockDensity D.family.bodyFamily
                (blockAt D.family.bodyFamily P k0) <= A ∧
              ∀ q : Fin (blocks D.family.bodyFamily P).length,
                q < k0 → A < blockDensity D.family.bodyFamily
                  (blockAt D.family.bodyFamily P q)) := by
  classical
  obtain ⟨P, _hcover, _hlength, _hcross⟩ :=
    exists_fullConvexGreedyDensityPartition D.family.bodyFamily Finset.univ
  let low := lowDensityOccurrences D.family.bodyFamily Finset.univ P A
  by_cases hlow : low.Nonempty
  · let k0 : Fin (blocks D.family.bodyFamily P).length := low.min' hlow
    have hk0mem : k0 ∈ low := Finset.min'_mem low hlow
    have hk0low : blockDensity D.family.bodyFamily
        (blockAt D.family.bodyFamily P k0) <= A := by
      exact (mem_lowDensityOccurrences
        D.family.bodyFamily Finset.univ P A k0).mp hk0mem
    have hprior : ∀ q : Fin (blocks D.family.bodyFamily P).length,
        q < k0 → A < blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) := by
      intro q hq
      by_contra hnot
      have hqLow : blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) <= A :=
        le_of_not_gt hnot
      have hqmem : q ∈ low :=
        (mem_lowDensityOccurrences
          D.family.bodyFamily Finset.univ P A q).mpr hqLow
      exact (not_le_of_gt hq) (Finset.min'_le low q hqmem)
    rcases source_shadingMass_le_two_mul_tail_or_prefix D P k0 with
      htail | hprefix
    · left
      refine ⟨activeAt D.family.bodyFamily P k0, htail, ?_, ?_, ?_⟩
      · exact source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
          D (activeAt D.family.bodyFamily P k0) 2 htail
      · exact
          Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
            hD (activeAt D.family.bodyFamily P k0)
      · apply isKatzTao_restrictActualTubeDatum_of_isKatzTaoOn
        exact activeAt_isKatzTaoOn_of_blockDensity_le
          D.family.bodyFamily Finset.univ P (fun _ hi => hi) k0 A hk0low
    · right
      refine ⟨P, Finset.univ \ activeAt D.family.bodyFamily P k0,
        hprefix, ?_, ?_, Or.inr ?_⟩
      · exact source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
          D (Finset.univ \ activeAt D.family.bodyFamily P k0) 2 hprefix
      · exact
          Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
            hD (Finset.univ \ activeAt D.family.bodyFamily P k0)
      · exact ⟨k0, rfl, hk0low, hprior⟩
  · right
    have hallHigh : ∀ q : Fin (blocks D.family.bodyFamily P).length,
        A < blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) := by
      intro q
      have hnotLow : ¬ blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) <= A := by
        intro hqLow
        exact hlow ⟨q, (mem_lowDensityOccurrences
          D.family.bodyFamily Finset.univ P A q).mpr hqLow⟩
      exact lt_of_not_ge hnotLow
    have hmassEq : (restrictActualTubeDatum D
        (Finset.univ : Finset index)).shading.shadingMass =
        D.shading.shadingMass := by
      rw [restrictActualTubeDatum_shadingMass]
      unfold Shading.shadingMass
      simp
    have hmass : D.shading.shadingMass <= 2 *
        (restrictActualTubeDatum D
          (Finset.univ : Finset index)).shading.shadingMass := by
      rw [hmassEq]
      calc
        D.shading.shadingMass = 1 * D.shading.shadingMass := by simp
        _ <= 2 * D.shading.shadingMass := by
          exact mul_le_mul' (by norm_num : (1 : ENNReal) <= 2) le_rfl
    exact ⟨P, Finset.univ, hmass,
      source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
        D Finset.univ 2 hmass,
      Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
        hD Finset.univ,
      Or.inl ⟨rfl, hallHigh⟩⟩

#print axioms lowDensityOccurrences
#print axioms mem_lowDensityOccurrences
#print axioms activeAt_isKatzTaoOn_of_blockDensity_le
#print axioms shadingMass_eq_restrict_activeAt_add_restrict_prefix
#print axioms source_shadingMass_le_two_mul_tail_or_prefix
#print axioms exists_factorTwo_lowKatzTaoRestriction_or_highConcentrationPrefix

end
end Family8GreedyFirstLowDensityDichotomyV1

import Family8Grounding.Family8Prop51JointOccurrenceWeightedSelectionV1
import Family8Grounding.Family8PaperEq45SelectedOccurrenceBundleV2
import Mathlib.Tactic

/-!
# The canonical Proposition 5.1 occurrence selection and its source Frostman theorem

The joint weighted pigeonhole theorem gives an existential label.  This file
chooses that label once and for all, so the shaded-mass retention, fibre-card
uniformity, and block-density bounds below all concern the same literal set
`prop51SelectedOccurrences`.

Restricting a normalized `IsFrostmanOn` statement to an arbitrary subset is
not valid: the normalizing ambient mass can decrease.  The exact missing
scalar is recorded here as an inequality between the full and selected
ambient body masses.  From that inequality and a global source
`IsFrostmanOn`, the selected source certificate is proved; it is not accepted
as a conclusion-valued callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51SelectedOccurrenceSourceFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceAverageRetentionV1
open Family8Prop51JointOccurrenceWeightedSelectionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-! ## One canonical joint bucket -/

/-- The label supplied by weighted pigeonholing of the actual induced outer
shaded mass. -/
def prop51SelectedOccurrenceLabel
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) :
    Fin (Nat.log 2 (Fintype.card iota) + 1) × Fin (M + 1) :=
  Classical.choose
    (exists_selectedJointOccurrenceBucket_shadedMass_retention P Y base M)

/-- The literal selected occurrence set used by every theorem in this file. -/
def prop51SelectedOccurrences
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) :
    Finset (Fin (blocks F P).length) :=
  selectedJointOccurrenceBucket P base M
    (prop51SelectedOccurrenceLabel P Y base M)

/-- The lower endpoint of the selected block-density band. -/
def prop51SelectedLowerDensity
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) : ENNReal :=
  (2 : ENNReal) ^ (prop51SelectedOccurrenceLabel P Y base M).2.1 * base

/-- The upper endpoint of the selected block-density band. -/
def prop51SelectedUpperDensity
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) : ENNReal :=
  (2 : ENNReal) ^ ((prop51SelectedOccurrenceLabel P Y base M).2.1 + 1) * base

/-- The canonical selected set retains the actual full induced outer shaded
mass with the explicit joint logarithmic loss. -/
theorem prop51SelectedOccurrences_shadedMass_retention
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) :
    (fullOccurrenceInducedShading P Y).shadingMass ≤
      (prop51JointOccurrenceLoss iota M : ENNReal) *
        (selectedOccurrenceOuterShading P Y
          (prop51SelectedOccurrences P Y base M)).shadingMass := by
  exact Classical.choose_spec
    (exists_selectedJointOccurrenceBucket_shadedMass_retention P Y base M)

/-- The same canonical set has dyadically uniform actual fibre cards. -/
theorem prop51SelectedOccurrences_fiberCard_dyadicUniform
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (k : Fin (blocks F P).length)
    (hk : k ∈ prop51SelectedOccurrences P Y base M)
    (l : Fin (blocks F P).length)
    (hl : l ∈ prop51SelectedOccurrences P Y base M) :
    (((blockAt F P k).fiber.card : Nat) : ENNReal) ≤
      2 * (((blockAt F P l).fiber.card : Nat) : ENNReal) := by
  exact selectedJointOccurrenceBucket_fiberCard_dyadicUniform
    P base M (prop51SelectedOccurrenceLabel P Y base M) k hk l hl

theorem prop51SelectedLowerDensity_ne_zero
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (M : Nat) {base : ENNReal} (hbase : base ≠ 0) :
    prop51SelectedLowerDensity P Y base M ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hbase

theorem prop51SelectedLowerDensity_ne_top
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (M : Nat) {base : ENNReal} (hbase : base ≠ ∞) :
    prop51SelectedLowerDensity P Y base M ≠ ∞ := by
  exact ENNReal.mul_ne_top (by simp) hbase

/-- The lower block-mass bound on the same canonical selection. -/
theorem prop51SelectedOccurrences_blockMass_lower
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧ InENNRealDyadicBand base n
        (blockDensity F (blockAt F P k)))
    (k : Fin (blocks F P).length)
    (hk : k ∈ prop51SelectedOccurrences P Y base M) :
    prop51SelectedLowerDensity P Y base M *
        volume ((blockAt F P k).body : Set Space) ≤
      blockMass F (blockAt F P k) := by
  exact selectedJointOccurrenceBucket_blockMass_lower P base M hcovered
    (prop51SelectedOccurrenceLabel P Y base M) k hk

/-- The upper block-mass bound on the same canonical selection. -/
theorem prop51SelectedOccurrences_blockMass_upper
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧ InENNRealDyadicBand base n
        (blockDensity F (blockAt F P k)))
    (hvolume0 : ∀ k : Fin (blocks F P).length,
      volume ((blockAt F P k).body : Set Space) ≠ 0)
    (k : Fin (blocks F P).length)
    (hk : k ∈ prop51SelectedOccurrences P Y base M) :
    blockMass F (blockAt F P k) ≤
      prop51SelectedUpperDensity P Y base M *
        volume ((blockAt F P k).body : Set Space) := by
  exact selectedJointOccurrenceBucket_blockMass_upper P base M hcovered
    hvolume0 (prop51SelectedOccurrenceLabel P Y base M) k hk

/-! ## Exact restriction of source Frostman non-concentration -/

/-- The fine indices belonging to any selected occurrence set are genuinely
a subset of the original greedy active set. -/
theorem selectedOccurrenceFineIndices_subset_active
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) :
    selectedOccurrenceFineIndices P S ⊆ active := by
  intro i hi
  obtain ⟨k, _hk, hik⟩ := Finset.mem_biUnion.mp hi
  exact blockAt_fiber_subset_active F P k hik

omit [DecidableEq iota] in
/-- Restrict a normalized source Frostman theorem after paying exactly the
loss of ambient contained body mass.  This is the minimal scalar obstruction
to arbitrary subset monotonicity. -/
theorem isFrostmanOn_subset_of_ambientMass_retention
    {s t : Finset iota} {C L : ENNReal} {K : ConvexBody Space}
    (hst : s ⊆ t) (hfull : IsFrostmanOn C F t K)
    (hretained : containedMassOn F t K ≤ L * containedMassOn F s K) :
    IsFrostmanOn (C * L) F s K := by
  refine ⟨?_, ?_⟩
  · intro i hi
    exact hfull.1 i (hst hi)
  · intro K' hK'
    calc
      containedMassOn F s K' * volume (K : Set Space) ≤
          containedMassOn F t K' * volume (K : Set Space) := by
        gcongr
        exact containedMassOn_mono hst K'
      _ ≤ C * containedMassOn F t K * volume (K' : Set Space) :=
        hfull.2 K' hK'
      _ ≤ C * (L * containedMassOn F s K) *
          volume (K' : Set Space) := by
        gcongr
      _ = (C * L) * containedMassOn F s K *
          volume (K' : Set Space) := by
        ac_rfl

/-- Global source non-concentration plus the one unavoidable ambient-mass
retention inequality produces the source Frostman field on the canonical
Proposition 5.1 selection. -/
theorem prop51SelectedOccurrences_source_fine_frostman
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) {C L : ENNReal}
    (hglobal : IsFrostmanOn C F active K)
    (hbodyRetained : containedMassOn F active K ≤
      L * containedMassOn F
        (selectedOccurrenceFineIndices P
          (prop51SelectedOccurrences P Y base M)) K) :
    IsFrostmanOn (C * L) F
      (selectedOccurrenceFineIndices P
        (prop51SelectedOccurrences P Y base M)) K := by
  exact isFrostmanOn_subset_of_ambientMass_retention
    (selectedOccurrenceFineIndices_subset_active P
      (prop51SelectedOccurrences P Y base M)) hglobal hbodyRetained

#print axioms prop51SelectedOccurrences_shadedMass_retention
#print axioms prop51SelectedOccurrences_fiberCard_dyadicUniform
#print axioms prop51SelectedOccurrences_blockMass_lower
#print axioms prop51SelectedOccurrences_blockMass_upper
#print axioms selectedOccurrenceFineIndices_subset_active
#print axioms isFrostmanOn_subset_of_ambientMass_retention
#print axioms prop51SelectedOccurrences_source_fine_frostman

end

end Family8Prop51SelectedOccurrenceSourceFrostmanV1

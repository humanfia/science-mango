import Family8Grounding.Family8FrostmanInheritanceToActiveCoarseV3
import Family8Grounding.Family8GreedyOccurrenceOuterDatumV1
import Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
import Mathlib.Tactic

/-!
# Density-selected greedy occurrences and Frostman inheritance

The full greedy occurrence family is not the paper's refined family `W'`.
This file keeps an arbitrary literal set `S` of occurrence positions, removes
the inactive `Option.none` marker, and constructs the corresponding selected
fine factorization.  Comparable `blockMass / volume` on `S` then feeds the
SAFE Remark 3.3(A) connector and produces an actual `IsFrostmanIn`
certificate on exactly that selected outer family.

The selected count is definitionally tied to the index subtype and proved to
equal `S.card`.  Fibre-cardinality uniformity is deliberately not used to
derive the Frostman certificate: it is a separate paper input unless body
volumes have also been made comparable.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceDensityFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8FrostmanInheritanceToActiveCoarseV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- The genuine coarse indices belonging to selected occurrence positions.
The inactive `none` marker is absent by construction. -/
def selectedOccurrenceIndices
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) :
    Finset (Option (Fin (blocks F P).length)) :=
  S.image some

@[simp] theorem mem_selectedOccurrenceIndices
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length))
    (q : Option (Fin (blocks F P).length)) :
    q ∈ selectedOccurrenceIndices P S ↔
      ∃ k ∈ S, some k = q := by
  simp [selectedOccurrenceIndices]

/-- The selected active fine indices are exactly the union of the chosen
literal occurrence fibres. -/
def selectedOccurrenceFineIndices
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) : Finset iota :=
  S.biUnion fun k => (blockAt F P k).fiber

/-- Restrict a geometric factorization to the fibres over a specified coarse
set.  No geometric premise is added: containment is inherited from `P`. -/
def selectedConvexFactorization
    {j l : Type*} [Fintype j] [DecidableEq j] [DecidableEq l]
    {G : ConvexFamily j} {W : ConvexFamily l}
    (P : ConvexFactorization G W) (selected : Finset l) :
    ConvexFactorization G W where
  index := selectedIndexFactorization P.index.fine P.index.parent selected
  contained := by
    intro i hi
    exact P.contained i (Finset.mem_filter.mp hi).1

/-- The exact selected occurrence factorization used for the refined outer
family. -/
def selectedOccurrenceFactorization
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) :
    ConvexFactorization F (coarseFamily F P) :=
  selectedConvexFactorization (convexFactorization F P)
    (selectedOccurrenceIndices P S)

/-- Its active coarse set is the literal image of `S`, with no inactive marker. -/
@[simp] theorem selectedOccurrenceFactorization_coarse
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceFactorization P S).index.coarse =
      selectedOccurrenceIndices P S :=
  rfl

/-- Its active fine set is exactly the union of the selected greedy blocks. -/
theorem selectedOccurrenceFactorization_fine
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceFactorization P S).index.fine =
      selectedOccurrenceFineIndices P S := by
  classical
  ext i
  unfold selectedOccurrenceFactorization selectedConvexFactorization
  simp only [selectedIndexFactorization_fine]
  unfold selectedOccurrenceFineIndices selectedFineIndices
    selectedOccurrenceIndices
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hi, hparent⟩
    obtain ⟨k, hk, hkparent⟩ := Finset.mem_image.mp hparent
    exact Finset.mem_biUnion.mpr
      ⟨k, hk, (mem_blockAt_iff_parent_eq F P hi k).2 hkparent.symm⟩
  · intro hi
    obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hi
    have hactive : i ∈ active := blockAt_fiber_subset_active F P k hik
    have hparent : parent F P i = some k :=
      (mem_blockAt_iff_parent_eq F P hactive k).1 hik
    refine ⟨hactive, Finset.mem_image.mpr ⟨k, hk, ?_⟩⟩
    exact hparent.symm

/-- Selection does not change the fibre over a retained occurrence. -/
theorem selectedOccurrenceFactorization_fiber
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length))
    (k : Fin (blocks F P).length) (hk : k ∈ S) :
    (selectedOccurrenceFactorization P S).index.fiber (some k) =
      (blockAt F P k).fiber := by
  classical
  change
    (selectedIndexFactorization active (parent F P)
      (S.image some)).fiber (some k) = _
  rw [selected_fiber_eq_raw_fiber active (parent F P) (S.image some)]
  · change (indexFactorization F P).fiber (some k) = _
    exact indexFactorization_fiber_eq_blockAt F P k
  · exact Finset.mem_image.mpr ⟨k, hk, rfl⟩

/-- Hence the selected-factorization fibre mass is the literal `blockMass`
used by occurrence density bucketing. -/
theorem selectedOccurrenceFactorization_fiberBodyMass
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length))
    (k : Fin (blocks F P).length) (hk : k ∈ S) :
    fiberBodyMass (selectedOccurrenceFactorization P S) (some k) =
      blockMass F (blockAt F P k) := by
  unfold fiberBodyMass blockMass
  rw [selectedOccurrenceFactorization_fiber P S k hk]

/-- The actual selected outer family, indexed by the attached finite subtype
of genuine occurrence labels. -/
abbrev selectedOccurrenceOuterFamily
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) :
    ConvexFamily {q // q ∈ selectedOccurrenceIndices P S} :=
  selectedCoarseFamily (coarseFamily F P) (selectedOccurrenceIndices P S)

/-- Embed a retained occurrence position into the actual selected outer
index type. -/
def selectedOccurrenceIndexOf
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length))
    (k : Fin (blocks F P).length) (hk : k ∈ S) :
    {q // q ∈ selectedOccurrenceIndices P S} :=
  ⟨some k, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩

/-- A selected outer member is exactly its greedy winning body. -/
@[simp] theorem selectedOccurrenceOuterFamily_indexOf
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length))
    (k : Fin (blocks F P).length) (hk : k ∈ S) :
    selectedOccurrenceOuterFamily P S (selectedOccurrenceIndexOf P S k hk) =
      (blockAt F P k).body :=
  rfl

/-- Restrict the original induced shading to exactly the selected occurrence
subtype. -/
def selectedOccurrenceOuterShading
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length)) :
    Shading (selectedOccurrenceOuterFamily P S) :=
  selectedCoarseShading ((convexFactorization F P).inducedShading Y)
    (selectedOccurrenceIndices P S)

/-- Its carrier is literally the original induced carrier at `some k`. -/
@[simp] theorem selectedOccurrenceOuterShading_carrier_indexOf
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length))
    (k : Fin (blocks F P).length) (hk : k ∈ S) :
    (selectedOccurrenceOuterShading P Y S).carrier
        (selectedOccurrenceIndexOf P S k hk) =
      ((convexFactorization F P).inducedShading Y).carrier (some k) :=
  rfl

/-- The selected shading mass is the exact sum of the corresponding original
induced carriers. -/
theorem selectedOccurrenceOuterShading_mass
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceOuterShading P Y S).shadingMass =
      ∑ k ∈ S,
        volume (((convexFactorization F P).inducedShading Y).carrier (some k)) := by
  unfold selectedOccurrenceOuterShading
  rw [selectedCoarseShading_mass]
  unfold selectedOccurrenceIndices
  rw [Finset.sum_image]
  intro k _ l _ hkl
  exact Option.some.inj hkl

/-- The honest selected outer count is the cardinality of its actual index
type, rather than an independent endpoint parameter. -/
def selectedOccurrenceOuterCount
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) : Nat :=
  Fintype.card {q // q ∈ selectedOccurrenceIndices P S}

/-- The honest selected outer count is exactly `S.card`. -/
@[simp] theorem selectedOccurrenceOuterCount_eq_card
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) :
    selectedOccurrenceOuterCount P S = S.card := by
  classical
  unfold selectedOccurrenceOuterCount selectedOccurrenceIndices
  rw [Fintype.card_coe]
  exact Finset.card_image_of_injective S (fun _ _ h => Option.some.inj h)

/-- Explicit two-sided block-mass comparability on the selected occurrences
produces a genuine Frostman certificate on exactly the selected outer family.
This is the paper's Remark 3.3(A) connector at occurrence level. -/
theorem selectedOccurrenceOuterFamily_isFrostmanIn_of_comparable_blockMass
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) (K : ConvexBody Space)
    {C lower upper : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfine : IsFrostmanOn C F (selectedOccurrenceFineIndices P S) K)
    (hcontained : ∀ k ∈ S,
      ((blockAt F P k).body : Set Space) ⊆ (K : Set Space))
    (hlower : ∀ k ∈ S,
      lower * volume ((blockAt F P k).body : Set Space) ≤
        blockMass F (blockAt F P k))
    (hupper : ∀ k ∈ S,
      blockMass F (blockAt F P k) ≤
        upper * volume ((blockAt F P k).body : Set Space)) :
    IsFrostmanIn (C * upper * lower⁻¹)
      (selectedOccurrenceOuterFamily P S) K := by
  have hfine' : IsFrostmanOn C F
      (selectedOccurrenceFactorization P S).index.fine K := by
    rw [selectedOccurrenceFactorization_fine P S]
    exact hfine
  have hactive : IsFrostmanOn (C * upper * lower⁻¹)
      (coarseFamily F P) (selectedOccurrenceIndices P S) K := by
    apply activeCoarse_isFrostmanOn_of_comparable_fiberDensity
      (selectedOccurrenceFactorization P S) K hlower0 hlowerTop hfine'
    · intro q hq
      obtain ⟨k, hk, rfl⟩ :=
        (mem_selectedOccurrenceIndices P S q).1 hq
      exact hcontained k hk
    · intro q hq
      obtain ⟨k, hk, rfl⟩ :=
        (mem_selectedOccurrenceIndices P S q).1 hq
      change lower * volume ((blockAt F P k).body : Set Space) ≤ _
      rw [selectedOccurrenceFactorization_fiberBodyMass P S k hk]
      exact hlower k hk
    · intro q hq
      obtain ⟨k, hk, rfl⟩ :=
        (mem_selectedOccurrenceIndices P S q).1 hq
      change _ ≤ upper * volume ((blockAt F P k).body : Set Space)
      rw [selectedOccurrenceFactorization_fiberBodyMass P S k hk]
      exact hupper k hk
  exact isFrostmanIn_selectedCoarseFamily_of_isFrostmanOn hactive

/-- A literal occurrence-density bucket supplies the comparable block-mass
bounds once its label has a lower and upper density band.  The nonzero body
volume premise is used only to clear the upper density quotient; in the plank
application it follows from nondegenerate side lengths. -/
theorem occurrenceDensityBucket_outerFamily_isFrostmanIn_of_densityBand
    (F : ConvexFamily iota) (base : Finset iota) {active : Finset iota}
    (P : GreedyDensityPartition F (hullCandidates base)
      (hullContainer F) active)
    {beta : Type*} [DecidableEq beta]
    (label : ENNReal -> beta) (bucket : beta)
    (K : ConvexBody Space) {C lower upper : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfine : IsFrostmanOn C F
      (selectedOccurrenceFineIndices P
        (occurrenceDensityBucket F base P label bucket)) K)
    (hcontained : ∀ k ∈ occurrenceDensityBucket F base P label bucket,
      ((blockAt F P k).body : Set Space) ⊆ (K : Set Space))
    (hvolume0 : ∀ k ∈ occurrenceDensityBucket F base P label bucket,
      volume ((blockAt F P k).body : Set Space) ≠ 0)
    (hlowerBand : ∀ rho, label rho = bucket -> lower ≤ rho)
    (hupperBand : ∀ rho, label rho = bucket -> rho ≤ upper) :
    IsFrostmanIn (C * upper * lower⁻¹)
      (selectedOccurrenceOuterFamily P
        (occurrenceDensityBucket F base P label bucket)) K := by
  apply selectedOccurrenceOuterFamily_isFrostmanIn_of_comparable_blockMass
    P (occurrenceDensityBucket F base P label bucket) K
      hlower0 hlowerTop hfine hcontained
  · intro k hk
    exact lower_mul_volume_le_blockMass F (blockAt F P k) lower
      (hlowerBand _
        ((mem_occurrenceDensityBucket F base P label bucket k).1 hk))
  · intro k hk
    have hdensity : blockDensity F (blockAt F P k) ≤ upper :=
      hupperBand _
        ((mem_occurrenceDensityBucket F base P label bucket k).1 hk)
    exact (ENNReal.div_le_iff_le_mul
      (Or.inl (hvolume0 k hk))
      (Or.inl (blockAt F P k).body.isCompact.measure_lt_top.ne)).1 hdensity

#print axioms selectedOccurrenceFactorization_fine
#print axioms selectedOccurrenceFactorization_fiberBodyMass
#print axioms selectedOccurrenceOuterShading_mass
#print axioms selectedOccurrenceOuterCount_eq_card
#print axioms selectedOccurrenceOuterFamily_isFrostmanIn_of_comparable_blockMass
#print axioms occurrenceDensityBucket_outerFamily_isFrostmanIn_of_densityBand

end

end Family8SelectedOccurrenceDensityFrostmanV1

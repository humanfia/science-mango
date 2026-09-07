import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV11
import Family8Grounding.Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import Mathlib.Tactic

/-!
# Local Katz--Tao control on actual-parent occurrence fibres

Suppose every retained greedy occurrence has density at least one.  Then the
volume of its winning hull is at most the mass of its fine block.  Parent
purity puts that whole fine block in the literal sticky source-parent fibre.
After summing disjoint greedy blocks, every actual-parent fibre of occurrence
hulls inherits the Katz--Tao coefficient of the corresponding source-parent
fibre with no reciprocal-density or cardinality loss.

The final specialization uses the exact maximum of the genuine sticky
source-parent fibre concentrations.  Its finite-cardinality bound is used
only to justify `ENNReal.toNNReal`; the displayed coefficient remains the
literal maximum and contains neither `R.card` nor a source `KT / d` envelope.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceActualParentLocalKatzTaoProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6PlankKatzTaoFrostmanActualAdaptersV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8SelectedOccurrenceActiveParentOwnerV5
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceActiveParentOwnerV11
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyFiniteFamilyMaximalConcentrationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {delta rho a b : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-! ## Exact occurrence-position bookkeeping -/

/-- The selected outer body at a subtype index is the winning body at its
decoded literal greedy position. -/
theorem selectedOccurrenceOuterFamily_eq_blockAt_position
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    selectedOccurrenceOuterFamily P R q =
      (blockAt fine.bodyFamily P
        (selectedOccurrencePosition C R q)).body := by
  let k := selectedOccurrencePosition C R q
  have hk : k ∈ R := by
    simpa only [k] using selectedOccurrencePosition_mem C R q
  have hq : q = selectedOccurrenceIndexOf P R k hk := by
    simpa only [k] using selectedOccurrence_eq_indexOf C R q
  calc
    selectedOccurrenceOuterFamily P R q =
        selectedOccurrenceOuterFamily P R
          (selectedOccurrenceIndexOf P R k hk) :=
      congrArg (selectedOccurrenceOuterFamily P R) hq
    _ = (blockAt fine.bodyFamily P k).body :=
      selectedOccurrenceOuterFamily_indexOf P R k hk

/-- Decoding selected occurrence labels back to greedy positions is
injective. -/
theorem selectedOccurrencePosition_injective
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    Function.Injective (selectedOccurrencePosition C R) := by
  intro q q' hposition
  apply Subtype.ext
  calc
    q.1 = some (selectedOccurrencePosition C R q) :=
      (some_selectedOccurrencePosition_eq C R q).symm
    _ = some (selectedOccurrencePosition C R q') :=
      congrArg some hposition
    _ = q'.1 := some_selectedOccurrencePosition_eq C R q'

/-! ## Unit-density mass transport to one literal source-parent fibre -/

/-- Density at least one is exactly the scalar input needed to pay for the
winning-body volume by its block mass. -/
theorem blockBodyVolume_le_blockMass_of_one_le_density
    (k : Fin (blocks fine.bodyFamily P).length)
    (hDensity : 1 ≤ blockDensity fine.bodyFamily
      (blockAt fine.bodyFamily P k)) :
    volume ((blockAt fine.bodyFamily P k).body : Set Space) ≤
      blockMass fine.bodyFamily (blockAt fine.bodyFamily P k) := by
  simpa only [one_mul] using
    (lower_mul_volume_le_blockMass fine.bodyFamily
      (blockAt fine.bodyFamily P k) 1 hDensity)

/-- For one actual parent and one convex test body, the contained mass of
retained occurrence hulls is bounded by the contained mass of the literal
sticky fine fibre.  This is the central loss-free combinatorial adapter. -/
theorem containedMassOn_actualParentOwner_le_sourceParentFiber
    (hpure : ParentPure C P)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (hfamily : D.family = selectedOccurrenceOuterFamily P R)
    (hblockVolume : ∀ k, k ∈ R →
      volume ((blockAt fine.bodyFamily P k).body : Set Space) ≤
        blockMass fine.bodyFamily (blockAt fine.bodyFamily P k))
    (p : Fin C.coarseCard) (K : ConvexBody Space) :
    containedMassOn D.family
        (ownerFiberIndices (selectedOccurrenceActiveParent C R) p) K ≤
      containedMassOn fine.bodyFamily (C.fiber p) K := by
  let owner := selectedOccurrenceActiveParent C R
  let Q := ownerFiberIndices owner p ∩ containedIndices D.family K
  let U := Q.biUnion fun q =>
    (blockAt fine.bodyFamily P (selectedOccurrencePosition C R q)).fiber
  have hdisjoint :
      (↑Q : Set {q // q ∈ selectedOccurrenceIndices P R}).PairwiseDisjoint
        (fun q =>
          (blockAt fine.bodyFamily P
            (selectedOccurrencePosition C R q)).fiber) := by
    intro q hq q' hq' hne
    have hpositionNe : selectedOccurrencePosition C R q ≠
        selectedOccurrencePosition C R q' := by
      intro hposition
      exact hne (selectedOccurrencePosition_injective C R hposition)
    exact blockAt_fibers_pairwiseDisjoint fine.bodyFamily P R
      (selectedOccurrencePosition_mem C R q)
      (selectedOccurrencePosition_mem C R q') hpositionNe
  have hUsubset :
      U ⊆ C.fiber p ∩ containedIndices fine.bodyFamily K := by
    intro i hi
    obtain ⟨q, hqQ, hiBlock⟩ := Finset.mem_biUnion.mp hi
    have hqData := Finset.mem_inter.mp hqQ
    have hqOwner : owner q = p :=
      (mem_ownerFiberIndices owner p q).mp hqData.1
    have hiActive : i ∈ C.activeFine :=
      blockAt_fiber_subset_active fine.bodyFamily P
        (selectedOccurrencePosition C R q) hiBlock
    have hiParent : C.parent i = p := by
      calc
        C.parent i = occurrenceActiveParent C P
            (selectedOccurrencePosition C R q) :=
          hpure (selectedOccurrencePosition C R q) i hiBlock
        _ = owner q := rfl
        _ = p := hqOwner
    have hiFiber : i ∈ C.fiber p :=
      (C.mem_fiber i p).2 ⟨hiActive, hiParent⟩
    have hqContained : (D.family q : Set Space) ⊆ (K : Set Space) :=
      (mem_containedIndices D.family K q).1 hqData.2
    have hbodyEq : D.family q =
        (blockAt fine.bodyFamily P
          (selectedOccurrencePosition C R q)).body := by
      rw [hfamily]
      exact selectedOccurrenceOuterFamily_eq_blockAt_position C R q
    have hiContained : (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) :=
      ((blockAt fine.bodyFamily P
          (selectedOccurrencePosition C R q)).contained i hiBlock).trans
        (by simpa only [hbodyEq] using hqContained)
    exact Finset.mem_inter.mpr
      ⟨hiFiber, (mem_containedIndices fine.bodyFamily K i).2 hiContained⟩
  have hmain :
      (∑ q ∈ Q, volume (D.family q : Set Space)) ≤
        ∑ i ∈ C.fiber p ∩ containedIndices fine.bodyFamily K,
          volume (fine.bodyFamily i : Set Space) := by
    calc
      (∑ q ∈ Q, volume (D.family q : Set Space)) ≤
          ∑ q ∈ Q, blockMass fine.bodyFamily
            (blockAt fine.bodyFamily P
              (selectedOccurrencePosition C R q)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hbodyEq : D.family q =
            (blockAt fine.bodyFamily P
              (selectedOccurrencePosition C R q)).body := by
          rw [hfamily]
          exact selectedOccurrenceOuterFamily_eq_blockAt_position C R q
        rw [hbodyEq]
        exact hblockVolume (selectedOccurrencePosition C R q)
          (selectedOccurrencePosition_mem C R q)
      _ = ∑ i ∈ U, volume (fine.bodyFamily i : Set Space) := by
        dsimp only [U]
        unfold blockMass
        exact (Finset.sum_biUnion hdisjoint).symm
      _ ≤ ∑ i ∈ C.fiber p ∩ containedIndices fine.bodyFamily K,
          volume (fine.bodyFamily i : Set Space) :=
        Finset.sum_le_sum_of_subset hUsubset
  calc
    containedMassOn D.family
        (ownerFiberIndices (selectedOccurrenceActiveParent C R) p) K =
        ∑ q ∈ Q, volume (D.family q : Set Space) := by
      unfold containedMassOn
      apply Finset.sum_congr
      · ext q
        simp only [Q, owner, Finset.mem_inter]
      · intro q hq
        rfl
    _ ≤ ∑ i ∈ C.fiber p ∩ containedIndices fine.bodyFamily K,
        volume (fine.bodyFamily i : Set Space) := hmain
    _ = containedMassOn fine.bodyFamily (C.fiber p) K := by
      unfold containedMassOn
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_inter]
      · intro i hi
        rfl

/-- A Katz--Tao certificate on one literal sticky source-parent fibre
transfers without loss to the matching occurrence-hull owner indices. -/
theorem actualParentOwner_isKatzTaoOn_of_sourceParentFiber
    (hpure : ParentPure C P)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (hfamily : D.family = selectedOccurrenceOuterFamily P R)
    (hblockVolume : ∀ k, k ∈ R →
      volume ((blockAt fine.bodyFamily P k).body : Set Space) ≤
        blockMass fine.bodyFamily (blockAt fine.bodyFamily P k))
    (A : ENNReal) (p : Fin C.coarseCard)
    (hparentKT : IsKatzTao A (C.fiberFamily p)) :
    IsKatzTaoOn A D.family
      (ownerFiberIndices (selectedOccurrenceActiveParent C R) p) := by
  intro K
  have hparent := hparentKT K
  change containedMass
      (activeSubtypeFamily fine.bodyFamily (C.fiber p)) K ≤
        A * volume (K : Set Space) at hparent
  rw [containedMass_activeSubtypeFamily] at hparent
  exact (containedMassOn_actualParentOwner_le_sourceParentFiber
    C hpure R D hfamily hblockVolume p K).trans hparent

/-- Global source Katz--Tao control restricts to each literal sticky parent
fibre with the same coefficient.  This is the useful O(1) source certificate:
there is no density inverse and no parent-fibre cardinality factor. -/
theorem sourceParentFiber_isKatzTao_of_global
    (A : ENNReal) (hsourceKT : IsKatzTao A fine.bodyFamily)
    (p : Fin C.coarseCard) :
    IsKatzTao A (C.fiberFamily p) := by
  intro K
  have hglobal := hsourceKT K
  change containedMass
      (activeSubtypeFamily fine.bodyFamily (C.fiber p)) K ≤
        A * volume (K : Set Space)
  rw [containedMass_activeSubtypeFamily]
  calc
    containedMassOn fine.bodyFamily (C.fiber p) K ≤
        containedMassOn fine.bodyFamily Finset.univ K :=
      containedMassOn_mono (Finset.subset_univ _) K
    _ = containedMass fine.bodyFamily K :=
      containedMassOn_univ fine.bodyFamily K
    _ ≤ A * volume (K : Set Space) := hglobal

/-- The V11 consumer interface, produced from genuine source-parent fibre
Katz--Tao data and unit lower block density.  No global selected-occurrence
Katz--Tao theorem is proved or assumed. -/
theorem ownerFiberIsKatzTao_of_sourceParentFibers_and_one_le_density
    (hpure : ParentPure C P)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (hfamily : D.family = selectedOccurrenceOuterFamily P R)
    (Delta : NNReal)
    (hparentKT : ∀ p : Fin C.coarseCard,
      IsKatzTao (Delta : ENNReal) (C.fiberFamily p))
    (hDensity : ∀ k, k ∈ R →
      1 ≤ blockDensity fine.bodyFamily (blockAt fine.bodyFamily P k)) :
    OwnerFiberIsKatzTao (Delta := Delta) C D
      (selectedOccurrenceActiveParent C R) := by
  intro p
  apply isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
  apply actualParentOwner_isKatzTaoOn_of_sourceParentFiber
    C hpure R D hfamily
  · intro k hk
    exact blockBodyVolume_le_blockMass_of_one_le_density
      (C := C) k (hDensity k hk)
  · exact hparentKT p

/-- Direct V11 producer from a global source Katz--Tao theorem.  If the
source coefficient is O(1), the actual-parent owner fibres retain exactly
that O(1) coefficient. -/
theorem ownerFiberIsKatzTao_of_global_source_and_one_le_density
    (hpure : ParentPure C P)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (hfamily : D.family = selectedOccurrenceOuterFamily P R)
    (Delta : NNReal)
    (hsourceKT : IsKatzTao (Delta : ENNReal) fine.bodyFamily)
    (hDensity : ∀ k, k ∈ R →
      1 ≤ blockDensity fine.bodyFamily (blockAt fine.bodyFamily P k)) :
    OwnerFiberIsKatzTao (Delta := Delta) C D
      (selectedOccurrenceActiveParent C R) := by
  apply ownerFiberIsKatzTao_of_sourceParentFibers_and_one_le_density
    C hpure R D hfamily Delta
  · intro p
    exact sourceParentFiber_isKatzTao_of_global C
      (Delta : ENNReal) hsourceKT p
  · exact hDensity

/-! ## Canonical exact source-parent coefficient -/

/-- The literal worst maximal concentration over all sticky source-parent
fibres.  Inactive parent fibres are included; they are empty and hence do not
change the value. -/
def actualParentSourceFiberDeltaMax : ENNReal :=
  ⨆ p : Fin C.coarseCard, maximalConcentration (C.fiberFamily p)

/-- The exact all-parent maximum is finite.  The card bound is used only in
this proof and is not substituted into the public coefficient. -/
theorem actualParentSourceFiberDeltaMax_ne_top :
    actualParentSourceFiberDeltaMax C ≠ ∞ := by
  have hle : actualParentSourceFiberDeltaMax C ≤
      (C.activeFine.card : ENNReal) := by
    unfold actualParentSourceFiberDeltaMax
    apply iSup_le
    intro p
    calc
      maximalConcentration (C.fiberFamily p) ≤
          (Fintype.card {i // i ∈ C.fiber p} : ENNReal) :=
        maximalConcentration_le_card (C.fiberFamily p)
      _ = (C.fiber p).card := by
        exact_mod_cast Fintype.card_coe (C.fiber p)
      _ ≤ C.activeFine.card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  exact (hle.trans_lt (ENNReal.natCast_lt_top C.activeFine.card)).ne

/-- Finite `NNReal` representative of the literal source-parent maximum. -/
def actualParentSourceFiberDelta : NNReal :=
  (actualParentSourceFiberDeltaMax C).toNNReal

theorem actualParentSourceFiberDelta_coe :
    (actualParentSourceFiberDelta C : ENNReal) =
      actualParentSourceFiberDeltaMax C := by
  unfold actualParentSourceFiberDelta
  rw [ENNReal.coe_toNNReal]
  exact actualParentSourceFiberDeltaMax_ne_top C

/-- Every source-parent fibre has Katz--Tao constant equal to the literal
all-parent maximum. -/
theorem sourceParentFiber_isKatzTao_actualDelta
    (p : Fin C.coarseCard) :
    IsKatzTao (actualParentSourceFiberDelta C : ENNReal)
      (C.fiberFamily p) := by
  apply isKatzTao_iff_maximalConcentration_le.mpr
  rw [actualParentSourceFiberDelta_coe C]
  exact le_iSup
    (fun q : Fin C.coarseCard =>
      maximalConcentration (C.fiberFamily q)) p

/-- Fully automatic V11 local-KT producer at the exact source-parent
coefficient, assuming only parent purity and the CoreHigh-style unit density
floor on the retained occurrences. -/
theorem ownerFiberIsKatzTao_actualParentSourceDelta_of_one_le_density
    (hpure : ParentPure C P)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (hfamily : D.family = selectedOccurrenceOuterFamily P R)
    (hDensity : ∀ k, k ∈ R →
      1 ≤ blockDensity fine.bodyFamily (blockAt fine.bodyFamily P k)) :
    OwnerFiberIsKatzTao
      (Delta := actualParentSourceFiberDelta C) C D
      (selectedOccurrenceActiveParent C R) := by
  apply ownerFiberIsKatzTao_of_sourceParentFibers_and_one_le_density
    C hpure R D hfamily (actualParentSourceFiberDelta C)
  · exact sourceParentFiber_isKatzTao_actualDelta C
  · exact hDensity

/-! ## CoreHigh scalar bridge -/

/-- A CoreHigh occurrence above a threshold at least one supplies exactly
the unit density floor consumed by the preceding producer. -/
theorem one_le_blockDensity_of_coreHighOccurrence
    (D : ActualTubeDatum delta index)
    (Pcore : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (highThreshold : ENNReal) (hThreshold : 1 ≤ highThreshold)
    (k : Fin (blocks D.family.bodyFamily Pcore).length)
    (hcore : CoreHighConcentrationOccurrence D Pcore highThreshold k) :
    1 ≤ blockDensity D.family.bodyFamily
      (blockAt D.family.bodyFamily Pcore k) :=
  hThreshold.trans hcore.1.le

#print axioms selectedOccurrenceOuterFamily_eq_blockAt_position
#print axioms selectedOccurrencePosition_injective
#print axioms containedMassOn_actualParentOwner_le_sourceParentFiber
#print axioms actualParentOwner_isKatzTaoOn_of_sourceParentFiber
#print axioms sourceParentFiber_isKatzTao_of_global
#print axioms ownerFiberIsKatzTao_of_sourceParentFibers_and_one_le_density
#print axioms ownerFiberIsKatzTao_of_global_source_and_one_le_density
#print axioms actualParentSourceFiberDeltaMax
#print axioms actualParentSourceFiberDelta_coe
#print axioms sourceParentFiber_isKatzTao_actualDelta
#print axioms
  ownerFiberIsKatzTao_actualParentSourceDelta_of_one_le_density
#print axioms one_le_blockDensity_of_coreHighOccurrence

end

end Family8SelectedOccurrenceActualParentLocalKatzTaoProducerV1

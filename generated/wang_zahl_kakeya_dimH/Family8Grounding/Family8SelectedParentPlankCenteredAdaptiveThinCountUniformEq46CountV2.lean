import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountFullFiberOrHullThinV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredAdaptiveThinCountFullFiberOrHullThinV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Uniform natural Eq. (46) count on one actual selected-parent bucket

The single-`W` full-fibre cap is maximized over the finite literal bucket.
This produces one honest `tubesPerPlank` for every member.  Since the bucket
cardinality is at most the active-parent cardinality, choosing
`countLoss = tubesPerPlank` closes the outer Eq. (46) count inequality.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Finite maximum of the literal full-fibre caps attached to every member
of one actual plank bucket. -/
def centeredAdaptiveUniformFullFiberNatCap
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (hplank : ∀ W : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (C : ENNReal) : Nat :=
  Finset.univ.sup fun W : {p // p ∈
      selectedParentPlankBucketIndices e S B hrho label} ↦
    adaptiveThinCountFullFiberNatCap
      (centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C) label

theorem actualFullFiberNatCap_le_centeredAdaptiveUniform
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (hplank : ∀ W : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (C : ENNReal)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label}) :
    adaptiveThinCountFullFiberNatCap
        (centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
          s e S B hrho label hplank W C) label ≤
      centeredAdaptiveUniformFullFiberNatCap
        s e S B hrho label hplank C := by
  classical
  unfold centeredAdaptiveUniformFullFiberNatCap
  exact Finset.le_sup (s := Finset.univ)
    (f := fun V : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label} ↦
        adaptiveThinCountFullFiberNatCap
          (centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
            s e S B hrho label hplank V C) label)
    (Finset.mem_univ W)

/-- The actual selected bucket has no more elements than the active-parent
type.  This is the literal subtype-cardinality comparison, independent of
any mass or multiplicity callback. -/
theorem selectedParentPlankBucketIndexType_card_le_active
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (e : Space ≃ᵃ[Real] Space) (label : Fin 3 → Int) :
    Fintype.card {p // p ∈ selectedParentPlankBucketIndices
      e S (blockAt S.activeCoarseFamily P k).fiber hrho label} ≤
      Fintype.card (ActiveParentIndex S) := by
  calc
    Fintype.card {p // p ∈ selectedParentPlankBucketIndices
        e S (blockAt S.activeCoarseFamily P k).fiber hrho label} =
        (selectedParentPlankBucketIndices e S
          (blockAt S.activeCoarseFamily P k).fiber hrho label).card := by
      rw [Fintype.card_coe]
    _ ≤ (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_univ p
    _ = (blockAt S.activeCoarseFamily P k).fiber.card := by
      rw [Finset.card_univ, Fintype.card_coe]
    _ ≤ Fintype.card (ActiveParentIndex S) := Finset.card_le_univ _

/-- Callback-free outer Eq. (46) count with the actual finite uniform cap.
The right-hand count loss is exactly the chosen `tubesPerPlank`. -/
theorem selectedParent_centeredAdaptive_uniformEq46Count
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hplank : ∀ W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label W))
    (C : ENNReal) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let s := selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label
    let plankCount := Fintype.card {p // p ∈
      selectedParentPlankBucketIndices e S B hrho label}
    let tubesPerPlank := centeredAdaptiveUniformFullFiberNatCap
      s e S B hrho label hplank C
    ((plankCount * tubesPerPlank : Nat) : ENNReal) ≤
      (tubesPerPlank : ENNReal) *
        (Fintype.card (ActiveParentIndex S) : ENNReal) := by
  dsimp only
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let s := selectedParentCenteredHalfPostAdaptiveProxyScale
    delta rho r label
  let plankCount := Fintype.card {p // p ∈
    selectedParentPlankBucketIndices e S B hrho label}
  let tubesPerPlank := centeredAdaptiveUniformFullFiberNatCap
    s e S B hrho label hplank C
  have hplankCount : plankCount ≤ Fintype.card (ActiveParentIndex S) := by
    simpa only [e, B, plankCount] using
      selectedParentPlankBucketIndexType_card_le_active
        S hrho P k e label
  have hplankCountENN : (plankCount : ENNReal) ≤
      (Fintype.card (ActiveParentIndex S) : ENNReal) := by
    exact_mod_cast hplankCount
  calc
    ((plankCount * tubesPerPlank : Nat) : ENNReal) =
        (plankCount : ENNReal) * (tubesPerPlank : ENNReal) := by norm_num
    _ ≤ (Fintype.card (ActiveParentIndex S) : ENNReal) *
        (tubesPerPlank : ENNReal) := mul_le_mul' hplankCountENN le_rfl
    _ = (tubesPerPlank : ENNReal) *
        (Fintype.card (ActiveParentIndex S) : ENNReal) := mul_comm _ _

#print axioms actualFullFiberNatCap_le_centeredAdaptiveUniform
#print axioms selectedParentPlankBucketIndexType_card_le_active
#print axioms selectedParent_centeredAdaptive_uniformEq46Count

end
end Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2

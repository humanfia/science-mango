import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV4
import Family8Grounding.Family8SelectedParentPlankFreshFullFiberCountV1
import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV8
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import FamilyStickyCinematicL32FiniteWeightedBucketV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2

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
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredAdaptiveThinCountFullFiberOrHullThinV3
open Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV4
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFreshFullFiberCountV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

/-!
# One honest global fibre cap for the selected-parent Prop. 6.6(A) consumer

The block and occupied-label choices made downstream are both finite.  This
file first produces the plank certificate directly from literal bucket
membership, then maximizes the already SAFE per-bucket cap over those two
finite choices.  The resulting natural is independent of the downstream
choice of `k` and `label`, exactly as required by the scalar consumer.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Every literal selected-parent side-shape bucket is automatically a
`576`-plank bucket.  If it is nonempty, one member supplies the coordinate
ordering used to prove `bucketShortB ≤ 1`; empty buckets are vacuous. -/
theorem selectedParentLiteralPlankBucket_isPlank
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    ∀ W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W) := by
  dsimp only
  intro W
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let p : {p // p ∈ B} := W.1
  have hpBucket : p ∈ sideShapeBucket Finset.univ
      (fun q ↦ selectedParentLongRelabeledSide e S B hrho q) label := by
    exact W.2
  have hpLabel : sideShapeLabel
      (selectedParentLongRelabeledSide e S B hrho p) = label :=
    (mem_sideShapeBucket_iff Finset.univ
      (fun q ↦ selectedParentLongRelabeledSide e S B hrho q) label p).mp
      hpBucket |>.2
  have hpos : ∀ i, 0 < selectedParentLongRelabeledSide e S B hrho p i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho p i
  have h02 := sideShapeUpper_le_of_side_le hpos
    (selectedParentLongRelabeledSide_le_two e S B hrho p 0)
  have h12 := sideShapeUpper_le_of_side_le hpos
    (selectedParentLongRelabeledSide_le_two e S B hrho p 1)
  rw [hpLabel] at h02 h12
  have hb : bucketShortB label ≤ 1 :=
    bucketShortB_le_one label h02 h12
  have hband : ∀ i,
      sideShapeUpper label i / 2 <
          selectedParentLongRelabeledSide e S B hrho p i ∧
        selectedParentLongRelabeledSide e S B hrho p i ≤
          sideShapeUpper label i := by
    intro i
    have hi := sideShapeUpper_half_lt_and_le hpos i
    simpa only [hpLabel] using hi
  exact selectedParentNormalizedBucket_isPlank e S B hrho label p hb
    (normalizedBucketSide_sideWidthEnvelope hband)

/-- The finite set of actual occupied shape labels at one greedy block. -/
def selectedParentOccupiedShapeLabels
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) : Finset (Fin 3 → Int) :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  occupiedWeightBuckets (Finset.univ : Finset {p // p ∈ B})
    (fun p ↦ sideShapeLabel
      (selectedParentLongRelabeledSide e S B hrho p))

/-- One natural full-fibre cap, maximized first over the actual occupied
labels of a block and then over every greedy block. -/
def centeredAdaptiveGlobalFullFiberNatCap
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r) (C : ENNReal) : Nat :=
  Finset.univ.sup fun k : Fin (blocks S.activeCoarseFamily P).length ↦
    (selectedParentOccupiedShapeLabels S hrho P k r hr).sup fun label ↦
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let B := (blockAt S.activeCoarseFamily P k).fiber
      let s := selectedParentCenteredHalfPostAdaptiveProxyScale
        delta rho r label
      centeredAdaptiveUniformFullFiberNatCap
        s e S B hrho label
          (selectedParentLiteralPlankBucket_isPlank
            S hrho P k r hr label) C

/-- Every actual occupied `(k,label)` bucket cap is below the single global
natural cap. -/
theorem centeredAdaptiveUniformFullFiberNatCap_le_global
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hoccupied : label ∈ selectedParentOccupiedShapeLabels S hrho P k r hr)
    (C : ENNReal) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let s := selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label
    centeredAdaptiveUniformFullFiberNatCap
        s e S B hrho label
          (selectedParentLiteralPlankBucket_isPlank
            S hrho P k r hr label) C ≤
      centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C := by
  dsimp only
  let inner : Fin (blocks S.activeCoarseFamily P).length → Nat := fun j ↦
    (selectedParentOccupiedShapeLabels S hrho P j r hr).sup fun ell ↦
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P j) r hr
      let B := (blockAt S.activeCoarseFamily P j).fiber
      let s := selectedParentCenteredHalfPostAdaptiveProxyScale
        delta rho r ell
      centeredAdaptiveUniformFullFiberNatCap
        s e S B hrho ell
          (selectedParentLiteralPlankBucket_isPlank
            S hrho P j r hr ell) C
  have hlabel : centeredAdaptiveUniformFullFiberNatCap
        (selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label)
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho label
          (selectedParentLiteralPlankBucket_isPlank
            S hrho P k r hr label) C ≤ inner k := by
    dsimp only [inner]
    exact Finset.le_sup
      (s := selectedParentOccupiedShapeLabels S hrho P k r hr)
      (f := fun ell ↦
        centeredAdaptiveUniformFullFiberNatCap
          (selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r ell)
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho ell
            (selectedParentLiteralPlankBucket_isPlank
              S hrho P k r hr ell) C)
      hoccupied
  have hk : inner k ≤ Finset.univ.sup inner :=
    Finset.le_sup (s := Finset.univ) (f := inner) (Finset.mem_univ k)
  exact hlabel.trans (by
    simpa only [centeredAdaptiveGlobalFullFiberNatCap, inner] using hk)

/-- A single-`W` full-fibre result using the canonical literal plank
certificate is uniformly bounded by the global cap. -/
theorem selectedFineCard_le_centeredAdaptiveGlobal_of_actualCap
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hoccupied : label ∈ selectedParentOccupiedShapeLabels S hrho P k r hr)
    (C : ENNReal)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (hfull : Fintype.card (SelectedPlankFineIndex S W) ≤
      adaptiveThinCountFullFiberNatCap
        (centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
          (selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label)
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label
          (selectedParentLiteralPlankBucket_isPlank
            S hrho P k r hr label) W C) label) :
    Fintype.card (SelectedPlankFineIndex S W) ≤
      centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C := by
  exact (selectedFineCard_le_centeredAdaptiveUniform_of_actualCap
    (selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label)
    (contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
    S (blockAt S.activeCoarseFamily P k).fiber hrho label
    (selectedParentLiteralPlankBucket_isPlank S hrho P k r hr label)
    C W hfull).trans
      (centeredAdaptiveUniformFullFiberNatCap_le_global
        S hrho P k r hr label hoccupied C)

/-- The global full-fibre cap is in the correct monotone direction for the
actual Proposition 6.6(A) inner scalar. -/
theorem proposition66AInnerFactor_selectedFine_le_centeredAdaptiveGlobal
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hoccupied : label ∈ selectedParentOccupiedShapeLabels S hrho P k r hr)
    (C : ENNReal)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    {epsilon beta : Real} (hbetaOne : beta ≤ 1)
    (hfull : Fintype.card (SelectedPlankFineIndex S W) ≤
      adaptiveThinCountFullFiberNatCap
        (centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
          (selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label)
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label
          (selectedParentLiteralPlankBucket_isPlank
            S hrho P k r hr label) W C) label) :
    proposition66AInnerFactor rho (bucketShortA label) (bucketShortB label)
        (Fintype.card (SelectedPlankFineIndex S W)) epsilon beta ≤
      proposition66AInnerFactor rho (bucketShortA label) (bucketShortB label)
        (centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C)
        epsilon beta := by
  exact proposition66AInnerFactor_mono_tubesPerPlank
    (hbetaOne.trans (by norm_num))
    (selectedFineCard_le_centeredAdaptiveGlobal_of_actualCap
      S hrho P k r hr label hoccupied C W hfull)

/-- Callback-free global Eq. (46) count.  The outer plank count is the
literal active-parent cardinality, while both `tubesPerPlank` and
`countLoss` are the actual global cap. -/
theorem selectedParent_centeredAdaptive_globalEq46Count
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r) (C : ENNReal) :
    let plankCount := Fintype.card (ActiveParentIndex S)
    let tubesPerPlank := centeredAdaptiveGlobalFullFiberNatCap
      S hrho P r hr C
    ((plankCount * tubesPerPlank : Nat) : ENNReal) ≤
      (tubesPerPlank : ENNReal) *
        (Fintype.card (ActiveParentIndex S) : ENNReal) := by
  dsimp only
  norm_num [mul_comm]

#print axioms selectedParentLiteralPlankBucket_isPlank
#print axioms centeredAdaptiveUniformFullFiberNatCap_le_global
#print axioms selectedFineCard_le_centeredAdaptiveGlobal_of_actualCap
#print axioms proposition66AInnerFactor_selectedFine_le_centeredAdaptiveGlobal
#print axioms selectedParent_centeredAdaptive_globalEq46Count

end
end Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2

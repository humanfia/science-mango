import Family8Grounding.Family8ThinPlankFivePackingNatCapLowerV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
import Mathlib.Tactic

/-!
# Actual selected-parent adaptive cap dominates the bucket aspect square

The literal five-parameter packing grid already contains the quadratic
aspect reserve.  Occupancy supplies a genuine member of the same bucket, so
the local reserve passes through both finite suprema to the exact global cap
used by Equation (46).
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentAdaptiveGlobalCapAspectLowerV1

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
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFivePackingNatCapLowerV1
open Family8ThinPlankFiveParameterPackingV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-- Every literal adaptive single-fibre cap contains the full square of its
actual selected-plank aspect. -/
theorem bucketAspect_sq_le_adaptiveThinCountFullFiberNatCap
    (Cproxy : ENNReal) (label : Fin 3 -> Int) :
    ((bucketShortB label : ENNReal) /
        (bucketShortA label : ENNReal)) ^ (2 : Nat) <=
      (adaptiveThinCountFullFiberNatCap Cproxy label : ENNReal) := by
  let a := bucketShortA label
  let b := bucketShortB label
  have ha : 0 < a := bucketShortA_pos label
  have hscaled := aspect_sq_le_thinPlankFivePackingNatCap
    a ((3 : NNReal) * b) ha
  have haspectNonneg :
      0 <= (b : ENNReal) / (a : ENNReal) := bot_le
  have haspectScale :
      ((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat) <=
        ((((3 : NNReal) * b : NNReal) : ENNReal) /
          (a : ENNReal)) ^ (2 : Nat) := by
    apply pow_le_pow_left₀ haspectNonneg
    rw [ENNReal.coe_mul]
    calc
      (b : ENNReal) / (a : ENNReal) =
          1 * ((b : ENNReal) / (a : ENNReal)) := by simp
      _ <= 3 * ((b : ENNReal) / (a : ENNReal)) := by gcongr; norm_num
      _ = (3 * (b : ENNReal)) / (a : ENNReal) := by
        rw [mul_div_assoc]
  have hpack :
      ((((3 : NNReal) * b : NNReal) : ENNReal) /
          (a : ENNReal)) ^ (2 : Nat) <=
        (thinPlankFivePackingNatCap
          (3 * selectedPlankFineCanonicalAspect label) : ENNReal) := by
    simpa only [a, b, selectedPlankFineCanonicalAspect, NNReal.coe_mul,
      NNReal.coe_ofNat, mul_div_assoc] using hscaled
  have hnat :
      thinPlankFivePackingNatCap
          (3 * selectedPlankFineCanonicalAspect label) <=
        adaptiveThinCountFullFiberNatCap Cproxy label := by
    unfold adaptiveThinCountFullFiberNatCap
    have hone :
        1 <= Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1 := by
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right
      (thinPlankFivePackingNatCap
        (3 * selectedPlankFineCanonicalAspect label)) hone
  exact haspectScale.trans (hpack.trans (by exact_mod_cast hnat))

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The same aspect-square reserve survives the actual occupied-label and
greedy-block suprema defining the global Equation (46) cap. -/
theorem selectedParent_bucketAspect_sq_le_centeredAdaptiveGlobalFullFiberNatCap
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : label ∈ selectedParentOccupiedShapeLabels
      S hrho P k r hr)
    (C : ENNReal) :
    ((bucketShortB label : ENNReal) /
        (bucketShortA label : ENNReal)) ^ (2 : Nat) <=
      (centeredAdaptiveGlobalFullFiberNatCap
        S hrho P r hr C : ENNReal) := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  have hocc : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset {p // p ∈ B})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide e S B hrho p)) := by
    simpa only [selectedParentOccupiedShapeLabels, e, B] using hoccupied
  obtain ⟨p, _hp, hpLabel⟩ := mem_occupiedWeightBuckets_iff.mp hocc
  let W : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label} := ⟨p, by
    rw [selectedParentPlankBucketIndices, mem_sideShapeBucket_iff]
    exact ⟨Finset.mem_univ _, hpLabel⟩⟩
  let s := selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label
  let hplank := selectedParentLiteralPlankBucket_isPlank
    S hrho P k r hr label
  let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
    s e S B hrho label hplank W C
  have hlocal :
      ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) ^ (2 : Nat) <=
        (adaptiveThinCountFullFiberNatCap Cproxy label : ENNReal) :=
    bucketAspect_sq_le_adaptiveThinCountFullFiberNatCap Cproxy label
  have huniform : adaptiveThinCountFullFiberNatCap Cproxy label <=
      centeredAdaptiveUniformFullFiberNatCap
        s e S B hrho label hplank C := by
    exact actualFullFiberNatCap_le_centeredAdaptiveUniform
      s e S B hrho label hplank C W
  have hglobal : centeredAdaptiveUniformFullFiberNatCap
        s e S B hrho label hplank C <=
      centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C := by
    simpa only [s, e, B, hplank] using
      centeredAdaptiveUniformFullFiberNatCap_le_global
        S hrho P k r hr label hoccupied C
  exact hlocal.trans (by exact_mod_cast huniform.trans hglobal)

#print axioms bucketAspect_sq_le_adaptiveThinCountFullFiberNatCap
#print axioms
  selectedParent_bucketAspect_sq_le_centeredAdaptiveGlobalFullFiberNatCap

end
end Family8SelectedParentAdaptiveGlobalCapAspectLowerV1

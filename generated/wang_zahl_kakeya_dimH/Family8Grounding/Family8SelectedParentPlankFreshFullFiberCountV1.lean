import Family8Grounding.Family8SelectedParentPlankCanonicalThinCountV5
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentPlankFreshFullFiberCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyDatumV1
open Family8ThinPlankFiveParameterPackingV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# The honest full-fibre count supplied by fresh thin-plank packing

The five-parameter packing theorem bounds only the freshly selected set.
The greedy retention theorem bounds the original same-`W` fibre by the
fresh loss times that selected cardinality.  This file composes those two
facts and records the resulting natural number that can honestly be used as
the `tubesPerPlank` parameter in the Proposition 6.6(A) inner factor.

There is deliberately no shading or average-multiplicity conclusion here:
the proxy datum used by the packing construction has empty shading.  Thus
this closes the cardinality direction only and does not manufacture the
still-required same-`W` mass-retention estimate.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The exact natural full-fibre cap obtained by multiplying the fresh
greedy loss with the five-parameter cap. -/
def selectedPlankFineCanonicalFreshFullFiberNatCap
    (C : ENNReal) (label : Fin 3 → Int) : Nat :=
  (Nat.ceil ((480000 * (128 * C) : ENNReal).toReal) + 1) *
    thinPlankFivePackingNatCap
      (3 * selectedPlankFineCanonicalAspect label)

/-- Canonical fresh selection bounds the entire original same-`W` fibre by
the fresh loss times the selected five-parameter cap. -/
theorem selectedPlankFine_fullFiber_card_le_canonicalFreshFullFiberNatCap
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
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
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C
      (selectedPlankFineProxyDatum
        (selectedPlankFineCanonicalProxyScale r label)
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho label W).family.bodyFamily)
    (hsmall : selectedPlankFineCanonicalProxyScale r label / 8 ≤
      (1 / 100 : NNReal))
    (hthin :
      (((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real) ^ 2 +
        (selectedPlankFineCanonicalAspect label *
          ((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real)) ^ 2 ≤
        (3 : Real) / 4)) :
    Fintype.card (SelectedPlankFineIndex S W) ≤
      selectedPlankFineCanonicalFreshFullFiberNatCap C label := by
  obtain ⟨selected, _hselected, _hpair, hcard, _hselectedKT, _hloss,
      hthinCount⟩ :=
    exists_selectedPlankFine_canonicalFresh_with_thinCount
      hfineContained S hrho hrhoOne P k r hr label hplank W hCfinite hKT
        hsmall hthin
  let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
  have hselectedCast : (selected.card : ENNReal) ≤
      (thinPlankFivePackingNatCap
        (3 * selectedPlankFineCanonicalAspect label) : Nat) := by
    exact_mod_cast hthinCount
  have hfullCast : (Fintype.card (SelectedPlankFineIndex S W) : ENNReal) ≤
      ((threshold + 1) * thinPlankFivePackingNatCap
        (3 * selectedPlankFineCanonicalAspect label) : Nat) := by
    calc
      (Fintype.card (SelectedPlankFineIndex S W) : ENNReal) ≤
          (threshold + 1 : Nat) * (selected.card : ENNReal) := hcard
      _ ≤ (threshold + 1 : Nat) *
          (thinPlankFivePackingNatCap
            (3 * selectedPlankFineCanonicalAspect label) : Nat) :=
        mul_le_mul' le_rfl hselectedCast
      _ = (((threshold + 1) * thinPlankFivePackingNatCap
          (3 * selectedPlankFineCanonicalAspect label) : Nat) : ENNReal) := by
        norm_num
  exact_mod_cast hfullCast

/-- The Proposition 6.6(A) inner scalar is monotone in the natural fibre
count when `beta ≤ 2`. -/
theorem proposition66AInnerFactor_mono_tubesPerPlank
    {delta a b : NNReal} {m n : Nat} {epsilon beta : Real}
    (hbetaTwo : beta ≤ 2) (hmn : m ≤ n) :
    proposition66AInnerFactor delta a b m epsilon beta ≤
      proposition66AInnerFactor delta a b n epsilon beta := by
  have hp : 0 ≤ 1 - beta / 2 := by linarith
  unfold proposition66AInnerFactor
  apply mul_le_mul' le_rfl
  apply ENNReal.rpow_le_rpow _ hp
  exact mul_le_mul' le_rfl (by exact_mod_cast hmn)

/-- Consequently the cap produced above is in the correct direction for the
inner factor.  This theorem consumes only an already proved full-fibre count;
the canonical geometric producer is the preceding theorem. -/
theorem proposition66AInnerFactor_fullFiber_le_freshThinCap
    {delta a b : NNReal} {epsilon beta : Real}
    {S : StickyScaleCover fine rho}
    {B : Finset (ActiveParentIndex S)} {hrho : 0 < rho}
    {label : Fin 3 → Int}
    {W : {p // p ∈ selectedParentPlankBucketIndices
      (AffineEquiv.refl Real Space) S B hrho label}}
    {C : ENNReal}
    (hbetaTwo : beta ≤ 2)
    (hfull : Fintype.card (SelectedPlankFineIndex S W) ≤
      selectedPlankFineCanonicalFreshFullFiberNatCap C label) :
    proposition66AInnerFactor delta a b
        (Fintype.card (SelectedPlankFineIndex S W)) epsilon beta ≤
      proposition66AInnerFactor delta a b
        (selectedPlankFineCanonicalFreshFullFiberNatCap C label)
        epsilon beta := by
  exact proposition66AInnerFactor_mono_tubesPerPlank hbetaTwo hfull

#print axioms selectedPlankFine_fullFiber_card_le_canonicalFreshFullFiberNatCap
#print axioms proposition66AInnerFactor_mono_tubesPerPlank
#print axioms proposition66AInnerFactor_fullFiber_le_freshThinCap

end
end Family8SelectedParentPlankFreshFullFiberCountV1

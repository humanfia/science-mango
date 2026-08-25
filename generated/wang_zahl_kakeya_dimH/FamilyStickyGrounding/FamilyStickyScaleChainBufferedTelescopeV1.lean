import FamilyStickyGrounding.FamilyStickyScaleChainBufferedHierarchyProducerV1

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainBufferedTelescopeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyAdjacentTestBodyGeometryV1
open FamilyStickyAdjacentTestBodyGeometryV1.StickyScaleCover
open FamilyStickyScaleChainNormalizedIntegrationV1
open FamilyStickyScaleChainBufferedHierarchyNormalizedV1.StickyScaleCover
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy

noncomputable section

/-!
# Sticky Kakeya: actual buffered test-body telescope

This module packages the geometric data needed to turn an honest buffered
tube hierarchy into the frozen `NormalizedScaleChain`:

* test bodies evolve by the proved `K -> K^(+4 rho_eff)` construction;
* each next tube normalization is a genuine lower bound for captured parents;
* each current test-body volume is bounded by an explicit dimensional loss
  times its current tube normalization.

No normalized adjacent inequality is stored as a field.  It is produced by
the actual parent/fiber decomposition and thickening theorem, after which the
finite product telescopes to an endpoint ratio.
-/

namespace MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {card : Nat -> Nat}
  (H : MultiscaleTubeHierarchy depth nominalRadius
    (fun l => Fin (card l)))

/-- Geometric and measure data for one recursively thickened test-body chain.
The local volume-envelope factor is kept as `dimensionalLoss`. -/
structure BufferedTestBodyChain where
  testBody : Nat -> ConvexBody Space
  tubeVolume : Nat -> ENNReal
  dimensionalLoss : Nat -> ENNReal
  bodyVolume_ne_zero : ∀ m, m <= depth ->
    MeasureTheory.volume (testBody m : Set Space) ≠ 0
  tubeVolume_ne_zero : ∀ m, m <= depth -> tubeVolume m ≠ 0
  tubeVolume_ne_top : ∀ m, m <= depth -> tubeVolume m ≠ ∞
  loss_mul_tube_ne_zero : ∀ m, m < depth ->
    dimensionalLoss m * tubeVolume m ≠ 0
  loss_mul_tube_ne_top : ∀ m, m < depth ->
    dimensionalLoss m * tubeVolume m ≠ ∞
  bodyVolume_envelope : ∀ m, m < depth ->
    MeasureTheory.volume (testBody m : Set Space) <=
      dimensionalLoss m * tubeVolume m
  nextTubeFloor : ∀ m (hm : m < depth) k,
    k ∈ capturedCoarseIndices (effectiveStickyScaleCover H m hm) (testBody m) ->
    tubeVolume (m + 1) <= MeasureTheory.volume
      ((effectiveStickyScaleCover H m hm).activeCoarseFamily k : Set Space)
  testBody_succ : ∀ m (_hm : m < depth),
    testBody (m + 1) =
      closedThickeningBody (testBody m)
        (4 * H.effectiveRadius (m + 1))
  top_le_one :
    concentration (effectiveActiveFamily H depth) (testBody depth) <= 1

namespace BufferedTestBodyChain

/-- The literal local factor: volume-envelope loss times the actual worst
fiber concentration of the buffered adjacent cover. -/
def localFactor (D : BufferedTestBodyChain H) (m : Nat) : ENNReal :=
  if hm : m < depth then
    D.dimensionalLoss m *
      fiberDeltaMax (effectiveStickyScaleCover H m hm)
  else 1

/-- All inputs of the generic normalized telescope are now actual hierarchy
and test-body values; its primitive step is proved, not supplied. -/
def toNormalizedScaleChain (D : BufferedTestBodyChain H) :
    NormalizedScaleChain depth where
  value := fun m =>
    concentration (effectiveActiveFamily H m) (D.testBody m)
  localFactor := localFactor H D
  bodyVolume := fun m => MeasureTheory.volume (D.testBody m : Set Space)
  tubeVolume := D.tubeVolume
  bodyVolume_ne_zero := D.bodyVolume_ne_zero
  bodyVolume_ne_top := by
    intro m hm
    exact (D.testBody m).isCompact.measure_lt_top.ne
  tubeVolume_ne_zero := D.tubeVolume_ne_zero
  tubeVolume_ne_top := D.tubeVolume_ne_top
  normalized_step := by
    intro m hm
    rw [D.testBody_succ m hm]
    simpa only [localFactor, dif_pos hm] using
      effective_normalized_adjacent_cross_with_volumeEnvelope_le
      H m hm (D.testBody m) (D.tubeVolume m) (D.tubeVolume (m + 1))
        (D.dimensionalLoss m)
        (D.loss_mul_tube_ne_zero m hm)
        (D.loss_mul_tube_ne_top m hm)
        (D.bodyVolume_envelope m hm)
        (D.nextTubeFloor m hm)
  top_le_one := D.top_le_one

/-- The full actual hierarchy bound with every buffer and volume cost kept in
the endpoint ratio. -/
theorem global_le_endpointRatio (D : BufferedTestBodyChain H) :
    concentration (effectiveActiveFamily H 0) (D.testBody 0) <=
      (∏ m ∈ Finset.range depth, localFactor H D m) *
        ((MeasureTheory.volume (D.testBody depth : Set Space) /
            MeasureTheory.volume (D.testBody 0 : Set Space)) *
          (D.tubeVolume 0 / D.tubeVolume depth)) := by
  exact (toNormalizedScaleChain H D).global_le_endpointRatio

/-- If the two endpoint normalizations cost at most one, only the product of
actual fiber factors and explicit volume-envelope losses remains. -/
theorem global_le_prod_local_of_endpointRatio_le_one
    (D : BufferedTestBodyChain H)
    (hendpoint :
      (MeasureTheory.volume (D.testBody depth : Set Space) /
          MeasureTheory.volume (D.testBody 0 : Set Space)) *
        (D.tubeVolume 0 / D.tubeVolume depth) <= 1) :
    concentration (effectiveActiveFamily H 0) (D.testBody 0) <=
      ∏ m ∈ Finset.range depth, localFactor H D m := by
  exact (toNormalizedScaleChain H D).global_le_prod_local_of_endpointRatio_le_one
    hendpoint

/-- The canonical lower normalization supplied by the explicit tube-volume
bound at one effective hierarchy radius. -/
def actualTubeFloor (m : Nat) : ENNReal :=
  (H.effectiveRadius m : ENNReal) ^ 2 / 2

/-- At an effective radius at most one half, the canonical next tube floor is
automatic for every captured parent. -/
theorem actualTubeFloor_le_capturedParentVolume
    (D : BufferedTestBodyChain H) (m : Nat) (hm : m < depth)
    (hradius : H.effectiveRadius (m + 1) <= (2 : NNReal)⁻¹)
    (k : {k // k ∈
      capturedCoarseIndices (effectiveStickyScaleCover H m hm)
        (D.testBody m)}) :
    actualTubeFloor H (m + 1) <= MeasureTheory.volume
      ((effectiveStickyScaleCover H m hm).activeCoarseFamily k.1 : Set Space) := by
  change ((H.effectiveRadius (m + 1) : ENNReal) ^ 2 / 2) <=
    MeasureTheory.volume
      ((H.effectiveFamily (m + 1)).tubes k.1.1).carrier
  exact Tube.half_sq_le_volume_of_le_half
    ((H.effectiveFamily (m + 1)).tubes k.1.1) hradius

end BufferedTestBodyChain
end MultiscaleTubeHierarchy

#print axioms MultiscaleTubeHierarchy.BufferedTestBodyChain.toNormalizedScaleChain
#print axioms MultiscaleTubeHierarchy.BufferedTestBodyChain.global_le_endpointRatio
#print axioms MultiscaleTubeHierarchy.BufferedTestBodyChain.global_le_prod_local_of_endpointRatio_le_one
#print axioms MultiscaleTubeHierarchy.BufferedTestBodyChain.actualTubeFloor_le_capturedParentVolume

end
end FamilyStickyScaleChainBufferedTelescopeV1

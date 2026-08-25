import FamilyStickyGrounding.FamilyStickyScaleChainBufferedTelescopeV1

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFiniteDeltaMaxBridgeV1

open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyScaleChainNormalizedIntegrationV1
open FamilyStickyVolumeRatioTelescopingV1
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy

noncomputable section

/-!
# Sticky Kakeya: normalized chain to finite Delta-max chain

The dividing-scales adapter consumes `FiniteDeltaMaxChain`.  This module
turns an honest normalized scale chain into that exact API.  Its local value
is the actual geometric factor multiplied by the explicit adjacent
body-growth/tube-decay ratio; the fixed dimensional loss is one because all
losses have already been retained locally.

The product of these local values is proved equal to the product of actual
geometric factors times the endpoint ratio.  Thus an exponent budget is never
accepted as an opaque global upper bound.
-/

namespace NormalizedScaleChain

/-- The literal local factor seen by the scalar finite-chain API. -/
def finiteLocalFactor {depth : Nat} (C : NormalizedScaleChain depth)
    (m : Nat) : ENNReal :=
  C.localFactor m * C.volumeRatio m

/-- Forget only the separated normalization, retaining it inside each local
factor. -/
def toFiniteDeltaMaxChain {depth : Nat} (C : NormalizedScaleChain depth) :
    FiniteDeltaMaxChain depth where
  deltaMax := C.value
  localDeltaMax := finiteLocalFactor C
  dimensionalLoss := 1
  step_le := by
    intro m hm
    simpa only [finiteLocalFactor, one_mul] using C.step_le m hm
  top_le_one := C.top_le_one

/-- The finite-chain local product is exactly the geometric local product
times the telescoped endpoint normalization. -/
theorem prod_finiteLocalFactor_eq {depth : Nat}
    (C : NormalizedScaleChain depth) :
    (∏ m ∈ Finset.range depth, finiteLocalFactor C m) =
      (∏ m ∈ Finset.range depth, C.localFactor m) *
        ((C.bodyVolume depth / C.bodyVolume 0) *
          (C.tubeVolume 0 / C.tubeVolume depth)) := by
  calc
    (∏ m ∈ Finset.range depth, finiteLocalFactor C m) =
        (∏ m ∈ Finset.range depth, C.localFactor m) *
          (∏ m ∈ Finset.range depth, C.volumeRatio m) := by
      simp only [finiteLocalFactor]
      rw [Finset.prod_mul_distrib]
    _ = (∏ m ∈ Finset.range depth, C.localFactor m) *
        ((C.bodyVolume depth / C.bodyVolume 0) *
          (C.tubeVolume 0 / C.tubeVolume depth)) := by
      rw [show (∏ m ∈ Finset.range depth, C.volumeRatio m) =
          (C.bodyVolume depth / C.bodyVolume 0) *
            (C.tubeVolume 0 / C.tubeVolume depth) by
        exact prod_bodyGrowth_mul_tubeDecay depth C.bodyVolume C.tubeVolume
          C.bodyVolume_ne_zero C.bodyVolume_ne_top
          C.tubeVolume_ne_zero C.tubeVolume_ne_top]

/-- A source-shaped exponent budget on actual local factors and the endpoint
ratio produces the exact `productBudget` consumed by dividing scales. -/
theorem finite_productBudget_of_local_endpoint_le {depth : Nat}
    (C : NormalizedScaleChain depth) (target : ENNReal)
    (hbudget :
      (∏ m ∈ Finset.range depth, C.localFactor m) *
        ((C.bodyVolume depth / C.bodyVolume 0) *
          (C.tubeVolume 0 / C.tubeVolume depth)) <= target) :
    (toFiniteDeltaMaxChain C).dimensionalLoss ^ depth *
        (∏ m ∈ Finset.range depth,
          (toFiniteDeltaMaxChain C).localDeltaMax m) <= target := by
  simpa only [toFiniteDeltaMaxChain, one_pow, one_mul,
    prod_finiteLocalFactor_eq] using hbudget

end NormalizedScaleChain

namespace MultiscaleTubeHierarchy.BufferedTestBodyChain

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {card : Nat -> Nat}
  {H : Submission.Kakeya.ConvexFactoring.MultiscaleTubeHierarchy
    depth nominalRadius (fun l => Fin (card l))}

/-- The actual buffered test-body chain in the scalar form consumed by the
existing dividing-scales finite-chain adapter. -/
def toFiniteDeltaMaxChain (D : BufferedTestBodyChain H) :
    FiniteDeltaMaxChain depth :=
  NormalizedScaleChain.toFiniteDeltaMaxChain
    (BufferedTestBodyChain.toNormalizedScaleChain H D)

@[simp] theorem toFiniteDeltaMaxChain_deltaMax
    (D : BufferedTestBodyChain H) (m : Nat) :
    (toFiniteDeltaMaxChain D).deltaMax m =
      Submission.Kakeya.ConvexGeometry.concentration
        (effectiveActiveFamily H m) (D.testBody m) := by
  rfl

/-- The remaining exponent input is stated entirely in actual geometric
factors and the two endpoint volume ratios. -/
theorem productBudget_of_local_endpoint_le
    (D : BufferedTestBodyChain H) (target : ENNReal)
    (hbudget :
      (∏ m ∈ Finset.range depth,
        BufferedTestBodyChain.localFactor H D m) *
        ((MeasureTheory.volume (D.testBody depth : Set
            LeanEval.Analysis.WangZahlKakeya.Space) /
          MeasureTheory.volume (D.testBody 0 : Set
            LeanEval.Analysis.WangZahlKakeya.Space)) *
          (D.tubeVolume 0 / D.tubeVolume depth)) <= target) :
    (toFiniteDeltaMaxChain D).dimensionalLoss ^ depth *
        (∏ m ∈ Finset.range depth,
          (toFiniteDeltaMaxChain D).localDeltaMax m) <= target := by
  exact NormalizedScaleChain.finite_productBudget_of_local_endpoint_le
    (BufferedTestBodyChain.toNormalizedScaleChain H D) target hbudget

end MultiscaleTubeHierarchy.BufferedTestBodyChain

#print axioms NormalizedScaleChain.toFiniteDeltaMaxChain
#print axioms NormalizedScaleChain.prod_finiteLocalFactor_eq
#print axioms NormalizedScaleChain.finite_productBudget_of_local_endpoint_le
#print axioms MultiscaleTubeHierarchy.BufferedTestBodyChain.toFiniteDeltaMaxChain
#print axioms MultiscaleTubeHierarchy.BufferedTestBodyChain.productBudget_of_local_endpoint_le

end
end FamilyStickyScaleChainFiniteDeltaMaxBridgeV1

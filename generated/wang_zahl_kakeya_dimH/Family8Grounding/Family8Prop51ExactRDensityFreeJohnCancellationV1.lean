import Family8Grounding.Family8Prop51ExactRLocalKTResidualDichotomyV1
import Family8Grounding.Family8SelectedParentBlockDensityJohnHullCancellationV1
import Mathlib.Tactic

/-!
# Exact-R density-free cancellation through one literal John container

The high branch of the exact-`R` Proposition 5.1 residual contains

`A * volume ambient * (prop51SubselectedBodyVolume P R)⁻¹`.

If `q ∈ R`, the body of the literal block `q` is one summand of the exact
body-volume denominator.  Consequently a John bound for `ambient` by that
same block body cancels the inverse without any nonzero or finiteness
hypothesis on the sum.

This file is scalar only.  It does not assert that all fine bodies selected
by `R` lie in the John container, identify an exact assembly or shading, or
replace the input occurrence by another selected occurrence.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51ExactRDensityFreeJohnCancellationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8Prop51ExactRLocalKTResidualDichotomyV1
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
open Family8SelectedParentBlockDensityJohnHullCancellationV1
open Family8SelectedParentBucketContainerJacobianEnvelopeV3
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- Generic exact-`R` scalar cancellation.  Membership of the fixed block
`q` is the only relation required between `q` and `R`; the ambient-volume
estimate is deliberately supplied in its weakest one-sided form. -/
theorem prop51SubselectedFineDensityFreeScale_le_jacobian_mul_johnFactor
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (q : Fin (blocks F P).length) (hq : q ∈ R)
    (ambient : ConvexBody Space) (A J : ENNReal)
    (hambient :
      volume (ambient : Set Space) <=
        J * ((288 : ENNReal) ^ 3 *
          volume ((blockAt F P q).body : Set Space))) :
    prop51SubselectedFineDensityFreeScale A P R ambient <=
      A * J * (288 : ENNReal) ^ 3 := by
  have hbody :
      volume ((blockAt F P q).body : Set Space) <=
        prop51SubselectedBodyVolume P R := by
    unfold prop51SubselectedBodyVolume
    exact Finset.single_le_sum
      (f := fun k => volume ((blockAt F P k).body : Set Space))
      (fun _ _ => bot_le) hq
  have hratio :
      volume ((blockAt F P q).body : Set Space) *
          (prop51SubselectedBodyVolume P R)⁻¹ <= 1 := by
    calc
      volume ((blockAt F P q).body : Set Space) *
          (prop51SubselectedBodyVolume P R)⁻¹ <=
        prop51SubselectedBodyVolume P R *
          (prop51SubselectedBodyVolume P R)⁻¹ :=
            mul_le_mul' hbody le_rfl
      _ <= 1 := ENNReal.mul_inv_le_one _
  unfold prop51SubselectedFineDensityFreeScale
  calc
    A * volume (ambient : Set Space) *
        (prop51SubselectedBodyVolume P R)⁻¹ <=
      A * (J * ((288 : ENNReal) ^ 3 *
        volume ((blockAt F P q).body : Set Space))) *
          (prop51SubselectedBodyVolume P R)⁻¹ :=
            mul_le_mul' (mul_le_mul' le_rfl hambient) le_rfl
    _ = (A * J * (288 : ENNReal) ^ 3) *
        (volume ((blockAt F P q).body : Set Space) *
          (prop51SubselectedBodyVolume P R)⁻¹) := by
            ac_rfl
    _ <= (A * J * (288 : ENNReal) ^ 3) * 1 :=
      mul_le_mul' le_rfl hratio
    _ = A * J * (288 : ENNReal) ^ 3 := by simp

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Literal selected-parent specialization.  The partition, occurrence,
John frame, normalized container, and affine Jacobian are exactly those of
the existing one-block container theorem; no equality transport is used. -/
theorem selectedParent_prop51SubselectedFineDensityFreeScale_le
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (q : Fin (blocks S.activeCoarseFamily P).length) (hq : q ∈ R)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) (A : ENNReal) :
    prop51SubselectedFineDensityFreeScale A P R
        (selectedParentBucketNormalizedJohnContainer
          S hrho P q r label) <=
      A *
        affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P q) r hr)
            label) *
        (288 : ENNReal) ^ 3 := by
  apply prop51SubselectedFineDensityFreeScale_le_jacobian_mul_johnFactor
    P R q hq
  exact
    selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_mul_johnFactor_mul_hullVolume
      S hrho P q r hr label

#print axioms
  prop51SubselectedFineDensityFreeScale_le_jacobian_mul_johnFactor
#print axioms
  selectedParent_prop51SubselectedFineDensityFreeScale_le

end
end Family8Prop51ExactRDensityFreeJohnCancellationV1

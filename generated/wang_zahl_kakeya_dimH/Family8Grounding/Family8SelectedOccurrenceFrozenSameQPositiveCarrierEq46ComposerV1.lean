import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1
import Family8Grounding.Family8SelectedParentExactAssemblyCordobaExpandedV5
import Family8Grounding.Family8SelectedParentPlankFreshFullFiberCountV1
import Mathlib.Tactic

/-!
# The one selected positive-carrier label closes Equation (46)

The same-`q` positive-carrier payment has already selected one actual side
label.  This file consumes the Córdoba estimate and the carrier-floor
cancellation for precisely that label.  It does not ask for Equation (46) on
all occupied labels.

The remaining Equation (46) premise is division-free.  Its left side is the
fully expanded thresholded Córdoba numerator after the quantitative carrier
floor has been cancelled.  The right side keeps the positive finite source
factor, so that factor can be cancelled only after the two estimates have
been composed.  No factor `R.card` occurs.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentExactAssemblyCordobaExpandedV5
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFreshFullFiberCountV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The positive source factor which occurs in both the paid Córdoba bound
and the selected-label Equation (46) budget. -/
noncomputable def selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (source : Shading S.activeCoarseFamily)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) : ENNReal :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
  affineJacobian (bucketNormalizedAffineEquiv e label) *
    (source.shadingDensity * ((rho : ENNReal) ^ 2 / 2))

/-- After expanding the dyadic certificate and cancelling the quantitative
carrier floor, this is the exact numerator left by the same-`q` payment.
It contains neither a global selected-occurrence count nor `R.card`. -/
noncomputable def
    selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
    (S : StickyScaleCover fine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (label : Fin 3 -> Int) (KT : ENNReal) : ENNReal :=
  ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
      (2 *
        ((certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : Nat) : ENNReal))) *
    (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
      (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
        ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3))))

/-- The only remaining Equation (46) input for one already selected label.
The source factor is deliberately retained on the right until the preceding
Córdoba and carrier-floor bounds have been multiplied together. -/
def SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (source : Shading S.activeCoarseFamily)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) (KT : ENNReal)
    (innerLoss : ENNReal) (tubesPerPlank : Nat)
    (epsilon beta : Real) : Prop :=
  selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
      S P r label KT <=
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
        S hrho P q source r hr label *
      (innerLoss * proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        tubesPerPlank epsilon beta)

/-- Nonzero source mass makes the literal source factor cancellable. -/
theorem selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_zero
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (source : Shading S.activeCoarseFamily)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hsource : source.shadingMass ≠ 0) :
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
        S hrho P q source r hr label ≠ 0 := by
  have hdensity0 : source.shadingDensity ≠ 0 := by
    unfold Shading.shadingDensity
    exact ENNReal.div_ne_zero.mpr
      ⟨hsource, familyVolume_ne_top S.activeCoarseFamily⟩
  have harea0 : ((rho : ENNReal) ^ 2 / 2) ≠ 0 := by
    exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.pow_ne_zero (ENNReal.coe_ne_zero.mpr hrho.ne') 2,
        by norm_num⟩
  unfold selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
  exact mul_ne_zero
    (affineJacobian_pos
      (bucketNormalizedAffineEquiv
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P q) r hr)
        label)).ne'
    (mul_ne_zero hdensity0 harea0)

/-- The same literal source factor is finite.  Nonzero source mass rules out
a zero family-volume denominator in `shadingDensity`. -/
theorem selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_top
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (source : Shading S.activeCoarseFamily)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hsource : source.shadingMass ≠ 0) :
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
        S hrho P q source r hr label ≠ ∞ := by
  have hfamily0 : familyVolume S.activeCoarseFamily ≠ 0 := by
    intro hzero
    apply hsource
    exact nonpos_iff_eq_zero.mp
      (source.shadingMass_le_familyVolume.trans_eq hzero)
  have hdensityTop : source.shadingDensity ≠ ∞ := by
    unfold Shading.shadingDensity
    exact ENNReal.div_ne_top source.shadingMass_lt_top.ne hfamily0
  have hareaTop : ((rho : ENNReal) ^ 2 / 2) ≠ ∞ := by
    exact ENNReal.div_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
  unfold selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
  exact ENNReal.mul_ne_top
    (affineJacobian_ne_top
      (bucketNormalizedAffineEquiv
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P q) r hr)
        label))
    (ENNReal.mul_ne_top hdensityTop hareaTop)

/-- Equation (46)'s inner factor is monotone in the local fibre count, so a
budget at an honest smaller count can be weakened to an actual block count.
-/
theorem SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget.mono_count
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (source : Shading S.activeCoarseFamily)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) (KT : ENNReal)
    (innerLoss : ENNReal) {m n : Nat} (epsilon beta : Real)
    (hbetaTwo : beta <= 2) (hmn : m <= n)
    (hbudget : SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
      S hrho P q source r hr label KT innerLoss m epsilon beta) :
    SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
      S hrho P q source r hr label KT innerLoss n epsilon beta := by
  unfold SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget at hbudget ⊢
  exact hbudget.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl
    (proposition66AInnerFactor_mono_tubesPerPlank hbetaTwo hmn)))

/-- A convenient specialization of `mono_count`: the selected side bucket
is a literal subset of the same greedy block.  This is the count needed by
the outer-product composer and introduces no global cardinal envelope. -/
theorem
    SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget.selectedBucket_to_block
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (source : Shading S.activeCoarseFamily)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) (KT : ENNReal)
    (innerLoss : ENNReal) (epsilon beta : Real) (hbetaTwo : beta <= 2)
    (hbudget : SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
      S hrho P q source r hr label KT innerLoss
        (selectedParentPlankBucketIndices
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P q) r hr)
          S (blockAt S.activeCoarseFamily P q).fiber hrho label).card
        epsilon beta) :
    SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
      S hrho P q source r hr label KT innerLoss
        (blockAt S.activeCoarseFamily P q).fiber.card epsilon beta := by
  apply SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget.mono_count
    S hrho P q source r hr label KT innerLoss epsilon beta hbetaTwo _ hbudget
  calc
    (selectedParentPlankBucketIndices
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P q) r hr)
        S (blockAt S.activeCoarseFamily P q).fiber hrho label).card <=
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P q).fiber}).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = (blockAt S.activeCoarseFamily P q).fiber.card := by
      rw [Finset.card_univ, Fintype.card_coe]

/-- Fixed selected-label Equation (46) composer.

The hypotheses `hcordoba` and `hcancel` are exactly the final two scalar
fields attached to the label returned by
`exists_selectedOccurrence_exactOuter_survivingDense_sameQ_positiveCarrierPayment`.
Only the Equation (46) budget for that one label is consumed. -/
theorem selectedOccurrenceFrozenSameQPositiveCarrier_finalFiberAverage_le_inner
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily) {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) source rFrozen)
    (q : Fin (blocks S.activeCoarseFamily P).length) (hq : q ∈ R)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hplank : forall p,
      p ∈ sideShapeBucket Finset.univ
          (fun p => selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P q) r hr)
            S (blockAt S.activeCoarseFamily P q).fiber hrho p)
          label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P q) r hr)
              label)
            S (blockAt S.activeCoarseFamily P q).fiber p))
    (KT : ENNReal)
    (hcordoba :
      let B := (blockAt S.activeCoarseFamily P q).fiber
      let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
      let Yraw := selectedParentArbitraryPlankBucketShading
        e S B hrho label Z
      let Yclean := positiveCarrierShading Yraw
      let hplankPos : forall t,
          IsPlank 576 (bucketShortA label) (bucketShortB label)
            (quantitativePositiveCarrierFamily Yclean t) := fun t =>
        selectedParentPlankBucket_isPlank
          e S B hrho label hplank t.1.1
      let cert := chosenPlankCertificate hplankPos
      Z.averageMultiplicity <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert) KT
              (certifiedPlankThresholdedAngleScaleCap 576 *
                (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                    ENNReal) ^ 3) /
                  quantitativeCarrierFloor Yclean))))
    (hcancel :
      let B := (blockAt S.activeCoarseFamily P q).fiber
      let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
      let Yraw := selectedParentArbitraryPlankBucketShading
        e S B hrho label Z
      let Yclean := positiveCarrierShading Yraw
      (affineJacobian (bucketNormalizedAffineEquiv e label) *
          (source.shadingDensity * ((rho : ENNReal) ^ 2 / 2))) *
          (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                ENNReal) ^ 3) /
              quantitativeCarrierFloor Yclean))) <=
        selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
          (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
            ((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
              ENNReal) ^ 3))))
    (hsource : source.shadingMass ≠ 0)
    (innerLoss : ENNReal) (tubesPerPlank : Nat) (epsilon beta : Real)
    (hEq46 : SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
      S hrho P q source r hr label KT innerLoss tubesPerPlank
        epsilon beta) :
    (finalFiberShading A (some q)).averageMultiplicity <=
      innerLoss * proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        tubesPerPlank epsilon beta := by
  let B := (blockAt S.activeCoarseFamily P q).fiber
  let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
  let Yraw := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let Yclean := positiveCarrierShading Yraw
  let hplankPos : forall t,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Yclean t) := fun t =>
    selectedParentPlankBucket_isPlank
      e S B hrho label hplank t.1.1
  let cert := chosenPlankCertificate hplankPos
  let floorScale : ENNReal :=
    certifiedPlankThresholdedAngleScaleCap 576 *
      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
        quantitativeCarrierFloor Yclean)
  let numeratorScale : ENNReal :=
    certifiedPlankThresholdedAngleScaleCap 576 *
      ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3)
  let bucketCoefficient : ENNReal :=
    (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
      (2 *
        ((certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : Nat) : ENNReal))
  let sourceFactor : ENNReal :=
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
      S hrho P q source r hr label
  let target : ENNReal :=
    innerLoss * proposition66AInnerFactor rho
      (bucketShortA label) (bucketShortB label)
      tubesPerPlank epsilon beta
  have hcordoba' : Z.averageMultiplicity <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (2 * certifiedPlankDyadicFactor
          (certifiedPlankThresholdedLevels cert) KT floorScale) := by
    simpa only [B, Z, e, Yraw, Yclean, hplankPos, cert, floorScale] using
      hcordoba
  have hexpand :
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert) KT floorScale) <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (2 *
            (((certifiedPlankThresholdedAngleBucketLoss
                (bucketShortA label) (bucketShortB label) : Nat) :
                ENNReal) * KT * floorScale)) :=
    loss_mul_two_mul_certifiedPlankDyadicFactor_le_explicit
      cert (selectedParentLogarithmicSideBucketLoss rho : ENNReal)
        KT floorScale
  have hZexpanded : Z.averageMultiplicity <=
      bucketCoefficient * (KT * floorScale) := by
    calc
      Z.averageMultiplicity <=
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (2 *
              (((certifiedPlankThresholdedAngleBucketLoss
                  (bucketShortA label) (bucketShortB label) : Nat) :
                  ENNReal) * KT * floorScale)) := hcordoba'.trans hexpand
      _ = bucketCoefficient * (KT * floorScale) := by
        dsimp only [bucketCoefficient]
        ac_rfl
  have hcancel' : sourceFactor * (KT * floorScale) <=
      selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
        (KT * numeratorScale) := by
    simpa only [sourceFactor,
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor,
      B, Z, e, Yraw, Yclean, floorScale, numeratorScale] using hcancel
  have hEq46' :
      bucketCoefficient *
          (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
            (KT * numeratorScale)) <=
        sourceFactor * target := by
    simpa only [SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget,
      selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS,
      sourceFactor, target, bucketCoefficient, numeratorScale] using hEq46
  have hscaled : sourceFactor * Z.averageMultiplicity <=
      sourceFactor * target := by
    calc
      sourceFactor * Z.averageMultiplicity <=
          sourceFactor * (bucketCoefficient * (KT * floorScale)) :=
        mul_le_mul' le_rfl hZexpanded
      _ = bucketCoefficient * (sourceFactor * (KT * floorScale)) := by
        ac_rfl
      _ <= bucketCoefficient *
          (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
            (KT * numeratorScale)) := mul_le_mul' le_rfl hcancel'
      _ <= sourceFactor * target := hEq46'
  have hsourceFactor0 : sourceFactor ≠ 0 := by
    dsimp only [sourceFactor]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_zero
      S hrho P q source r hr label hsource
  have hsourceFactorTop : sourceFactor ≠ ∞ := by
    dsimp only [sourceFactor]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_top
      S hrho P q source r hr label hsource
  have hinner : Z.averageMultiplicity <= target := by
    apply (ENNReal.mul_le_mul_iff_right
      hsourceFactor0 hsourceFactorTop).mp
    exact hscaled
  calc
    (finalFiberShading A (some q)).averageMultiplicity =
        Z.averageMultiplicity := by
      symm
      simpa only [Z] using
        (selectedOccurrenceFrozenFinalFiberBlockShading_averageMultiplicity_eq
          P R A q hq)
    _ <= target := hinner
    _ = innerLoss * proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        tubesPerPlank epsilon beta := rfl

#print axioms selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
#print axioms
  selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
#print axioms SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
#print axioms
  selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_zero
#print axioms
  selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_top
#print axioms
  SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget.mono_count
#print axioms
  SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget.selectedBucket_to_block
#print axioms
  selectedOccurrenceFrozenSameQPositiveCarrier_finalFiberAverage_le_inner

end
end Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1

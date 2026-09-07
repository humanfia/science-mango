import Family8Grounding.Family8EndpointIdentityExactSameCoreHighPayloadJointBucketAdapterV1
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Family8Grounding.Family8PositiveCarrierShadingRestrictionV5
import Family8Grounding.Family8SelectedOccurrenceLargeBLemma69Eq32ComposerV1
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV1
import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterDensityBandKatzTaoV1
import Family8Grounding.Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
import Mathlib.Tactic

/-!
# Winner-side joint-bucket consumer for the large-`b` Lemma 6.9 branch

The endpoint joint bucket returns a frozen-comparable assembly and one
selected occurrence.  Consequently its shortest honest large-`b` consumer is
the frozen same-`q` route, not the older `ExactAssembly` composer (which asks
for a different assembly and an inner estimate on every coarse occurrence).

This file keeps the winner-side `Rside`, the frozen assembly, the occurrence
`q`, and its occupied inner label unchanged.  The common normalized outer
plank certificate and Katz--Tao estimate are automatic.  Zero-volume outer
carriers are removed before the thresholded plank estimate, so the finite
positive carrier floor is automatic as well and average multiplicity is
unchanged.  The local payment supplies the product, plank, Cordoba, carrier
cancellation, and count data.

Only three selected-witness scalar comparisons remain: the literal Lemma 6.9
payment, its comparison with the outer Proposition 6.6(A) factor, and the
one-label Equation (46) budget.  They occur after the existentially selected
assembly, occurrence, and inner label; no universal callback over possible
winners is required.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8WinnerSideJointBucketLargeBLemma69ConsumerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8GreedyWinnerNormalizedPlankBucketV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8PositiveCarrierShadingRestrictionV5
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66InnerScaleMismatchAbsorptionV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceArbitraryROuterAverageBridgeV1
open Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
open Family8SelectedOccurrenceLargeBLemma69Eq32ComposerV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1
open Family8SelectedOccurrenceNormalizedOuterDensityBandKatzTaoV1
open Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
open Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {rho : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily rho iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- The automatic common container for the normalized outer winner bodies. -/
noncomputable def normalizedOuterUnitContainer
    (labelOuter : Fin 3 -> Int) : ConvexBody Space :=
  affineImageConvexBody
    (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) unitBallBody

/-- Unit-ball support of the active fine family gives a common container for
the exact normalized outer family. -/
theorem selectedOccurrenceNormalizedOuterFamily_subset_unitContainer
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hfineContained : forall i, i ∈ active ->
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (q : {q // q ∈ selectedOccurrenceIndices P Rside}) :
    (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside q :
        Set Space) ⊆ (normalizedOuterUnitContainer labelOuter : Set Space) := by
  let k := selectedOccurrenceNormalizedOuterPosition P Rside q
  have hk : k ∈ Rside :=
    selectedOccurrenceNormalizedOuterPosition_mem P Rside q
  rw [selectedOccurrenceNormalizedOuterFamily_apply]
  unfold normalizedWinnerBody normalizedOuterUnitContainer
  simp only [coe_affineImageConvexBody]
  exact Set.image_mono (winnerBody_subset_unitBall P hfineContained k)

/-- Lemma 6.9 on the exact normalized selected outer shading with its carrier
floor constructed internally.  Passing to the positive-carrier subtype loses
neither shading mass nor average multiplicity. -/
theorem selectedOccurrenceNormalizedOuter_averageMultiplicity_le_lemma69Power_automaticFloor
    (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide P hrho k) = labelOuter)
    (K : ConvexBody Space)
    (hcontains : forall q,
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside q :
          Set Space) ⊆ (K : Set Space))
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside))
    (eta : Real)
    (hlemma69Scalar :
      (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA labelOuter) (bucketShortB labelOuter) : ENNReal) *
          KT *
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (volume (K : Set Space) /
              automaticPositiveCarrierVolumeFloor
                (selectedOccurrenceNormalizedOuterShading
                  P Y labelOuter Rside))) <=
        (bucketShortA labelOuter : ENNReal) ^ (-8 * eta)) :
    (selectedOccurrenceNormalizedOuterShading
        P Y labelOuter Rside).averageMultiplicity <=
      (bucketShortA labelOuter : ENNReal) ^ (-8 * eta) := by
  let Youter := selectedOccurrenceNormalizedOuterShading
    P Y labelOuter Rside
  let Ypos := positiveCarrierShading Youter
  let floor := automaticPositiveCarrierVolumeFloor Youter
  let hplank : forall q,
      IsPlank 576 (bucketShortA labelOuter) (bucketShortB labelOuter)
        (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside q) :=
    selectedOccurrenceNormalizedOuterFamily_all_isPlank
      P hrho labelOuter Rside hlabel
  let hplankPos : forall q,
      IsPlank 576 (bucketShortA labelOuter) (bucketShortB labelOuter)
        (positiveCarrierFamily Youter q) := fun q => hplank q.1
  let cert := chosenPlankCertificate hplankPos
  let rowScale : ENNReal :=
    certifiedPlankThresholdedAngleScaleCap 576 *
      (volume (K : Set Space) / floor)
  have hcontainsPos : forall q,
      (positiveCarrierFamily Youter q : Set Space) ⊆ (K : Set Space) :=
    fun q => hcontains q.1
  have hKTpos : IsKatzTao KT (positiveCarrierFamily Youter) := by
    exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
      (hKT.on (positiveCarrierIndices Youter))
  have hcordoba : Ypos.averageMultiplicity <=
      certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) KT rowScale := by
    exact certifiedPlankThresholded_averageMultiplicity_le_globalContainer
      cert Ypos K hcontainsPos floor
        (automaticPositiveCarrierVolumeFloor_ne_zero Youter)
        (automaticPositiveCarrierVolumeFloor_ne_top Youter)
        (automaticPositiveCarrierVolumeFloor_le Youter) KT hKTpos
  have hexplicit :
      certifiedPlankDyadicFactor
          (certifiedPlankThresholdedLevels cert) KT rowScale <=
        (certifiedPlankThresholdedAngleBucketLoss
            (bucketShortA labelOuter) (bucketShortB labelOuter) : ENNReal) *
          KT * rowScale :=
    certifiedPlankDyadicFactor_thresholded_le_explicit cert KT rowScale
  calc
    (selectedOccurrenceNormalizedOuterShading
        P Y labelOuter Rside).averageMultiplicity =
        Ypos.averageMultiplicity := by
      simpa only [Youter] using
        (positiveCarrierShading_averageMultiplicity Youter).symm
    _ <= certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) KT rowScale := hcordoba
    _ <= (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA labelOuter) (bucketShortB labelOuter) : ENNReal) *
        KT * rowScale := hexplicit
    _ <= (bucketShortA labelOuter : ENNReal) ^ (-8 * eta) := by
      simpa only [rowScale, floor, Youter] using hlemma69Scalar

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {sourceFine : UniformTubeFamily delta index}

/-- The literal thresholded Lemma 6.9 scalar after the normalized outer
carrier floor and joint-band Katz--Tao constant have been constructed. -/
def SelectedNormalizedOuterLemma69ScalarBudget
    (labelOuter : Fin 3 -> Int) (outerKT carrierFloor : ENNReal)
    (eta : Real) : Prop :=
  let K := normalizedOuterUnitContainer labelOuter
  (certifiedPlankThresholdedAngleBucketLoss
      (bucketShortA labelOuter) (bucketShortB labelOuter) : ENNReal) *
        outerKT *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (volume (K : Set Space) /
            carrierFloor)) <=
      (bucketShortA labelOuter : ENNReal) ^ (-8 * eta)

/-- The remaining comparison from the literal Lemma 6.9 power to the outer
Proposition 6.6(A) factor. -/
def SelectedNormalizedOuterLargeBPaymentBudget
    (rho : NNReal) (labelOuter : Fin 3 -> Int)
    (plankCount : Nat) (outerKT : ENNReal)
    (eta : Real) (outerLoss : ENNReal) (epsilon beta : Real) : Prop :=
  (bucketShortA labelOuter : ENNReal) ^ (-8 * eta) <=
    outerLoss * proposition66AOuterFactor rho
      (bucketShortA labelOuter) (bucketShortB labelOuter)
      plankCount outerKT epsilon beta

/-- The three genuinely scalar payments at the already selected winner-side
outer label, frozen assembly, occurrence, and inner label. -/
def SelectedWinnerSideLargeBLemma69ScalarBudget
    (D : ActualTubeDatum delta index) (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (labelOuter labelInner : Fin 3 -> Int)
    (outerKT carrierFloor : ENNReal)
    (r : NNReal) (hr : 0 < r)
    (eta : Real) (outerLoss innerLoss : ENNReal)
    (epsilon beta : Real) : Prop :=
  let d := blockDensity S.activeCoarseFamily
    (blockAt S.activeCoarseFamily P q)
  SelectedNormalizedOuterLemma69ScalarBudget
      labelOuter outerKT carrierFloor eta /\
  SelectedNormalizedOuterLargeBPaymentBudget
      rho labelOuter Rside.card outerKT eta outerLoss epsilon beta /\
  SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
    S hrho P q source r hr labelInner d innerLoss
      (blockAt S.activeCoarseFamily P q).fiber.card epsilon beta

/-- Exactly the assembly, occurrence, and occupied inner label selected by
the local winner-side payment.  The bulky plank/Cordoba/carrier fields are
mechanically compressed to the one same-`q` cross inequality used below. -/
structure WinnerSideLargeBLemma69PaymentWitness
    (S : StickyScaleCover sourceFine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (rFrozen : Real) (r : NNReal) (hr : 0 < r) where
  assembly : Family8FrozenNeighborhoodAssemblyV1.Assembly
    (selectedOccurrenceFactorization P Rside) source rFrozen
  assembly_loss : assembly.loss =
    frozenComparableLoss (ActiveParentIndex S)
      (Option (Fin (blocks S.activeCoarseFamily P).length))
  frozen_eq : assembly.frozenCoarse =
    (selectedOccurrenceFactorization P Rside).inducedShading
      assembly.refinement.shading
  occurrence : Fin (blocks S.activeCoarseFamily P).length
  occurrence_mem : occurrence ∈ Rside
  count_active :
    Rside.card * (blockAt S.activeCoarseFamily P occurrence).fiber.card <=
      2 * Fintype.card (ActiveParentIndex S)
  actual_le_four_mul :
    (actualRefinementShading assembly).averageMultiplicity <=
      4 * (assembly.frozenCoarse.averageMultiplicity *
        (finalFiberShading assembly (some occurrence)).averageMultiplicity)
  innerLabel : Fin 3 -> Int
  innerLabel_occupied : innerLabel ∈ occupiedWeightBuckets
    (Finset.univ : Finset
      {p // p ∈ (blockAt S.activeCoarseFamily P occurrence).fiber})
    (fun p => sideShapeLabel
      (selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P occurrence) r hr)
        S (blockAt S.activeCoarseFamily P occurrence).fiber hrho p))
  inner_cross :
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
        S hrho P occurrence source r hr innerLabel *
      (finalFiberShading assembly (some occurrence)).averageMultiplicity <=
    selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS S P r
      innerLabel (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P occurrence))

/-- Extract the exact chosen witness from `hlocal`; all discarded payload
fields are used only to derive `inner_cross`. -/
theorem exists_winnerSideLargeBLemma69PaymentWitness_of_localPayment
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (hlocal : WinnerSideLocalBlockPositiveCarrierPaymentPayload
      D S P Rside source rFrozen hrho r hr) :
    exists _W : WinnerSideLargeBLemma69PaymentWitness
      S hrho P Rside source rFrozen r hr, True := by
  classical
  unfold WinnerSideLocalBlockPositiveCarrierPaymentPayload at hlocal
  obtain ⟨A, hAloss, hAfrozen, q, hq, hcount, _hpositive,
      hproduct, labelInner, hoccupied, _ha, _hab, _hb, hplank,
      hcordoba, _hfloor, hcancel⟩ := hlocal
  have hcross :=
    selectedOccurrenceFrozenSameQPositiveCarrier_sourceFactor_mul_finalFiberAverage_le_expandedEq46LHS
      S hrho P Rside source A q hq r hr labelInner hplank
        (blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P q)) hcordoba hcancel
  exact ⟨{
    assembly := A
    assembly_loss := hAloss
    frozen_eq := hAfrozen
    occurrence := q
    occurrence_mem := hq
    count_active := hcount
    actual_le_four_mul := hproduct
    innerLabel := labelInner
    innerLabel_occupied := hoccupied
    inner_cross := hcross }, trivial⟩

/-- The carrier floor used by the fixed-witness large-`b` argument.  It is
defined from the exact outer shading attached to `W.assembly`; callers never
choose it. -/
noncomputable def winnerSideLargeBLemma69CarrierFloor
    (P : GreedyDensityPartition fine.bodyFamily
      (hullCandidates active) (hullContainer fine.bodyFamily) active)
    (Y : Shading fine.bodyFamily)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    : ENNReal :=
  automaticPositiveCarrierVolumeFloor
    (selectedOccurrenceNormalizedOuterShading
      P Y labelOuter Rside)

/-- The selected inner Equation-(46) budget cancels the finite nonzero source
factor already present in `W.inner_cross`. -/
theorem winnerSideLargeBLemma69_inner_at
    (S : StickyScaleCover sourceFine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (hsource : source.shadingMass ≠ 0)
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (W : WinnerSideLargeBLemma69PaymentWitness
      S hrho P Rside source rFrozen r hr)
    (innerLoss : ENNReal) (epsilon beta : Real)
    (hEq46 : SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
      S hrho P W.occurrence source r hr W.innerLabel
        (blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P W.occurrence))
        innerLoss (blockAt S.activeCoarseFamily P W.occurrence).fiber.card
        epsilon beta) :
    (finalFiberShading W.assembly (some W.occurrence)).averageMultiplicity <=
      innerLoss * proposition66AInnerFactor rho
        (bucketShortA W.innerLabel) (bucketShortB W.innerLabel)
        (blockAt S.activeCoarseFamily P W.occurrence).fiber.card
        epsilon beta := by
  let sourceFactor :=
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
      S hrho P W.occurrence source r hr W.innerLabel
  let innerTarget := innerLoss * proposition66AInnerFactor rho
    (bucketShortA W.innerLabel) (bucketShortB W.innerLabel)
    (blockAt S.activeCoarseFamily P W.occurrence).fiber.card epsilon beta
  have hscaled : sourceFactor *
        (finalFiberShading W.assembly
          (some W.occurrence)).averageMultiplicity <=
      sourceFactor * innerTarget := by
    exact W.inner_cross.trans (by
      simpa only [SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget,
        sourceFactor, innerTarget] using hEq46)
  have hsourceFactor0 : sourceFactor ≠ 0 := by
    dsimp only [sourceFactor]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_zero
      S hrho P W.occurrence source r hr W.innerLabel hsource
  have hsourceFactorTop : sourceFactor ≠ ∞ := by
    dsimp only [sourceFactor]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_top
      S hrho P W.occurrence source r hr W.innerLabel hsource
  exact (ENNReal.mul_le_mul_iff_right
    hsourceFactor0 hsourceFactorTop).mp hscaled

/-- The normalized outer plank, unit container, carrier floor, and Katz--Tao
certificate are geometric data at the fixed shading.  This helper consumes
only the thresholded Lemma 6.9 scalar; container construction stays outside
as an automatic structural certificate. -/
theorem winnerSideLargeBLemma69_normalizedOuterPower_at
    (hrho : 0 < rho)
    (P : GreedyDensityPartition fine.bodyFamily
      (hullCandidates active) (hullContainer fine.bodyFamily) active)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (Y : Shading fine.bodyFamily)
    (labelOuter : Fin 3 -> Int)
    (hlabelOuter : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide P hrho k) = labelOuter)
    (hcontains : forall z,
      (selectedOccurrenceNormalizedOuterFamily
          P labelOuter Rside z : Set Space) ⊆
        (normalizedOuterUnitContainer labelOuter : Set Space))
    (outerKT : ENNReal)
    (houterKT : IsKatzTao outerKT
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside))
    (eta : Real)
    (hlemma69Scalar : SelectedNormalizedOuterLemma69ScalarBudget
      labelOuter outerKT
        (winnerSideLargeBLemma69CarrierFloor P Y labelOuter Rside) eta) :
    (selectedOccurrenceNormalizedOuterShading
      P Y labelOuter Rside).averageMultiplicity <=
      (bucketShortA labelOuter : ENNReal) ^ (-8 * eta) := by
  let K := normalizedOuterUnitContainer labelOuter
  let carrierFloor := winnerSideLargeBLemma69CarrierFloor
    P Y labelOuter Rside
  have hscalar :
      (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA labelOuter) (bucketShortB labelOuter) : ENNReal) *
          outerKT *
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (volume (K : Set Space) / carrierFloor)) <=
        (bucketShortA labelOuter : ENNReal) ^ (-8 * eta) := by
    simpa only [SelectedNormalizedOuterLemma69ScalarBudget,
      K, carrierFloor] using hlemma69Scalar
  simpa only [K, carrierFloor, winnerSideLargeBLemma69CarrierFloor] using
    selectedOccurrenceNormalizedOuter_averageMultiplicity_le_lemma69Power_automaticFloor
      P Y hrho labelOuter Rside hlabelOuter K (by
        simpa only [K] using hcontains) outerKT houterKT eta hscalar

/-- Exact transport from the frozen coarse shading of `W` to its normalized
selected outer shading.  This is independent of every scalar budget. -/
theorem winnerSideLargeBLemma69_outerTransport_at
    (P : GreedyDensityPartition fine.bodyFamily
      (hullCandidates active) (hullContainer fine.bodyFamily) active)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (source : Shading fine.bodyFamily) (rFrozen : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P Rside) source rFrozen)
    (hAfrozen : A.frozenCoarse =
      (selectedOccurrenceFactorization P Rside).inducedShading
        A.refinement.shading)
    (labelOuter : Fin 3 -> Int) :
    A.frozenCoarse.averageMultiplicity =
      (selectedOccurrenceNormalizedOuterShading
        P A.refinement.shading labelOuter Rside).averageMultiplicity := by
  rw [hAfrozen]
  calc
    ((selectedOccurrenceFactorization P Rside).inducedShading
        A.refinement.shading).averageMultiplicity =
        (selectedOccurrenceOuterShading
          P A.refinement.shading Rside).averageMultiplicity :=
      selectedOccurrenceFactorization_inducedShading_averageMultiplicity_eq_outer
        P A.refinement.shading Rside
    _ = (selectedOccurrenceNormalizedOuterShading
          P A.refinement.shading labelOuter Rside).averageMultiplicity :=
      (selectedOccurrenceNormalizedOuterShading_averageMultiplicity
        P A.refinement.shading labelOuter Rside).symm

/-- Pure scalar payment from the literal Lemma 6.9 power to the chosen outer
Proposition 6.6(A) factor. -/
theorem lemma69Power_le_paidOuterFactor
    (rho : NNReal) (labelOuter : Fin 3 -> Int)
    (plankCount : Nat) (outerKT x outerLoss : ENNReal)
    (eta epsilon beta : Real)
    (hx : x <= (bucketShortA labelOuter : ENNReal) ^ (-8 * eta))
    (hpayment : SelectedNormalizedOuterLargeBPaymentBudget
      rho labelOuter plankCount outerKT eta outerLoss epsilon beta) :
    x <= outerLoss * proposition66AOuterFactor rho
      (bucketShortA labelOuter) (bucketShortB labelOuter)
      plankCount outerKT epsilon beta := by
  exact hx.trans hpayment

/-- Pure two-label Proposition 6.6 algebra.  The outer and inner labels remain
independent, so their exact mismatch loss is retained. -/
theorem paidOuter_mul_paidInner_le_mismatchFrostman
    (rho : NNReal) (hrho : 0 < rho)
    (labelOuter labelInner : Fin 3 -> Int)
    (plankCount tubesPerPlank : Nat)
    (outerKT outerLoss innerLoss actual outerAverage innerAverage : ENNReal)
    (epsilon beta : Real) (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hproduct : actual <= 4 * (outerAverage * innerAverage))
    (houter : outerAverage <=
      outerLoss * proposition66AOuterFactor rho
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        plankCount outerKT epsilon beta)
    (hinner : innerAverage <=
      innerLoss * proposition66AInnerFactor rho
        (bucketShortA labelInner) (bucketShortB labelInner)
        tubesPerPlank epsilon beta) :
    actual <=
      (4 * outerLoss * innerLoss *
        prop66InnerScaleMismatchLoss
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          (bucketShortA labelInner) (bucketShortB labelInner) beta) *
        proposition66AFrostmanFactor rho
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          (plankCount * tubesPerPlank) outerKT epsilon beta := by
  have hfactor :=
    proposition66AOuterFactor_mul_innerFactor_eq_innerScaleMismatch_mul_frostmanFactor
      (delta := rho)
      (outerA := bucketShortA labelOuter)
      (outerB := bucketShortB labelOuter)
      (innerA := bucketShortA labelInner)
      (innerB := bucketShortB labelInner)
      (plankCount := plankCount)
      (tubesPerPlank := tubesPerPlank)
      (totalCount := plankCount * tubesPerPlank)
      (CF := outerKT) (epsilon := epsilon) (beta := beta)
      hrho (bucketShortA_pos labelOuter)
        ((bucketShortA_pos labelOuter).trans_le
          (bucketShortA_le_bucketShortB labelOuter))
        (bucketShortA_pos labelInner)
        ((bucketShortA_pos labelInner).trans_le
          (bucketShortA_le_bucketShortB labelInner))
        hbeta hbetaOne rfl
  calc
    actual <= 4 * (outerAverage * innerAverage) := hproduct
    _ <= 4 *
        ((outerLoss * proposition66AOuterFactor rho
            (bucketShortA labelOuter) (bucketShortB labelOuter)
            plankCount outerKT epsilon beta) *
          (innerLoss * proposition66AInnerFactor rho
            (bucketShortA labelInner) (bucketShortB labelInner)
            tubesPerPlank epsilon beta)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' houter hinner)
    _ = (4 * outerLoss * innerLoss) *
        (proposition66AOuterFactor rho
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          plankCount outerKT epsilon beta *
        proposition66AInnerFactor rho
          (bucketShortA labelInner) (bucketShortB labelInner)
          tubesPerPlank epsilon beta) := by
      ac_rfl
    _ = (4 * outerLoss * innerLoss) *
        (prop66InnerScaleMismatchLoss
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          (bucketShortA labelInner) (bucketShortB labelInner) beta *
        proposition66AFrostmanFactor rho
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          (plankCount * tubesPerPlank) outerKT epsilon beta) := by
      rw [hfactor]
    _ = (4 * outerLoss * innerLoss *
          prop66InnerScaleMismatchLoss
            (bucketShortA labelOuter) (bucketShortB labelOuter)
            (bucketShortA labelInner) (bucketShortB labelInner) beta) *
        proposition66AFrostmanFactor rho
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          (plankCount * tubesPerPlank) outerKT epsilon beta := by
      ac_rfl

/-- The three and only three scalar comparisons at one already selected
payment witness.  This is a structure, not a callback over possible winners. -/
structure WinnerSideLargeBLemma69ScalarBudgetAt
    (S : StickyScaleCover sourceFine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (labelOuter labelInner : Fin 3 -> Int)
    (outerKT carrierFloor : ENNReal)
    (r : NNReal) (hr : 0 < r)
    (eta : Real) (outerLoss innerLoss : ENNReal)
    (epsilon beta : Real) : Prop where
  lemma69 : SelectedNormalizedOuterLemma69ScalarBudget
    labelOuter outerKT carrierFloor eta
  outer_payment : SelectedNormalizedOuterLargeBPaymentBudget
    rho labelOuter Rside.card outerKT eta outerLoss epsilon beta
  eq46 : SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
    S hrho P q source r hr labelInner
      (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q))
      innerLoss (blockAt S.activeCoarseFamily P q).fiber.card
      epsilon beta

/-- The exact two-label large-`b` endpoint at a fixed payment witness. -/
def WinnerSideLargeBLemma69ConclusionAt
    (S : StickyScaleCover sourceFine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (rFrozen : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P Rside) source rFrozen)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (labelOuter labelInner : Fin 3 -> Int) (outerKT : ENNReal)
    (outerLoss innerLoss : ENNReal) (epsilon beta : Real) : Prop :=
  (actualRefinementShading A).averageMultiplicity <=
    (4 * outerLoss * innerLoss *
      prop66InnerScaleMismatchLoss
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        (bucketShortA labelInner) (bucketShortB labelInner) beta) *
      proposition66AFrostmanFactor rho
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        (Rside.card *
          (blockAt S.activeCoarseFamily P q).fiber.card)
        outerKT epsilon beta

/-- Coordinate form of the selected inner cancellation, used after the
payment witness has been destructured once. -/
theorem winnerSideLargeBLemma69_inner_atCoordinates
    (S : StickyScaleCover sourceFine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (hsource : source.shadingMass ≠ 0) (rFrozen : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P Rside) source rFrozen)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (labelInner : Fin 3 -> Int)
    (hcross :
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hrho P q source r hr labelInner *
        (finalFiberShading A (some q)).averageMultiplicity <=
      selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS S P r
        labelInner (blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P q)))
    (innerLoss : ENNReal) (epsilon beta : Real)
    (hEq46 : SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
      S hrho P q source r hr labelInner
        (blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P q))
        innerLoss (blockAt S.activeCoarseFamily P q).fiber.card
        epsilon beta) :
    (finalFiberShading A (some q)).averageMultiplicity <=
      innerLoss * proposition66AInnerFactor rho
        (bucketShortA labelInner) (bucketShortB labelInner)
        (blockAt S.activeCoarseFamily P q).fiber.card epsilon beta := by
  let sourceFactor :=
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
      S hrho P q source r hr labelInner
  let innerTarget := innerLoss * proposition66AInnerFactor rho
    (bucketShortA labelInner) (bucketShortB labelInner)
    (blockAt S.activeCoarseFamily P q).fiber.card epsilon beta
  have hscaled : sourceFactor *
        (finalFiberShading A (some q)).averageMultiplicity <=
      sourceFactor * innerTarget := by
    exact hcross.trans (by
      simpa only [SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget,
        sourceFactor, innerTarget] using hEq46)
  have hsourceFactor0 : sourceFactor ≠ 0 := by
    dsimp only [sourceFactor]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_zero
      S hrho P q source r hr labelInner hsource
  have hsourceFactorTop : sourceFactor ≠ ∞ := by
    dsimp only [sourceFactor]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_top
      S hrho P q source r hr labelInner hsource
  exact (ENNReal.mul_le_mul_iff_right
    hsourceFactor0 hsourceFactorTop).mp hscaled


/-- Generic outer producer.  It is deliberately independent of the endpoint
active-parent implementation: the common container, side label, and
Katz--Tao certificate are supplied as already constructed structural seams. -/
theorem winnerSideLargeBLemma69_outerPaid_atCoordinates
    (hrho : 0 < rho)
    (P : GreedyDensityPartition fine.bodyFamily
      (hullCandidates active) (hullContainer fine.bodyFamily) active)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (source : Shading fine.bodyFamily) (rFrozen : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P Rside) source rFrozen)
    (hAfrozen : A.frozenCoarse =
      (selectedOccurrenceFactorization P Rside).inducedShading
        A.refinement.shading)
    (labelOuter : Fin 3 -> Int)
    (hlabelOuter : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide P hrho k) = labelOuter)
    (hcontains : forall z,
      (selectedOccurrenceNormalizedOuterFamily
          P labelOuter Rside z : Set Space) ⊆
        (normalizedOuterUnitContainer labelOuter : Set Space))
    (outerKT : ENNReal)
    (houterKT : IsKatzTao outerKT
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside))
    (eta : Real) (outerLoss : ENNReal) (epsilon beta : Real)
    (hlemma69Scalar : SelectedNormalizedOuterLemma69ScalarBudget
      labelOuter outerKT
        (winnerSideLargeBLemma69CarrierFloor
          P A.refinement.shading labelOuter Rside) eta)
    (hlargeBOuterPayment : SelectedNormalizedOuterLargeBPaymentBudget
      rho labelOuter Rside.card outerKT eta outerLoss epsilon beta) :
    A.frozenCoarse.averageMultiplicity <=
      outerLoss * proposition66AOuterFactor rho
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        Rside.card outerKT epsilon beta := by
  have hnormalizedPower :=
    winnerSideLargeBLemma69_normalizedOuterPower_at
      hrho P Rside A.refinement.shading labelOuter hlabelOuter hcontains
        outerKT houterKT eta hlemma69Scalar
  have htransport := winnerSideLargeBLemma69_outerTransport_at
    P Rside source rFrozen A hAfrozen labelOuter
  have houterPower : A.frozenCoarse.averageMultiplicity <=
      (bucketShortA labelOuter : ENNReal) ^ (-8 * eta) := by
    rw [htransport]
    exact hnormalizedPower
  exact lemma69Power_le_paidOuterFactor
    rho labelOuter Rside.card outerKT A.frozenCoarse.averageMultiplicity
      outerLoss eta epsilon beta houterPower hlargeBOuterPayment

/-- Final fixed-coordinate core.  The first two scalar budgets have already
been consumed by the generic outer producer; this theorem consumes the one
selected Equation-(46) budget and performs the exact two-label product. -/
theorem winnerSide_largeBLemma69_productAtCoordinates
    (S : StickyScaleCover sourceFine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (hsource : source.shadingMass ≠ 0) (rFrozen : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P Rside) source rFrozen)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (hproduct :
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A (some q)).averageMultiplicity))
    (r : NNReal) (hr : 0 < r) (labelInner labelOuter : Fin 3 -> Int)
    (hcross :
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hrho P q source r hr labelInner *
        (finalFiberShading A (some q)).averageMultiplicity <=
      selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS S P r
        labelInner (blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P q)))
    (outerKT outerLoss innerLoss : ENNReal)
    (epsilon beta : Real) (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (houter : A.frozenCoarse.averageMultiplicity <=
      outerLoss * proposition66AOuterFactor rho
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        Rside.card outerKT epsilon beta)
    (hEq46 : SelectedOccurrenceFrozenSameQPositiveCarrierEq46Budget
      S hrho P q source r hr labelInner
        (blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P q))
        innerLoss (blockAt S.activeCoarseFamily P q).fiber.card
        epsilon beta) :
    WinnerSideLargeBLemma69ConclusionAt
      S P Rside source rFrozen A q labelOuter labelInner outerKT
        outerLoss innerLoss epsilon beta := by
  unfold WinnerSideLargeBLemma69ConclusionAt
  have hinner := winnerSideLargeBLemma69_inner_atCoordinates
    S hrho P Rside source hsource rFrozen A q r hr labelInner hcross
      innerLoss epsilon beta hEq46
  exact paidOuter_mul_paidInner_le_mismatchFrostman
    rho hrho labelOuter labelInner Rside.card
      (blockAt S.activeCoarseFamily P q).fiber.card
      outerKT outerLoss innerLoss
      (actualRefinementShading A).averageMultiplicity
      A.frozenCoarse.averageMultiplicity
      (finalFiberShading A (some q)).averageMultiplicity
      epsilon beta hbeta hbetaOne hproduct houter hinner

#print axioms selectedOccurrenceNormalizedOuterFamily_subset_unitContainer
#print axioms
  selectedOccurrenceNormalizedOuter_averageMultiplicity_le_lemma69Power_automaticFloor
#print axioms WinnerSideLargeBLemma69PaymentWitness
#print axioms exists_winnerSideLargeBLemma69PaymentWitness_of_localPayment
#print axioms WinnerSideLargeBLemma69ScalarBudgetAt
#print axioms WinnerSideLargeBLemma69ConclusionAt
#print axioms winnerSideLargeBLemma69_outerPaid_atCoordinates
#print axioms winnerSide_largeBLemma69_productAtCoordinates

end
end Family8WinnerSideJointBucketLargeBLemma69ConsumerV1

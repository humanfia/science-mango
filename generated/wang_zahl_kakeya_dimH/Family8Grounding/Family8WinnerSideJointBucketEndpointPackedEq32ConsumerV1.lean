import Family8Grounding.Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV1
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierScaledProductV1
import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterDensityBandKatzTaoV1
import Family8Grounding.Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
import Family8Grounding.Family8SelectedParentBlockDensityHullReserveInnerJointV1
import Family8Grounding.Family8SelectedParentSideHullDyadicTwoScaleJointV1
import Family8Grounding.Family8WinnerSideOuterInnerLabelScaleRelationV1
import Mathlib.Tactic

/-!
# Winner-side joint-bucket consumer for endpoint-packed Equation (32)

This is the short object-level route from the winner-side same-occurrence
payment to the two-label endpoint-packed Proposition 6.6(A) estimate. The
joint bucket supplies the common block-density band. At the occurrence and
inner label already selected by the payment, the proof derives the normalized
outer coefficient, outer/inner label relation, original-index count, John
bound, and scaled outer-times-Cordoba estimate.

The exact outer Equation-(45) inequality, the genuinely geometric joint-scale
inequality, and the final pure loss ledger are attached only to that selected
witness. No universally quantified replacement over every possible winner,
occurrence, assembly, or inner label is required.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8WinnerSideJointBucketEndpointPackedEq32ConsumerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8OuterInnerMismatchHighGammaPackingBridgeV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierScaledProductV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1
open Family8SelectedOccurrenceNormalizedOuterDensityBandKatzTaoV1
open Family8SelectedOccurrenceNormalizedOuterScaleBridgeV1
open Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
open Family8SelectedOccurrenceWeightedWinnerSideBucketV1
open Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentBlockDensityHullReserveInnerJointV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentSideHullDyadicTwoScaleJointV1
open Family8SelectedParentSideHullReserveProducerV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8WinnerSideOuterInnerLabelScaleRelationV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The fixed John loss in the literal thresholded block estimate. -/
noncomputable def winnerSideEndpointJohnLoss : ENNReal :=
  16 * certifiedPlankThresholdedAngleScaleCap 576 * (288 : ENNReal) ^ 3

/-- The geometry numerator left after the positive-carrier floor cancels. -/
noncomputable def winnerSideEndpointGeometryScale
    (r : NNReal) (label : Fin 3 -> Int) : ENNReal :=
  certifiedPlankThresholdedAngleScaleCap 576 *
    ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3)

/-- All losses paid while producing the scaled outer-times-local estimate. -/
noncomputable def winnerSideEndpointRawLoss
    (S : StickyScaleCover fine delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (label : Fin 3 -> Int) (outerLoss : ENNReal) : ENNReal :=
  4 * outerLoss *
    ((selectedParentLogarithmicSideBucketLoss delta : ENNReal) *
      (2 * ((certifiedPlankThresholdedAngleBucketLoss
        (bucketShortA label) (bucketShortB label) : Nat) : ENNReal))) *
    selectedOccurrenceFrozenSameQPositiveCarrierLoss S P

/-- The exact coefficient emitted before the surrounding final ledger, with
the outer Frostman-coefficient comparison loss kept explicit. -/
noncomputable def winnerSideEndpointPackedLossWithCoefficient
    (S : StickyScaleCover fine delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (label : Fin 3 -> Int)
    (outerLoss geometryLoss coefficientLoss : ENNReal)
    (beta : Real) : ENNReal :=
  winnerSideEndpointRawLoss S P label outerLoss * geometryLoss *
    coefficientLoss ^ (1 - beta / 2) *
    (outerInnerMismatchEndpointConstant beta *
      (2 : ENNReal) ^ (1 - beta / 2))

/-- Loss-one specialization retained for direct normalized-outer calls. -/
noncomputable def winnerSideEndpointPackedLoss
    (S : StickyScaleCover fine delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (label : Fin 3 -> Int) (outerLoss geometryLoss : ENNReal)
    (beta : Real) : ENNReal :=
  winnerSideEndpointPackedLossWithCoefficient S P label outerLoss
    geometryLoss 1 beta

/-- Precisely the portion of the local-payment existential used downstream.
The cross estimate is derived from the selected label's Cordoba and carrier
cancellation fields when this witness is extracted. -/
structure WinnerSideEq32PaymentWitness
    (S : StickyScaleCover fine delta) (hdelta : 0 < delta)
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
          (selectedParentGreedyBlockJohnFrame S hdelta P occurrence) r hr)
        S (blockAt S.activeCoarseFamily P occurrence).fiber hdelta p))
  cross :
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
        S hdelta P occurrence source r hr innerLabel *
      (finalFiberShading assembly (some occurrence)).averageMultiplicity <=
    selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS S P r
      innerLabel (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P occurrence))

/-- Extract the fixed occurrence/assembly/label witness and mechanically
compose its Cordoba and carrier-floor fields into the cross estimate. -/
theorem exists_winnerSideEq32PaymentWitness_of_localPayment
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family delta) (hdelta : 0 < delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (hlocal : WinnerSideLocalBlockPositiveCarrierPaymentPayload
      D S P Rside source rFrozen hdelta r hr) :
    exists _W : WinnerSideEq32PaymentWitness S hdelta P Rside source
      rFrozen r hr, True := by
  classical
  unfold WinnerSideLocalBlockPositiveCarrierPaymentPayload at hlocal
  obtain ⟨A, hAloss, hAfrozen, q, hq, hcount, _hpositive,
      hproduct, label, hoccupied, _ha, _hab, _hb, hplank,
      hcordoba, _hfloor, hcancel⟩ := hlocal
  have hcross :=
    selectedOccurrenceFrozenSameQPositiveCarrier_sourceFactor_mul_finalFiberAverage_le_expandedEq46LHS
      S hdelta P Rside source A q hq r hr label hplank
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
    innerLabel := label
    innerLabel_occupied := hoccupied
    cross := hcross }, trivial⟩

/-- The exact witness chosen by the winner conclusion, before any later
analytic budgets are requested. -/
structure WinnerSideEq32ChosenWitness
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family delta) (hdelta : 0 < delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (rFrozen : Real) (r : NNReal) (hr : 0 < r) where
  outerLabel : Fin 3 -> Int
  selection : WinnerSideSelectionPayload D S P hdelta R Y fineBucket outerLabel
  payment : WinnerSideEq32PaymentWitness S hdelta P
    (winnerSideRetainedOccurrences D S P hdelta R outerLabel)
    (winnerSideRetainedSource D S P hdelta R Y fineBucket outerLabel)
    rFrozen r hr

theorem exists_winnerSideEq32ChosenWitness_of_conclusion
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family delta) (hdelta : 0 < delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (hwinner : WinnerSideLocalBlockPositiveCarrierPaymentConclusion
      D S P R Y fineBucket rFrozen hdelta r hr) :
    exists _W : WinnerSideEq32ChosenWitness D S hdelta P R Y fineBucket
      rFrozen r hr, True := by
  classical
  unfold WinnerSideLocalBlockPositiveCarrierPaymentConclusion at hwinner
  obtain ⟨outerLabel, hselection, hlocal⟩ := hwinner
  let Rside := winnerSideRetainedOccurrences D S P hdelta R outerLabel
  let source := winnerSideRetainedSource
    D S P hdelta R Y fineBucket outerLabel
  change WinnerSideLocalBlockPositiveCarrierPaymentPayload
    D S P Rside source rFrozen hdelta r hr at hlocal
  obtain ⟨payment, _⟩ :=
    exists_winnerSideEq32PaymentWitness_of_localPayment
      D S hdelta P Rside source rFrozen r hr hlocal
  exact ⟨{
    outerLabel := outerLabel
    selection := hselection
    payment := by simpa only [Rside, source] using payment }, trivial⟩

/-- A canonical fixed witness lets callers state the remaining inputs only
at the existential objects actually supplied by `hwinner`. -/
noncomputable def winnerSideEq32ChosenWitnessOfConclusion
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family delta) (hdelta : 0 < delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (hwinner : WinnerSideLocalBlockPositiveCarrierPaymentConclusion
      D S P R Y fineBucket rFrozen hdelta r hr) :
    WinnerSideEq32ChosenWitness D S hdelta P R Y fineBucket rFrozen r hr :=
  Classical.choose
    (exists_winnerSideEq32ChosenWitness_of_conclusion
      D S hdelta P R Y fineBucket rFrozen r hr hwinner)

/-- Fixed-witness core. The outer Eq.-(45) estimate, joint scale, and final
ledger mention only `W.assembly`, `W.occurrence`, and `W.innerLabel`. Every
other premise of the endpoint-packed two-label estimate is derived here. -/
theorem winnerSide_jointBucket_endpointPackedEq32_at
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family delta)
    (hParent : (activeParentActualTubeDatum S D.shading).IsAdmissible)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (outerLabel : Fin 3 -> Int)
    (hselection : WinnerSideSelectionPayload
      D S P hdelta R Y fineBucket outerLabel)
    (W : WinnerSideEq32PaymentWitness S hdelta P
      (winnerSideRetainedOccurrences D S P hdelta R outerLabel)
      (winnerSideRetainedSource D S P hdelta R Y fineBucket outerLabel)
      rFrozen r hr)
    (base : ENNReal) (bucketKey : Nat)
    (hbandAt : InENNRealDyadicBand base bucketKey
      (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P W.occurrence)))
    (hbaseOne : 1 <= base) (hbaseTop : base ≠ ∞)
    (outerCFUsed coefficientLoss sourceCF : ENNReal)
    (outerLoss refinementLoss geometryLoss externalLoss : ENNReal)
    (epsilon beta : Real) (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (houterCF :
      outerCFUsed <= coefficientLoss * sourceCF *
        ((2 : ENNReal) ^ bucketKey * base)⁻¹)
    (houterEq45 : W.assembly.frozenCoarse.averageMultiplicity <=
      outerLoss * proposition66AOuterFactor delta
        (bucketShortA outerLabel) (bucketShortB outerLabel)
        (winnerSideRetainedOccurrences D S P hdelta R outerLabel).card
        (outerCFUsed * refinementLoss) epsilon beta)
    (hjointScale :
      winnerSideEndpointJohnLoss *
          ((((2 : ENNReal) ^ (beta / 2) *
                (selectedParentSideHullEnvelope delta
                  (bucketShortA W.innerLabel)) ^ (beta / 2)) *
              ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1)) *
            ((blockAt S.activeCoarseFamily P W.occurrence).fiber.card :
                ENNReal) ^ (1 - beta / 2)) <=
        ((winnerSideRetainedSource
            D S P hdelta R Y fineBucket outerLabel).shadingDensity *
          geometryLoss) *
          proposition66AInnerFactor delta
            (bucketShortA W.innerLabel) (bucketShortB W.innerLabel)
            (blockAt S.activeCoarseFamily P W.occurrence).fiber.card
            epsilon beta)
    (hfinalLedger : winnerSideEndpointPackedLossWithCoefficient S P
      W.innerLabel outerLoss geometryLoss coefficientLoss beta <=
        externalLoss) :
    (actualRefinementShading W.assembly).averageMultiplicity <=
      externalLoss * proposition66AFrostmanFactor delta
        (bucketShortA outerLabel) (bucketShortB outerLabel)
        (Fintype.card index)
        (endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
          (sourceCF * refinementLoss)) epsilon beta := by
  classical
  let Rside := winnerSideRetainedOccurrences D S P hdelta R outerLabel
  let source := winnerSideRetainedSource
    D S P hdelta R Y fineBucket outerLabel
  have hsourceMass : source.shadingMass ≠ 0 := by
    simpa only [source] using hselection.2.2.2.1
  change WinnerSideEq32PaymentWitness S hdelta P Rside source
    rFrozen r hr at W
  rcases W with ⟨A, _hAloss, _hAfrozen, q, hq, hcountActive, hproduct,
    labelInner, hoccupied, hcross⟩
  let B := (blockAt S.activeCoarseFamily P q).fiber
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hdelta P q) r hr
  let J := affineJacobian (bucketNormalizedAffineEquiv e labelInner)
  let area : ENNReal := (delta : ENNReal) ^ 2 / 2
  let d := blockDensity S.activeCoarseFamily
    (blockAt S.activeCoarseFamily P q)
  let G := winnerSideEndpointGeometryScale r labelInner
  let johnLoss := winnerSideEndpointJohnLoss
  let rawLoss := winnerSideEndpointRawLoss S P labelInner outerLoss
  let outerBound := proposition66AOuterFactor delta
    (bucketShortA outerLabel) (bucketShortB outerLabel) Rside.card
    (outerCFUsed * refinementLoss) epsilon beta
  have hbandq : InENNRealDyadicBand base bucketKey d := by
    simpa only [d, Rside, source] using hbandAt
  have hrel : Prop66OuterInnerLabelScaleRelation
      (delta / 576) (delta / 11943936) outerLabel labelInner := by
    exact winnerSide_outerInnerLabelScaleRelation
      D hD S hParent hdelta hdeltaHalf P R Y fineBucket outerLabel
        hselection q r hr labelInner hoccupied
  obtain ⟨p, _hp, hpLabel⟩ :=
    mem_occupiedWeightBuckets_iff.mp hoccupied
  let plankWitness : {p // p ∈ selectedParentPlankBucketIndices e S B
      hdelta labelInner} := ⟨p, by
    rw [selectedParentPlankBucketIndices, mem_sideShapeBucket_iff]
    exact ⟨Finset.mem_univ _, hpLabel⟩⟩
  have hsource0 : J * (source.shadingDensity * area) ≠ 0 := by
    have h :=
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_zero
        S hdelta P q source r hr labelInner hsourceMass
    simpa only [J, e, area,
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor] using h
  have hsourceTop : J * (source.shadingDensity * area) ≠ ∞ := by
    have h :=
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_top
        S hdelta P q source r hr labelInner hsourceMass
    simpa only [J, e, area,
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor] using h
  have hcount :
      (((Rside.card * B.card : Nat) : ENNReal) <=
        (2 : ENNReal) * (Fintype.card index : ENNReal)) := by
    have hactiveNat : Fintype.card (ActiveParentIndex S) <=
        Fintype.card index := by
      rw [Fintype.card_coe]
      exact
        (Family8StickyActiveIndexFrozenComparableAssemblyV5.activeCoarse_card_le_activeFine_card
          S).trans
            (Finset.card_le_univ S.activeFine)
    have hactive : (Fintype.card (ActiveParentIndex S) : ENNReal) <=
        (Fintype.card index : ENNReal) := by
      exact_mod_cast hactiveNat
    calc
      ((Rside.card * B.card : Nat) : ENNReal) <=
          (2 : ENNReal) * (Fintype.card (ActiveParentIndex S) : ENNReal) := by
        exact_mod_cast hcountActive
      _ <= (2 : ENNReal) * (Fintype.card index : ENNReal) :=
        mul_le_mul' le_rfl hactive
  have hscaledProduct :
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hdelta P q source r hr labelInner *
        (actualRefinementShading A).averageMultiplicity <=
      4 * A.frozenCoarse.averageMultiplicity *
        selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
          S P r labelInner d := by
    exact sourceFactor_mul_actualRefinementAverage_le_four_mul_outer_mul_cross
      S hdelta P Rside source A q r hr labelInner
        (selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
          S P r labelInner d) hproduct hcross
  have houter : A.frozenCoarse.averageMultiplicity <=
      outerLoss * outerBound := by
    simpa only [Rside, outerBound] using houterEq45
  have hscaled :
      (J * (source.shadingDensity * area)) *
          (actualRefinementShading A).averageMultiplicity <=
        rawLoss * (outerBound * (d * G)) := by
    calc
      (J * (source.shadingDensity * area)) *
          (actualRefinementShading A).averageMultiplicity =
        selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
            S hdelta P q source r hr labelInner *
          (actualRefinementShading A).averageMultiplicity := by rfl
      _ <= 4 * A.frozenCoarse.averageMultiplicity *
          selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
            S P r labelInner d := hscaledProduct
      _ <= 4 * (outerLoss * outerBound) *
          selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
            S P r labelInner d :=
        mul_le_mul' (mul_le_mul' le_rfl houter) le_rfl
      _ = rawLoss * (outerBound * (d * G)) := by
        dsimp only [rawLoss, winnerSideEndpointRawLoss, G,
          winnerSideEndpointGeometryScale]
        unfold selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
        ac_rfl
  have hJohn : d * G <= J * (johnLoss * ((B.card : ENNReal) * area)) := by
    have h := blockDensity_mul_thresholdedCordobaNumerator_le_jacobian_card_area
      S hdelta hdeltaHalf P q r hr labelInner
    simpa only [d, G, winnerSideEndpointGeometryScale, e, J, B, area,
      johnLoss, winnerSideEndpointJohnLoss] using h
  have hjoint :
      johnLoss *
          ((((2 : ENNReal) ^ (beta / 2) *
                (selectedParentSideHullEnvelope delta
                  (bucketShortA labelInner)) ^ (beta / 2)) *
              ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1)) *
            ((blockAt S.activeCoarseFamily P q).fiber.card : ENNReal) ^
              (1 - beta / 2)) <=
        (source.shadingDensity * geometryLoss) *
          proposition66AInnerFactor delta
            (bucketShortA labelInner) (bucketShortB labelInner)
            (blockAt S.activeCoarseFamily P q).fiber.card epsilon beta := by
    simpa only [johnLoss, Rside, source] using hjointScale
  have hexact :=
    selectedParent_average_le_endpointPackedFrostmanFactor_twoLabels_actualCount
      (fun i => hD.contained_in_unit_ball i) S hdelta hdeltaHalf P q r hr
      outerLabel labelInner plankWitness hrel base bucketKey hbandq
      hbaseOne hbaseTop
      (plankCount := Rside.card) (totalCount := Fintype.card index)
      (average := (actualRefinementShading A).averageMultiplicity)
      (geometricScale := G) (jacobian := J)
      (sourceDensity := source.shadingDensity) (area := area)
      (johnLoss := johnLoss) (rawLoss := rawLoss)
      (geometryLoss := geometryLoss) (coefficientLoss := coefficientLoss)
      (outerCF := outerCFUsed) (sourceCF := sourceCF)
      (refinementLoss := refinementLoss) (countLoss := 2)
      (epsilon := epsilon) (beta := beta) hbeta0 hbetaOne hsource0
      hsourceTop (by simpa only [B] using hcount) houterCF hjoint
      hscaled hJohn
  calc
    (actualRefinementShading A).averageMultiplicity <=
        winnerSideEndpointPackedLossWithCoefficient S P labelInner outerLoss
            geometryLoss coefficientLoss beta *
          proposition66AFrostmanFactor delta
            (bucketShortA outerLabel) (bucketShortB outerLabel)
            (Fintype.card index)
            (endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
              (sourceCF * refinementLoss)) epsilon beta := by
      simpa only [winnerSideEndpointPackedLossWithCoefficient, rawLoss]
        using hexact
    _ <= externalLoss * proposition66AFrostmanFactor delta
        (bucketShortA outerLabel) (bucketShortB outerLabel)
        (Fintype.card index)
        (endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
          (sourceCF * refinementLoss)) epsilon beta :=
      mul_le_mul' hfinalLedger le_rfl

#print axioms exists_winnerSideEq32PaymentWitness_of_localPayment
#print axioms exists_winnerSideEq32ChosenWitness_of_conclusion
#print axioms winnerSide_jointBucket_endpointPackedEq32_at

end
end Family8WinnerSideJointBucketEndpointPackedEq32ConsumerV1

import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchCallsV5B
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32PyzActualCanonicalPayloadLocalEstimateV5
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterLowHalfMomentV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchCallsV5B

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

def nativePhysical
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real -> Real) (hfContinuous : Continuous f)
    (outerA outerB : Real) : FiniteProjectedShading (Real × Real) iota :=
  actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
    physicalBase hphysicalBase f hfContinuous outerA outerB

def nativeCenters
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota) (ambient : Finset iota)
    (globalScale : Real) : Finset (Tube radius) :=
  finiteMetricCoverCenters (activeTubeImage S.family ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun T U => projectedTubePairCoefficientDistance_comm T U)

/-- Common actual data used by both native branches.  It stores geometry and
the hypotheses needed by V2, but no payload family, branch, split, or local
conclusion. -/
structure NativeBranchCore (radius : NNReal) (iota : Type u)
    [Fintype iota] [DecidableEq iota] where
  S : WZL3UniformTubeSource radius iota
  ambient : Finset iota
  physicalBase : Set (Real × Real)
  hphysicalBase : MeasurableSet physicalBase
  f : Real -> Real
  hfContinuous : Continuous f
  f1 : Real -> Real
  f2 : Real -> Real
  outerA : Real
  outerB : Real
  hOuter : outerA <= outerB
  hf : forall z, HasDerivAt f (f1 z) z
  hf1 : forall z, HasDerivAt f1 (f2 z) z
  globalScale : Real
  hglobalScale : 0 < globalScale
  cell : Tube radius -> Set (Real × Real)
  tangencyExponent : Real
  normExponent : Real
  logCount : Nat
  hradius : 0 < radius
  hradiusSixteen : (radius : Real) <= 16
  hradiusTangency : (radius : Real) <= 36 * globalScale
  hnormExponent : 0 <= normExponent
  hcellMeasurable : forall center,
    center ∈ nativeCenters S ambient globalScale -> MeasurableSet (cell center)
  hlocalized : forall center,
    center ∈ nativeCenters S ambient globalScale ->
    forall x, x ∈ cell center ->
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily S.family
          (nativePhysical S ambient physicalBase hphysicalBase f
            hfContinuous outerA outerB).ambient)
        projectedTubePairCoefficientDistance globalScale center
        ((nativePhysical S ambient physicalBase hphysicalBase f
          hfContinuous outerA outerB).activeAtPoint x)).Nonempty
  sourceMass : ENNReal
  hsourceMass : sourceMass =
    ∑ center ∈ nativeCenters S ambient globalScale, volume (cell center)

namespace NativeBranchCore

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]

def physical (D : NativeBranchCore radius iota) :=
  nativePhysical D.S D.ambient D.physicalBase D.hphysicalBase D.f
    D.hfContinuous D.outerA D.outerB

def centers (D : NativeBranchCore radius iota) :=
  nativeCenters D.S D.ambient D.globalScale

abbrev PositiveCenter (D : NativeBranchCore radius iota) :=
  ActualAllCenterPositiveCenter volume D.centers D.cell

noncomputable def payloadAt (D : NativeBranchCore radius iota) :
    forall center : D.PositiveCenter,
      ActualPositiveCenterCanonicalPayload volume (D.cell center.1)
        (D.hcellMeasurable center.1
          ((Finset.mem_filter.mp center.2).1))
        D.S.family D.physical D.f D.f1 D.f2 D.outerA D.outerB D.hOuter
          D.hf D.hf1 D.globalScale center.1 D.tangencyExponent :=
  actualAllCenterChosenPayloadAt volume D.S.family D.physical D.f D.f1 D.f2
    D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale D.centers D.cell
    D.tangencyExponent D.logCount D.hradius D.hradiusTangency
    D.hcellMeasurable D.hlocalized D.sourceMass D.hsourceMass

def degree (D : NativeBranchCore radius iota) (center : D.PositiveCenter) : Nat :=
  pyzE2DegreeLower (D.payloadAt center).finalLabel

def high (D : NativeBranchCore radius iota) : Finset D.PositiveCenter :=
  actualAllCenterHigh D.degree D.logCount

def low (D : NativeBranchCore radius iota) : Finset D.PositiveCenter :=
  actualAllCenterLow D.degree D.logCount

abbrev HighCenter (D : NativeBranchCore radius iota) :=
  {center : D.PositiveCenter // center ∈ D.high}

def positiveBase (D : NativeBranchCore radius iota) (c : D.PositiveCenter) :=
  D.cell c.1

theorem positiveBase_measurable (D : NativeBranchCore radius iota)
    (c : D.PositiveCenter) : MeasurableSet (D.positiveBase c) := by
  exact D.hcellMeasurable c.1 ((Finset.mem_filter.mp c.2).1)

def highBase (D : NativeBranchCore radius iota) (c : D.HighCenter) :=
  D.positiveBase c.1

theorem highBase_measurable (D : NativeBranchCore radius iota)
    (c : D.HighCenter) : MeasurableSet (D.highBase c) :=
  D.positiveBase_measurable c.1

abbrev HighPayloadCandidate (D : NativeBranchCore radius iota)
    (c : D.HighCenter) :=
  ActualHighPayloadWithNormNonconcentration volume (D.highBase c)
    (D.highBase_measurable c) D.S.family D.physical D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
        D.tangencyExponent D.normExponent D.logCount

/-- The high payload is manufactured from the frozen V2 choice. -/
noncomputable def chosenHighPayloadAt (D : NativeBranchCore radius iota)
    (c : D.HighCenter) : D.HighPayloadCandidate c :=
  actualHighPayloadOfCanonicalPayload D.S.family D.physical D.f D.f1 D.f2
    D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
    (D.highBase c) (D.highBase_measurable c) D.tangencyExponent
    D.normExponent D.logCount (D.payloadAt c.1)
    ((Finset.mem_filter.mp c.2).2) D.hradius D.hradiusSixteen
    D.hnormExponent
    (fun x hx => ambientCriticalFamily_nonempty_of_localized D.S.family
      D.physical D.globalScale c.1.1 x
      (D.hlocalized c.1.1 ((Finset.mem_filter.mp c.1.2).1) x hx))

/-- V2's exact split, specialized definitionally to the frozen core. -/
theorem payloadAt_spec (D : NativeBranchCore radius iota) :
    D.sourceMass =
        (∑ center ∈ D.high, volume (D.cell center.1)) +
          ∑ center ∈ D.low, volume (D.cell center.1) ∧
      (D.sourceMass / 2 <=
          ∑ center ∈ D.high, volume (D.cell center.1) ∨
        D.sourceMass / 2 <=
          ∑ center ∈ D.low, volume (D.cell center.1)) ∧
      (forall center, center ∈ D.high ->
        24 * D.logCount <= D.degree center) ∧
      (forall center, center ∈ D.low ->
        D.degree center < 24 * D.logCount) := by
  exact actualAllCenterChosenPayloadAt_spec volume D.S.family D.physical D.f
    D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
    D.centers D.cell D.tangencyExponent D.logCount D.hradius
    D.hradiusTangency D.hcellMeasurable D.hlocalized D.sourceMass
    D.hsourceMass

end NativeBranchCore

/-- Only the explicit V3 scalar geometry inputs, evaluated on the payload
already fixed by the core. -/
structure NativeHighGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) where
  bucket : Int
  hbucket : forall i, i ∈ D.ambient ->
    actualProjectedTubeCBucket ((radius : Real) / 2) (D.S.family.tubes i) =
      bucket
  mesh : D.HighCenter -> Real
  ballRadius : D.HighCenter -> Real
  hmesh : forall c, 0 < mesh c
  hparameter : forall z, z ∈ Icc D.outerA D.outerB -> |z| <= 1
  sharp : forall c, ActualY1SharpFineScaleNumerics
    (radius : Real)
      (dyadicCeilUpper (D.chosenHighPayloadAt c).payload.tangencyLabel)
      D.globalScale (D.outerB - D.outerA)
  hft : forall z, z ∈ Icc D.outerA D.outerB -> |D.f z| <= 2
  hf1Lower : forall z, z ∈ Icc D.outerA D.outerB -> 1 <= |D.f1 z|
  hf1Upper : forall z, z ∈ Icc D.outerA D.outerB -> |D.f1 z| <= 2
  hf2 : forall z, z ∈ Icc D.outerA D.outerB -> |D.f2 z| <= 1 / 100
  hf2Continuous : ContinuousOn D.f2 (Icc D.outerA D.outerB)
  hmeshBase : forall c, mesh c <= Real.sqrt ((radius : Real) /
    prop41Y1PaperFineT (radius : Real)
      (dyadicCeilUpper (D.chosenHighPayloadAt c).payload.tangencyLabel)
      D.globalScale) / 2
  hroom : forall c, automaticCanonicalNearCap
    (positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c))
      (ballRadius c) <
        pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel
  hnearRadiusLower : forall c,
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).delta <= 10 * ballRadius c
  hnearRadiusUpper : forall c, 10 * ballRadius c <=
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).ceiling
  hballRadiusLower : forall c,
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).delta <= ballRadius c
  hballRadiusUpper : forall c, ballRadius c <=
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).ceiling
  hsmall : forall c,
    ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real)
      (dyadicCeilUpper (D.chosenHighPayloadAt c).payload.tangencyLabel)
      D.globalScale (4 * ballRadius c)
  hcount : forall c,
    ActualY1PaperFineCNormalizedSelectedCountingSmallness
      (radius : Real)
      (dyadicCeilUpper (D.chosenHighPayloadAt c).payload.tangencyLabel)
      D.globalScale (4 * ballRadius c)

def NativeHighGeometry.Outcome
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} (G : NativeHighGeometry D) : Prop :=
  ActualAllCenterHighNativeOutcome D.highBase D.highBase_measurable D.S.family
    D.ambient D.physicalBase D.hphysicalBase D.f D.hfContinuous D.f1 D.f2
    D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
    (fun c => c.1.1) D.tangencyExponent D.normExponent D.logCount
    D.chosenHighPayloadAt G.mesh G.ballRadius D.sourceMass

/-- Only the explicit V4 low-side geometry and scalar inputs. -/
structure NativeLowGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) where
  E : Set (Real × Real)
  alpha : Real
  C : ENNReal
  Q : PyzCarrierQuasiProduct E
    (pyzFrostmanIntervalBound (radius : Real) alpha C)
  hambient : D.ambient ⊆ D.S.source
  hunit : forall i, i ∈ D.ambient ->
    (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1
  hparameter : forall z, z ∈ Icc D.outerA D.outerB -> |z| <= 1
  halpha : 0 <= alpha
  halphaOne : alpha <= 1
  hfun : forall z, z ∈ Icc D.outerA D.outerB -> |D.f z| <= 2
  hfun1 : forall z, z ∈ Icc D.outerA D.outerB -> |D.f1 z| <= 2
  lower : Nat
  upper : Nat
  multiplicity : Nat
  htangencyExponent : 0 <= D.tangencyExponent
  hbaseSubset : forall a, a ∈ D.low -> D.positiveBase a ⊆ E
  hbaseBand : forall a, a ∈ D.low ->
    D.positiveBase a ⊆ D.physical.multiplicityBand lower upper
  hpairAmbient : Set.Pairwise (D.ambient : Set iota) fun i j =>
    EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j)
  hpairAt : forall a, a ∈ D.low ->
    Set.Pairwise
      (D.physical.activeAtPoint (D.payloadAt a).q : Set iota)
      (fun i j => EssentiallyDistinct (D.S.family.tubes i)
        (D.S.family.tubes j))
  hactiveCapAt : forall a, a ∈ D.low ->
    forall center, center ∈ actualProjectedCriticalFamily D.S.family
        (D.physical.activeAtPoint (D.payloadAt a).q) ->
      (activeNearCoefficientIndices D.S.family
        (D.physical.activeAtPoint (D.payloadAt a).q) center
        (radius : Real)).card <= multiplicity
  hfamilyAt : forall a, a ∈ D.low ->
    (actualProjectedAmbientCriticalFamily D.S.family D.physical.ambient
      (D.physical.activeAtPoint (D.payloadAt a).q)).Nonempty
  hnormBallSubsetAt : forall a (ha : a ∈ D.low),
    let family := actualProjectedAmbientCriticalFamily D.S.family
      D.physical.ambient (D.physical.activeAtPoint (D.payloadAt a).q)
    finiteNormCriticalBall family projectedTubePairCoefficientDistance
        (radius : Real) 16 D.normExponent (hfamilyAt a ha) ⊆
      finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily D.S.family D.physical.ambient)
        projectedTubePairCoefficientDistance D.globalScale a.1
        (D.physical.activeAtPoint (D.payloadAt a).q)
  hnormScaleLowerAt : forall a, a ∈ D.low ->
    (radius : Real) / 2 < actualProjectedAmbientNormScale D.S.family
      D.physical 16 D.normExponent (D.payloadAt a).q

def NativeLowGeometry.Outcome
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} (L : NativeLowGeometry D) : Prop :=
  actualCanonicalPayloadGlobalWeight L.lower D.globalScale D.normExponent
      D.tangencyExponent * (D.sourceMass / 2) <=
    actualCanonicalPayloadCommonCost radius D.globalScale D.ambient.card
        L.multiplicity D.logCount D.normExponent D.tangencyExponent
        L.alpha L.C *
      ((19 ^ 3 * D.ambient.card : Nat) : ENNReal)

#print axioms NativeBranchCore.payloadAt_spec
#print axioms NativeBranchCore.chosenHighPayloadAt
#print axioms NativeHighGeometry.Outcome
#print axioms NativeLowGeometry.Outcome

end
end FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterLowHalfMomentV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- The actual positive cells on which the dependent canonical payload is
selected.  This is definitionally the subtype used by the frozen V2
selection theorem. -/
def actualAllCenterPositiveCenters
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} (mu : Measure point)
    (centers : Finset (Tube radius)) (cell : Tube radius -> Set point) :
    Finset (Tube radius) :=
  centers.filter fun center => 0 < mu (cell center)

abbrev ActualAllCenterPositiveCenter
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} (mu : Measure point)
    (centers : Finset (Tube radius)) (cell : Tube radius -> Set point) :=
  {center // center ∈ actualAllCenterPositiveCenters mu centers cell}

/-- The literal high half of a chosen dependent payload family. -/
def actualAllCenterHigh
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (degree : alpha -> Nat) (logCount : Nat) : Finset alpha :=
  (Finset.univ : Finset alpha).filter fun a => 24 * logCount <= degree a

/-- The complementary literal low half of a chosen dependent payload family. -/
def actualAllCenterLow
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (degree : alpha -> Nat) (logCount : Nat) : Finset alpha :=
  (Finset.univ : Finset alpha).filter fun a => ¬ 24 * logCount <= degree a

/-- Freeze the exact dependent payload selected by V2.  It is a definition,
not a caller-supplied payload callback. -/
noncomputable def actualAllCenterChosenPayloadAt
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real)
    (centers : Finset (Tube radius)) (cell : Tube radius -> Set point)
    (tangencyExponent : Real) (logCount : Nat)
    (hradius : 0 < radius)
    (hradiusTangency : (radius : Real) <= 36 * globalScale)
    (hcellMeasurable : forall center, center ∈ centers ->
      MeasurableSet (cell center))
    (hlocalized : forall center, center ∈ centers ->
      forall x, x ∈ cell center ->
        (finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily fine physical.ambient)
          projectedTubePairCoefficientDistance globalScale center
          (physical.activeAtPoint x)).Nonempty)
    (sourceMass : ENNReal)
    (hsourceMass : sourceMass = ∑ center ∈ centers, mu (cell center)) :
    forall center : ActualAllCenterPositiveCenter mu centers cell,
      ActualPositiveCenterCanonicalPayload mu (cell center.1)
        (hcellMeasurable center.1
          ((Finset.mem_filter.mp center.2).1))
        fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
          center.1 tangencyExponent :=
  Classical.choose
    (exists_actualAllCenter_payloadAt_mass_high_or_low mu fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale centers cell
      tangencyExponent logCount hradius hradiusTangency hcellMeasurable
      hlocalized sourceMass hsourceMass)

/-- The frozen V2 choice retains the exact mass partition and the half-mass
alternative, together with the literal degree inequalities on both sides. -/
theorem actualAllCenterChosenPayloadAt_spec
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real)
    (centers : Finset (Tube radius)) (cell : Tube radius -> Set point)
    (tangencyExponent : Real) (logCount : Nat)
    (hradius : 0 < radius)
    (hradiusTangency : (radius : Real) <= 36 * globalScale)
    (hcellMeasurable : forall center, center ∈ centers ->
      MeasurableSet (cell center))
    (hlocalized : forall center, center ∈ centers ->
      forall x, x ∈ cell center ->
        (finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily fine physical.ambient)
          projectedTubePairCoefficientDistance globalScale center
          (physical.activeAtPoint x)).Nonempty)
    (sourceMass : ENNReal)
    (hsourceMass : sourceMass = ∑ center ∈ centers, mu (cell center)) :
    let payloadAt := actualAllCenterChosenPayloadAt mu fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale centers cell
      tangencyExponent logCount hradius hradiusTangency hcellMeasurable
      hlocalized sourceMass hsourceMass
    let degree := fun center =>
      pyzE2DegreeLower (payloadAt center).finalLabel
    let high := actualAllCenterHigh degree logCount
    let low := actualAllCenterLow degree logCount
    sourceMass =
        (∑ center ∈ high, mu (cell center.1)) +
          ∑ center ∈ low, mu (cell center.1) ∧
      (sourceMass / 2 <= ∑ center ∈ high, mu (cell center.1) ∨
        sourceMass / 2 <= ∑ center ∈ low, mu (cell center.1)) ∧
      (forall center, center ∈ high ->
        24 * logCount <= degree center) ∧
      (forall center, center ∈ low ->
        degree center < 24 * logCount) := by
  exact Classical.choose_spec
    (exists_actualAllCenter_payloadAt_mass_high_or_low mu fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale centers cell
      tangencyExponent logCount hradius hradiusTangency hcellMeasurable
      hlocalized sourceMass hsourceMass)

/- Split into the separately compiled V5B branch-call layer.
/-- A nonempty fixed-scale localization is still a member of its ambient
critical family.  This is a definitional filter projection, not an extra
geometric hypothesis. -/
theorem actualProjectedAmbientCriticalFamily_nonempty_of_localized
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (globalScale : Real) (center : Tube radius) (x : point)
    (hlocalized :
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale center
        (physical.activeAtPoint x)).Nonempty) :
    (actualProjectedAmbientCriticalFamily fine physical.ambient
      (physical.activeAtPoint x)).Nonempty := by
  rcases hlocalized with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  change T ∈ finiteFamilyMetricBall
    (actualProjectedAmbientCriticalFamily fine physical.ambient
      (physical.activeAtPoint x))
    projectedTubePairCoefficientDistance (3 * globalScale) center at hT
  exact (Finset.mem_filter.mp hT).1

section ActualHigh

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable (S : WZL3UniformTubeSource radius iota)
variable (ambient : Finset iota)
variable (physicalBase : Set (Real × Real))
  (hphysicalBase : MeasurableSet physicalBase)
variable (f : Real -> Real) (hfContinuous : Continuous f)
variable (f1 f2 : Real -> Real) (outerA outerB : Real)
variable (hOuter : outerA <= outerB)
variable (hf : forall z, HasDerivAt f (f1 z) z)
variable (hf1 : forall z, HasDerivAt f1 (f2 z) z)
variable (globalScale : Real)
variable (cell : Tube radius -> Set (Real × Real))
variable (tangencyExponent normExponent : Real) (logCount : Nat)
variable (hradius : 0 < radius)
variable (hradiusSixteen : (radius : Real) <= 16)
variable (hradiusTangency : (radius : Real) <= 36 * globalScale)
variable (hnormExponent : 0 <= normExponent)

local notation "physical" =>
  actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
    physicalBase hphysicalBase f hfContinuous outerA outerB

local notation "centers" =>
  finiteMetricCoverCenters
    (activeTubeImage S.family ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun T U => projectedTubePairCoefficientDistance_comm T U)

variable (hcellMeasurable : forall center, center ∈ centers ->
  MeasurableSet (cell center))
variable (hlocalized : forall center, center ∈ centers ->
  forall x, x ∈ cell center ->
    (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily S.family physical.ambient)
      projectedTubePairCoefficientDistance globalScale center
      (physical.activeAtPoint x)).Nonempty)
variable (sourceMass : ENNReal)
variable (hsourceMass :
  sourceMass = ∑ center ∈ centers, volume (cell center))

local notation "payloadAt" =>
  actualAllCenterChosenPayloadAt volume S.family physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale centers cell
    tangencyExponent logCount hradius hradiusTangency hcellMeasurable
    hlocalized sourceMass hsourceMass

local notation "degree" =>
  (fun center => pyzE2DegreeLower (payloadAt center).finalLabel)

local notation "high" => actualAllCenterHigh degree logCount

/-- The high-side wrapper is constructed from the literal V2 payload and the
already required localized-family nonemptiness.  Callers do not choose a
second payload. -/
noncomputable def actualAllCenterChosenHighPayloadAt
    (c : {center // center ∈ high}) :
    ActualHighPayloadWithNormNonconcentration volume (cell c.1.1)
      (hcellMeasurable c.1.1
        ((Finset.mem_filter.mp c.1.2).1))
      S.family physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
        c.1.1 tangencyExponent normExponent logCount :=
  ActualHighPayloadWithNormNonconcentration.ofPayload
    (payloadAt c.1)
    ((Finset.mem_filter.mp c.2).2)
    hradius hradiusSixteen hnormExponent
    (fun x hx =>
      actualProjectedAmbientCriticalFamily_nonempty_of_localized
        S.family physical globalScale c.1.1 x
        (hlocalized c.1.1
          ((Finset.mem_filter.mp c.1.2).1) x hx))

end ActualHigh
-/
#print axioms actualAllCenterChosenPayloadAt
#print axioms actualAllCenterChosenPayloadAt_spec

end
end FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5

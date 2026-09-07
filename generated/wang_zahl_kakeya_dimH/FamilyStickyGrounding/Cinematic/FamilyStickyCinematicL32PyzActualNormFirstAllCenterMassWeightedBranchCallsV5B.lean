import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchCallsV5B

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterLowHalfMomentV4
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- A nonempty fixed-scale localization projects to a genuine ambient-family
member. -/
theorem ambientCriticalFamily_nonempty_of_localized
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

/-- The unmodified native high-side conclusion returned by V3. -/
def ActualAllCenterHighNativeOutcome
    {center : Type v} [Fintype center] [DecidableEq center]
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (base : center -> Set (Real × Real))
    (hbase : forall c, MeasurableSet (base c))
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real -> Real) (hfContinuous : Continuous f)
    (f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : center -> Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (HAt : forall c,
      ActualHighPayloadWithNormNonconcentration volume (base c) (hbase c)
        fine
        (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
        f f1 f2 outerA outerB hOuter hf hf1 globalScale (globalCenter c)
          tangencyExponent normExponent logCount)
    (mesh ballRadius : center -> Real) (sourceMass : ENNReal) : Prop :=
  exists hlocal : forall c,
    PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (base c) (hbase c) fine
      (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB)
      f f1 f2 outerA outerB hOuter hf hf1 globalScale (globalCenter c)
        tangencyExponent normExponent logCount (HAt c) (mesh c)
          (ballRadius c),
    sourceMass / 2 <= ∑ c,
      positiveCenterHighPayload_baseChosenSampledLensRHS
        (base c) (hbase c) fine
        (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
        f f1 f2 outerA outerB hOuter hf hf1 globalScale (globalCenter c)
          tangencyExponent normExponent logCount (HAt c) (mesh c)
            (ballRadius c) (hlocal c)

#print axioms ambientCriticalFamily_nonempty_of_localized
section SingleCellHighPayload

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable (fine : UniformTubeFamily radius iota)
variable (physical : FiniteProjectedShading (Real × Real) iota)
variable (f f1 f2 : Real -> Real) (outerA outerB : Real)
variable (hOuter : outerA <= outerB)
variable (hf : forall z, HasDerivAt f (f1 z) z)
variable (hf1 : forall z, HasDerivAt f1 (f2 z) z)
variable (globalScale : Real) (center : Tube radius)
variable (base : Set (Real × Real)) (hbase : MeasurableSet base)
variable (tangencyExponent normExponent : Real) (logCount : Nat)
variable (P : ActualPositiveCenterCanonicalPayload volume base hbase fine
  physical f f1 f2 outerA outerB hOuter hf hf1 globalScale center
    tangencyExponent)

/-- Upgrade one selected canonical payload on a literal high cell. -/
noncomputable def actualHighPayloadOfCanonicalPayload
    (hhigh : 24 * logCount <= pyzE2DegreeLower P.finalLabel)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) <= 16)
    (hnormExponent : 0 <= normExponent)
    (hfamily : forall x, x ∈ base ->
      (actualProjectedAmbientCriticalFamily fine physical.ambient
        (physical.activeAtPoint x)).Nonempty) :
    ActualHighPayloadWithNormNonconcentration volume base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale center
        tangencyExponent normExponent logCount :=
  ActualHighPayloadWithNormNonconcentration.ofPayload P hhigh hradius
    hradiusSixteen hnormExponent hfamily

end SingleCellHighPayload
#print axioms ActualAllCenterHighNativeOutcome

end
end FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchCallsV5B

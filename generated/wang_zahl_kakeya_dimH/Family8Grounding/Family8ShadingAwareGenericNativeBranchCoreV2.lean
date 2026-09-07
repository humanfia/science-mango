import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ShadingAwareGenericNativeBranchCoreV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchCallsV5B
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open Family8ShadingAwareProjectedPhysicalV3

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

def genericNativeCenters
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) : Finset (Tube radius) :=
  finiteMetricCoverCenters (activeTubeImage S.family physical.ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun T U => projectedTubePairCoefficientDistance_comm T U)

/-- The branch core with the projected physical datum exposed as a genuine
parameter.  In particular, neither a full tube trace nor a desired local
estimate is stored in the structure. -/
structure GenericNativeBranchCore
    (radius : NNReal) (iota : Type u)
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f : Real -> Real) (hfContinuous : Continuous f) where
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
    center ∈ genericNativeCenters S physical globalScale ->
      MeasurableSet (cell center)
  hlocalized : forall center,
    center ∈ genericNativeCenters S physical globalScale ->
    forall x, x ∈ cell center ->
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily S.family physical.ambient)
        projectedTubePairCoefficientDistance globalScale center
        (physical.activeAtPoint x)).Nonempty

namespace GenericNativeBranchCore

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real -> Real} {hfContinuous : Continuous f}

def physicalDatum
    (_D : GenericNativeBranchCore radius iota S physical f hfContinuous) :=
  physical

def centers
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :=
  genericNativeCenters S physical D.globalScale

abbrev PositiveCenter
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :=
  ActualAllCenterPositiveCenter volume D.centers D.cell

/-- The source mass is the actual sum of the measurable cells.  It is not a
caller-selected scalar accompanied by an equality callback. -/
def sourceMass
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :
    ENNReal :=
  ∑ center ∈ D.centers, volume (D.cell center)

theorem sourceMass_eq_sum_cells
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :
    D.sourceMass = ∑ center ∈ D.centers, volume (D.cell center) := by
  rfl

noncomputable def payloadAt
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :
    forall center : D.PositiveCenter,
      ActualPositiveCenterCanonicalPayload volume (D.cell center.1)
        (D.hcellMeasurable center.1
          ((Finset.mem_filter.mp center.2).1))
        S.family physical f D.f1 D.f2 D.outerA D.outerB D.hOuter
          D.hf D.hf1 D.globalScale center.1 D.tangencyExponent :=
  actualAllCenterChosenPayloadAt volume S.family physical f D.f1 D.f2
    D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale D.centers D.cell
    D.tangencyExponent D.logCount D.hradius D.hradiusTangency
    D.hcellMeasurable D.hlocalized D.sourceMass D.sourceMass_eq_sum_cells

def degree
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (center : D.PositiveCenter) : Nat :=
  pyzE2DegreeLower (D.payloadAt center).finalLabel

def high
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :
    Finset D.PositiveCenter :=
  actualAllCenterHigh D.degree D.logCount

def low
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :
    Finset D.PositiveCenter :=
  actualAllCenterLow D.degree D.logCount

abbrev HighCenter
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :=
  {center : D.PositiveCenter // center ∈ D.high}

def positiveBase
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : D.PositiveCenter) :=
  D.cell c.1

theorem positiveBase_measurable
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : D.PositiveCenter) : MeasurableSet (D.positiveBase c) := by
  exact D.hcellMeasurable c.1 ((Finset.mem_filter.mp c.2).1)

def highBase
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : D.HighCenter) :=
  D.positiveBase c.1

theorem highBase_measurable
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : D.HighCenter) : MeasurableSet (D.highBase c) :=
  D.positiveBase_measurable c.1

abbrev HighPayloadCandidate
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : D.HighCenter) :=
  ActualHighPayloadWithNormNonconcentration volume (D.highBase c)
    (D.highBase_measurable c) S.family physical f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
        D.tangencyExponent D.normExponent D.logCount

/-- The literal selected high payload, now independent of the old full-trace
physical datum. -/
noncomputable def chosenHighPayloadAt
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : D.HighCenter) : D.HighPayloadCandidate c :=
  actualHighPayloadOfCanonicalPayload S.family physical f D.f1 D.f2
    D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
    (D.highBase c) (D.highBase_measurable c) D.tangencyExponent
    D.normExponent D.logCount (D.payloadAt c.1)
    ((Finset.mem_filter.mp c.2).2) D.hradius D.hradiusSixteen
    D.hnormExponent
    (fun x hx => ambientCriticalFamily_nonempty_of_localized S.family
      physical D.globalScale c.1.1 x
      (D.hlocalized c.1.1 ((Finset.mem_filter.mp c.1.2).1) x hx))

/-- Exact high/low mass split for an arbitrary projected physical datum. -/
theorem payloadAt_spec
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :
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
  exact actualAllCenterChosenPayloadAt_spec volume S.family physical f
    D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
    D.centers D.cell D.tangencyExponent D.logCount D.hradius
    D.hradiusTangency D.hcellMeasurable D.hlocalized D.sourceMass
    D.sourceMass_eq_sum_cells

end GenericNativeBranchCore

/-- The generic core specialized definitionally to the shading-aware physical
datum. -/
abbrev ShadingAwareNativeBranchCore
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota)
    (f : Real -> Real) (hfContinuous : Continuous f)
    (X : Set (Real × Real)) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) :=
  GenericNativeBranchCore radius iota S
    (shadingAwareProjectedPhysical Y active f hfContinuous.measurable
      X hX I hI)
    f hfContinuous

namespace ShadingAwareNativeBranchCore

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {Y : Shading S.family.bodyFamily} {active : Finset iota}
variable {f : Real -> Real} {hfContinuous : Continuous f}
variable {X : Set (Real × Real)} {hX : MeasurableSet X}
variable {I : Set Real} {hI : MeasurableSet I}

@[simp]
theorem physicalDatum_eq
    (D : ShadingAwareNativeBranchCore S Y active f hfContinuous X hX I hI) :
    D.physicalDatum =
      shadingAwareProjectedPhysical Y active f hfContinuous.measurable
        X hX I hI := by
  rfl

@[simp]
theorem mem_physical_activeAtPoint
    (D : ShadingAwareNativeBranchCore S Y active f hfContinuous X hX I hI)
    (u : Real × Real) (i : iota) :
    i ∈ D.physicalDatum.activeAtPoint u ↔
      i ∈ active ∧ u ∈ X ∧
        0 < shadingFiberMass
          (shadingWindowRestriction Y f hfContinuous.measurable X hX I hI)
            f i u := by
  exact mem_activeAtPoint_shadingAwareProjectedPhysical
    Y active f hfContinuous.measurable X hX I hI u i

/-- The actual WZ2 projected multiplicity is controlled by the active-card
quantity used by the generic Family 7 payload, with constant one. -/
theorem projectedActiveMultiplicity_le_physical_activeAtPoint_card
    (D : ShadingAwareNativeBranchCore S Y active f hfContinuous X hX I hI)
    (hIone : volume I <= 1) (u : Real × Real) (hu : u ∈ X) :
    projectedActiveMultiplicity
        (shadingWindowRestriction Y f hfContinuous.measurable X hX I hI)
        active f u <=
      ((D.physicalDatum.activeAtPoint u).card : ENNReal) := by
  exact projectedActiveMultiplicity_shadingWindowRestriction_le_activeAtPoint_card
    Y active f hfContinuous.measurable X hX I hI hIone u hu

end ShadingAwareNativeBranchCore

#print axioms genericNativeCenters
#print axioms GenericNativeBranchCore
#print axioms GenericNativeBranchCore.sourceMass_eq_sum_cells
#print axioms GenericNativeBranchCore.payloadAt
#print axioms GenericNativeBranchCore.chosenHighPayloadAt
#print axioms GenericNativeBranchCore.payloadAt_spec
#print axioms ShadingAwareNativeBranchCore
#print axioms ShadingAwareNativeBranchCore.physicalDatum_eq
#print axioms ShadingAwareNativeBranchCore.mem_physical_activeAtPoint
#print axioms ShadingAwareNativeBranchCore.projectedActiveMultiplicity_le_physical_activeAtPoint_card

end

end Family8ShadingAwareGenericNativeBranchCoreV2

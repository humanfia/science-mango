import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualCoarseFiberNonconcentrationTransportV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41ActualCoarseFiberNormFamilyProvenanceV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualCoarseFiberNonconcentrationTransportV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Provenance from actual `Y₁` coarse fibres to the canonical norm family

The canonical high payload stores a tube-valued norm family, whereas the
coarse separated-pair producer is indexed by curve labels.  We first pull the
actual norm family back along the literal tube map.  Membership in that
pullback retains both pieces of provenance: the index is in the physical
ambient family and its actual tube belongs to the high payload's canonical
norm family.

For an actual centered-half `Y₁` incidence, the existing carrier certificate
already proves membership in the norm-localized family at its source point.
The localized family is a filter of the canonical critical family at that
same point.  Thus the only cross-record datum still required is transport
from the source point's critical family to the one target canonical family.
An anchor equality with `payload.q` supplies that transport automatically.
-/

section ActualHighPayload

variable {point : Type u} [MeasurableSpace point]
variable {radius : NNReal} {iota : Type v} [DecidableEq iota]
variable {muMeasure : Measure point} {base : Set point}
variable {hbase : MeasurableSet base}
variable {fine : UniformTubeFamily radius iota}
variable {physical : FiniteProjectedShading point iota}
variable {f f1 f2 : Real -> Real} {outerA outerB : Real}
variable {hOuter : outerA <= outerB}
variable {hf : forall z, HasDerivAt f (f1 z) z}
variable {hf1 : forall z, HasDerivAt f1 (f2 z) z}
variable {globalScale : Real} {globalCenter : Tube radius}
variable {tangencyExponent normExponent : Real} {logCount : Nat}

/-- Index pullback of the literal tube-valued canonical norm family. -/
noncomputable def actualHighPayloadNormIndexFamily
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount) : Finset iota := by
  classical
  exact physical.ambient.filter fun i => fine.tubes i ∈ P.normData.family

@[simp]
theorem mem_actualHighPayloadNormIndexFamily_iff
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    {i : iota} :
    i ∈ actualHighPayloadNormIndexFamily P <->
      i ∈ physical.ambient ∧ fine.tubes i ∈ P.normData.family := by
  classical
  simp [actualHighPayloadNormIndexFamily]

/-- Nonemptiness of the tube-valued critical family has an actual ambient
index witness, so its pullback is nonempty without surjectivity assumptions
on the whole tube type. -/
theorem actualHighPayloadNormIndexFamily_nonempty
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount) :
    (actualHighPayloadNormIndexFamily P).Nonempty := by
  obtain ⟨T, hT⟩ := P.normFamily_nonempty
  have hTsource : T ∈ activeTubeImage fine physical.ambient := by
    exact actualProjectedAmbientCriticalFamily_subset fine physical.ambient
      (physical.activeAtPoint P.payload.q) hT
  obtain ⟨i, hi, hTi⟩ :=
    (mem_activeTubeImage_iff fine physical.ambient T).mp hTsource
  refine ⟨i, (mem_actualHighPayloadNormIndexFamily_iff P).mpr ⟨hi, ?_⟩⟩
  change fine.tubes i ∈ actualProjectedAmbientCriticalFamily fine
    physical.ambient (physical.activeAtPoint P.payload.q)
  simpa only [hTi] using hT

/-- The pulled-back index family carries its own genuine canonical
non-concentration maximizer.  Its distance is the actual projected
coefficient distance after applying the literal tube map. -/
noncomputable def actualHighPayloadNormIndexData
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount) :
    CanonicalNormNonconcentrationData iota where
  family := actualHighPayloadNormIndexFamily P
  distance := fun i j =>
    projectedTubePairCoefficientDistance (fine.tubes i) (fine.tubes j)
  delta := radius
  ceiling := 16
  exponent := normExponent
  family_nonempty := actualHighPayloadNormIndexFamily_nonempty P
  self_le_delta := by
    intro i _hi
    rw [projectedTubePairCoefficientDistance_self]
    exact_mod_cast P.radius_pos.le
  delta_pos := by exact_mod_cast P.radius_pos
  delta_le_ceiling := P.radius_le_sixteen
  exponent_nonneg := P.normExponent_nonneg

@[simp]
theorem actualHighPayloadNormIndexData_family
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount) :
    (actualHighPayloadNormIndexData P).family =
      actualHighPayloadNormIndexFamily P := rfl

theorem actualHighPayloadNormIndexData_distance_comm
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (i j : iota) :
    (actualHighPayloadNormIndexData P).distance i j =
      (actualHighPayloadNormIndexData P).distance j i := by
  exact projectedTubePairCoefficientDistance_comm _ _

end ActualHighPayload

/-- A norm-localized family is literally a metric-ball filter of its source
critical family.  This is the scale certificate used below; no membership
callback is introduced. -/
theorem finiteIncidenceNormLocalizedFamilyValue_subset_source
    {index alpha : Type*} [DecidableEq alpha]
    (familyOfActive : Finset index -> Finset alpha)
    (distance : alpha -> alpha -> Real)
    (globalScale : Real) (globalCenter : alpha) (active : Finset index) :
    finiteIncidenceNormLocalizedFamilyValue familyOfActive distance
        globalScale globalCenter active ⊆ familyOfActive active := by
  intro a ha
  simp only [finiteIncidenceNormLocalizedFamilyValue,
    finiteGlobalNormLocalizedFamily, finiteFamilyMetricBall,
    Finset.mem_filter] at ha
  exact ha.1

/-- Any retained-pair membership theorem automatically promotes to the
whole coarse index fibre by unpacking its genuine fine-label witness. -/
theorem _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.coarseCurveIndexFiber_subset_of_retained_source
    {point : Type*} [MeasurableSpace point]
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    {fineLabel : Type*} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (family : Finset iota)
    (hsource : forall i r, D.GoodPair i r -> keep i r -> i ∈ family) :
    D.coarseCurveIndexFiber keep R ⊆ family := by
  intro i hi
  obtain ⟨r, hgood, hkeep, _hcoarse⟩ :=
    (D.mem_coarseCurveIndexFiber_iff keep).mp hi
  exact hsource i r hgood hkeep

section ActualCenteredHalfY1

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable {muMeasure : Measure (Real × Real)}
variable {base : Set (Real × Real)} {hbase : MeasurableSet base}
variable {fine : UniformTubeFamily radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f f1 f2 : Real -> Real} {outerA outerB : Real}
variable {hOuter : outerA <= outerB}
variable {hf : forall z, HasDerivAt f (f1 z) z}
variable {hf1 : forall z, HasDerivAt f1 (f2 z) z}
variable {globalScale : Real} {globalCenter : Tube radius}
variable {tangencyExponent normExponent : Real} {logCount : Nat}

/-- The full actual source/point/scale certificate for one centered-half
Y1 active incidence. Existing Y1 data puts the tube in the localized family
at q; filter containment and cross-point transport put it in the target
canonical family. -/
theorem actualCenteredHalfY1_active_tube_mem_normFamily_of_criticalTransport
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (ceiling threshold : Real) (q : Real × Real) (i : iota)
    (hi : i ∈ (actualProjectedCenteredHalfTangencyY1 base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling tangencyExponent threshold).activeAtPoint q)
    (hcriticalTransport :
      actualProjectedAmbientCriticalFamily fine physical.ambient
          (physical.activeAtPoint q) ⊆ P.normData.family) :
    fine.tubes i ∈ P.normData.family := by
  have hiData := mem_actualProjectedCenteredHalfTangencyY1_data
    base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling tangencyExponent threshold q i hi
  apply hcriticalTransport
  exact finiteIncidenceNormLocalizedFamilyValue_subset_source
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (physical.activeAtPoint q) hiData.2.1

/-- If the actual source point is the selected payload point, critical-family
transport is equality and hence automatic. -/
theorem actualCenteredHalfY1_active_tube_mem_normFamily_of_anchor
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (ceiling threshold : Real) (q : Real × Real) (i : iota)
    (hi : i ∈ (actualProjectedCenteredHalfTangencyY1 base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling tangencyExponent threshold).activeAtPoint q)
    (hanchor : q = P.payload.q) :
    fine.tubes i ∈ P.normData.family := by
  apply actualCenteredHalfY1_active_tube_mem_normFamily_of_criticalTransport
    P ceiling threshold q i hi
  intro T hT
  change T ∈ actualProjectedAmbientCriticalFamily fine physical.ambient
    (physical.activeAtPoint P.payload.q)
  simpa only [hanchor] using hT

/-- A genuine good pair in the actual fine/coarse rectangle data reaches
the index pullback of the target canonical norm family. -/
theorem actualCenteredHalfY1_goodPair_mem_normIndexFamily_of_criticalTransport
    {fineLabel : Type v} [DecidableEq fineLabel]
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (ceiling threshold fineT coarseDelta coarseT : Real)
    (i : iota) (r : fineLabel)
    (hgood : (actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling tangencyExponent threshold fineT
      coarseDelta coarseT).GoodPair i r)
    (hcriticalTransport :
      actualProjectedAmbientCriticalFamily fine physical.ambient
          (physical.activeAtPoint (pointAt r)) ⊆ P.normData.family) :
    i ∈ actualHighPayloadNormIndexFamily P := by
  have hgoodData : i ∈
      (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling tangencyExponent threshold).ambient ∧ r ∈ fineLabels ∧
      pointAt r ∈ (actualProjectedCenteredHalfTangencyY1 base hbase fine
        physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling tangencyExponent threshold).carrier i := by
    simpa only [actualCenteredHalfY1FineCoarseRectangleData,
      y1FineCoarseRectangleData, CoarseRectangleIncidenceData.GoodPair] using
        hgood
  have hiAmbient : i ∈ physical.ambient := by
    simpa only [actualProjectedCenteredHalfTangencyY1,
      finiteIncidenceLocalizedTangencyY1] using hgoodData.1
  have hiY1 : i ∈ (actualProjectedCenteredHalfTangencyY1 base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling tangencyExponent threshold).activeAtPoint (pointAt r) :=
    (FiniteProjectedShading.mem_activeAtPoint _ _ _).mpr
      ⟨hiAmbient, hgoodData.2.2⟩
  refine (mem_actualHighPayloadNormIndexFamily_iff P).mpr
    ⟨hiAmbient, ?_⟩
  exact actualCenteredHalfY1_active_tube_mem_normFamily_of_criticalTransport
    P ceiling threshold (pointAt r) i hiY1 hcriticalTransport

/-- Source anchoring at payload.q is a concrete sufficient provenance field
for every actual good pair. -/
theorem actualCenteredHalfY1_goodPair_mem_normIndexFamily_of_anchor
    {fineLabel : Type v} [DecidableEq fineLabel]
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (ceiling threshold fineT coarseDelta coarseT : Real)
    (i : iota) (r : fineLabel)
    (hgood : (actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling tangencyExponent threshold fineT
      coarseDelta coarseT).GoodPair i r)
    (hanchor : pointAt r = P.payload.q) :
    i ∈ actualHighPayloadNormIndexFamily P := by
  apply actualCenteredHalfY1_goodPair_mem_normIndexFamily_of_criticalTransport
    P fineLabels pointAt ceiling threshold fineT coarseDelta coarseT i r hgood
  intro T hT
  change T ∈ actualProjectedAmbientCriticalFamily fine physical.ambient
    (physical.activeAtPoint P.payload.q)
  simpa only [hanchor] using hT

/-- Coarse-fibre bridge with the minimal semantic missing datum: for each
retained source, transport its pointwise critical family into the one target
canonical family. -/
theorem actualCenteredHalfY1_coarseCurveIndexFiber_subset_normIndexFamily_of_criticalTransport
    {fineLabel : Type v} [DecidableEq fineLabel]
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (ceiling threshold fineT coarseDelta coarseT : Real)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    let D := actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling tangencyExponent threshold fineT
      coarseDelta coarseT
    (forall i r, D.GoodPair i r -> keep i r ->
      actualProjectedAmbientCriticalFamily fine physical.ambient
          (physical.activeAtPoint (pointAt r)) ⊆ P.normData.family) ->
      D.coarseCurveIndexFiber keep R ⊆
        (actualHighPayloadNormIndexData P).family := by
  dsimp only
  intro htransport
  apply CoarseRectangleIncidenceData.coarseCurveIndexFiber_subset_of_retained_source
  intro i r hgood hkeep
  exact actualCenteredHalfY1_goodPair_mem_normIndexFamily_of_criticalTransport
    P fineLabels pointAt ceiling threshold fineT coarseDelta coarseT i r
      hgood (htransport i r hgood hkeep)

/-- Concrete anchor version of the whole index-fibre bridge. -/
theorem actualCenteredHalfY1_coarseCurveIndexFiber_subset_normIndexFamily_of_anchor
    {fineLabel : Type v} [DecidableEq fineLabel]
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (ceiling threshold fineT coarseDelta coarseT : Real)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    let D := actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling tangencyExponent threshold fineT
      coarseDelta coarseT
    (forall i r, D.GoodPair i r -> keep i r ->
      pointAt r = P.payload.q) ->
      D.coarseCurveIndexFiber keep R ⊆
        (actualHighPayloadNormIndexData P).family := by
  dsimp only
  intro hanchor
  apply CoarseRectangleIncidenceData.coarseCurveIndexFiber_subset_of_retained_source
  intro i r hgood hkeep
  exact actualCenteredHalfY1_goodPair_mem_normIndexFamily_of_anchor P
    fineLabels pointAt ceiling threshold fineT coarseDelta coarseT i r hgood
      (hanchor i r hgood hkeep)

/-- The same anchor certificate closes the tube-valued inclusion consumed by
the actual coarse non-concentration transport. -/
theorem actualCenteredHalfY1_coarseTubeFiber_subset_normFamily_of_anchor
    {fineLabel : Type v} [DecidableEq fineLabel]
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (ceiling threshold fineT coarseDelta coarseT : Real)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    let D := actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling tangencyExponent threshold fineT
      coarseDelta coarseT
    (forall i r, D.GoodPair i r -> keep i r ->
      pointAt r = P.payload.q) ->
      D.coarseTubeFiber keep R ⊆ P.normData.family := by
  dsimp only
  intro hanchor T hT
  obtain ⟨i, hi, hTi⟩ :=
    (CoarseRectangleIncidenceData.mem_coarseTubeFiber_iff
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine physical
        fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling tangencyExponent threshold fineT coarseDelta
        coarseT) (keep := keep)).mp hT
  have hiIndex :=
    actualCenteredHalfY1_coarseCurveIndexFiber_subset_normIndexFamily_of_anchor
      P fineLabels pointAt ceiling threshold fineT coarseDelta coarseT keep R
        hanchor hi
  have hiTube := (mem_actualHighPayloadNormIndexFamily_iff P).mp hiIndex |>.2
  rw [← hTi]
  exact hiTube

end ActualCenteredHalfY1

#print axioms actualHighPayloadNormIndexFamily
#print axioms actualHighPayloadNormIndexFamily_nonempty
#print axioms actualHighPayloadNormIndexData
#print axioms finiteIncidenceNormLocalizedFamilyValue_subset_source
#print axioms CoarseRectangleIncidenceData.coarseCurveIndexFiber_subset_of_retained_source
#print axioms actualCenteredHalfY1_active_tube_mem_normFamily_of_criticalTransport
#print axioms actualCenteredHalfY1_goodPair_mem_normIndexFamily_of_criticalTransport
#print axioms actualCenteredHalfY1_coarseCurveIndexFiber_subset_normIndexFamily_of_criticalTransport
#print axioms actualCenteredHalfY1_coarseCurveIndexFiber_subset_normIndexFamily_of_anchor
#print axioms actualCenteredHalfY1_coarseTubeFiber_subset_normFamily_of_anchor

end

end FamilyStickyCinematicL32Prop41ActualCoarseFiberNormFamilyProvenanceV1

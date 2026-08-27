import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualCoarseFiberNormFamilyProvenanceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1

open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
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
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualCoarseFiberNormFamilyProvenanceV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# One global norm-localized family for all actual coarse fibres

The pointwise critical family changes with the source point, so it need not
be contained in the critical family at one selected point.  However the
actual centered-half `Y₁` definition filters every pointwise critical family
by the same global coefficient ball `3 B(globalCenter, globalScale)`.

This module records that common global family at both tube and index level.
Every actual `Y₁` good pair enters it with no source anchor and no cross-point
critical-family nesting premise.
-/

/-- Tube-valued global `3B` family over the literal physical ambient image. -/
def actualGlobalNormTubeFamily
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius) :
    Finset (Tube radius) :=
  finiteGlobalNormLocalizedFamily (activeTubeImage fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter

/-- Index pullback of the same global `3B` family. -/
def actualGlobalNormIndexFamily
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius) : Finset iota :=
  physical.ambient.filter fun i =>
    projectedTubePairCoefficientDistance (fine.tubes i) globalCenter <=
      3 * globalScale

@[simp]
theorem mem_actualGlobalNormIndexFamily_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius) {i : iota} :
    i ∈ actualGlobalNormIndexFamily fine physical globalScale globalCenter <->
      i ∈ physical.ambient ∧
        projectedTubePairCoefficientDistance (fine.tubes i) globalCenter <=
          3 * globalScale := by
  simp [actualGlobalNormIndexFamily]

@[simp]
theorem mem_actualGlobalNormTubeFamily_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius) {T : Tube radius} :
    T ∈ actualGlobalNormTubeFamily fine physical globalScale globalCenter <->
      T ∈ activeTubeImage fine physical.ambient ∧
        projectedTubePairCoefficientDistance T globalCenter <=
          3 * globalScale := by
  simp [actualGlobalNormTubeFamily, finiteGlobalNormLocalizedFamily,
    finiteFamilyMetricBall]

/-- Canonical non-concentration data on the common global index family.
Nonemptiness is explicit because this data can be formed before choosing a
particular good-pair witness. -/
noncomputable def actualGlobalNormIndexData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (exponent : Real)
    (hfamily : (actualGlobalNormIndexFamily fine physical globalScale
      globalCenter).Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent) :
    CanonicalNormNonconcentrationData iota where
  family := actualGlobalNormIndexFamily fine physical globalScale globalCenter
  distance := fun i j =>
    projectedTubePairCoefficientDistance (fine.tubes i) (fine.tubes j)
  delta := radius
  ceiling := 16
  exponent := exponent
  family_nonempty := hfamily
  self_le_delta := by
    intro i _hi
    rw [projectedTubePairCoefficientDistance_self]
    exact_mod_cast hradius.le
  delta_pos := by exact_mod_cast hradius
  delta_le_ceiling := hradiusSixteen
  exponent_nonneg := hexponent

/-- Tube-level version of the same common-global canonical family. -/
noncomputable def actualGlobalNormTubeData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (exponent : Real)
    (hfamily : (actualGlobalNormTubeFamily fine physical globalScale
      globalCenter).Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent) :
    CanonicalNormNonconcentrationData (Tube radius) where
  family := actualGlobalNormTubeFamily fine physical globalScale globalCenter
  distance := projectedTubePairCoefficientDistance
  delta := radius
  ceiling := 16
  exponent := exponent
  family_nonempty := hfamily
  self_le_delta := by
    intro T _hT
    rw [projectedTubePairCoefficientDistance_self]
    exact_mod_cast hradius.le
  delta_pos := by exact_mod_cast hradius
  delta_le_ceiling := hradiusSixteen
  exponent_nonneg := hexponent

theorem actualGlobalNormIndexData_distance_comm
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius) (exponent : Real)
    (hfamily : (actualGlobalNormIndexFamily fine physical globalScale
      globalCenter).Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent) (i j : iota) :
    (actualGlobalNormIndexData fine physical globalScale globalCenter exponent
      hfamily hradius hradiusSixteen hexponent).distance i j =
    (actualGlobalNormIndexData fine physical globalScale globalCenter exponent
      hfamily hradius hradiusSixteen hexponent).distance j i := by
  exact projectedTubePairCoefficientDistance_comm _ _

/-- The common-global-family conclusion extracted from one literal
centered-half `Y₁` active certificate. -/
theorem actualCenteredHalfY1_active_mem_globalNormFamilies
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real) (i : iota)
    (hi : i ∈ (actualProjectedCenteredHalfTangencyY1 base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent threshold).activeAtPoint q) :
    i ∈ actualGlobalNormIndexFamily fine physical globalScale globalCenter ∧
      fine.tubes i ∈
        actualGlobalNormTubeFamily fine physical globalScale globalCenter := by
  have hiData := mem_actualProjectedCenteredHalfTangencyY1_data
    base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold q i hi
  have hiLocalized := hiData.2.1
  simp only [finiteIncidenceNormLocalizedFamilyValue,
    finiteGlobalNormLocalizedFamily, finiteFamilyMetricBall,
    Finset.mem_filter] at hiLocalized
  have hiAmbient : i ∈ physical.ambient :=
    (physical.mem_activeAtPoint q i).mp hiData.1 |>.1
  have hiTubeAmbient : fine.tubes i ∈
      activeTubeImage fine physical.ambient :=
    actualProjectedAmbientCriticalFamily_subset fine physical.ambient
      (physical.activeAtPoint q) hiLocalized.1
  exact ⟨(mem_actualGlobalNormIndexFamily_iff fine physical globalScale
      globalCenter).mpr ⟨hiAmbient, hiLocalized.2⟩,
    (mem_actualGlobalNormTubeFamily_iff fine physical globalScale
      globalCenter).mpr ⟨hiTubeAmbient, hiLocalized.2⟩⟩

/-- A genuine good pair in the actual rectangle data lies in both common
global families, independently of its source point. -/
theorem actualCenteredHalfY1_goodPair_mem_globalNormFamilies
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (i : iota) (r : fineLabel)
    (hgood : (actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT).GoodPair i r) :
    i ∈ actualGlobalNormIndexFamily fine physical globalScale globalCenter ∧
      fine.tubes i ∈
        actualGlobalNormTubeFamily fine physical globalScale globalCenter := by
  have hgoodData : i ∈
      (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent threshold).ambient ∧ r ∈ fineLabels ∧
      pointAt r ∈ (actualProjectedCenteredHalfTangencyY1 base hbase fine
        physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent threshold).carrier i := by
    simpa only [actualCenteredHalfY1FineCoarseRectangleData,
      y1FineCoarseRectangleData, CoarseRectangleIncidenceData.GoodPair] using
        hgood
  have hiAmbient : i ∈ physical.ambient := by
    simpa only [actualProjectedCenteredHalfTangencyY1,
      FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1.finiteIncidenceLocalizedTangencyY1]
      using hgoodData.1
  have hiY1 : i ∈ (actualProjectedCenteredHalfTangencyY1 base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent threshold).activeAtPoint (pointAt r) :=
    (FiniteProjectedShading.mem_activeAtPoint _ _ _).mpr
      ⟨hiAmbient, hgoodData.2.2⟩
  exact actualCenteredHalfY1_active_mem_globalNormFamilies base hbase fine
    physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent threshold (pointAt r) i hiY1

/-- One genuine good pair supplies nonemptiness of both common global
families. -/
theorem actualCenteredHalfY1_globalNormFamilies_nonempty_of_goodPairs
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (hgood :
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine physical
        fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent threshold fineT coarseDelta coarseT
      ).goodPairs.Nonempty) :
    (actualGlobalNormIndexFamily fine physical globalScale
        globalCenter).Nonempty ∧
      (actualGlobalNormTubeFamily fine physical globalScale
        globalCenter).Nonempty := by
  obtain ⟨pair, hpair⟩ := hgood
  have hpairData :=
    (CoarseRectangleIncidenceData.mem_goodPairs_iff
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine physical
        fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent threshold fineT coarseDelta coarseT)
      ).mp hpair
  have hmem := actualCenteredHalfY1_goodPair_mem_globalNormFamilies
    base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB hOuter
    hf hf1 globalScale globalCenter ceiling exponent threshold fineT
    coarseDelta coarseT pair.1 pair.2 hpairData
  exact ⟨⟨pair.1, hmem.1⟩, ⟨fine.tubes pair.1, hmem.2⟩⟩

/-- Every actual coarse index fibre lies in the one common global index
family, with no anchor and no critical-family transport input. -/
theorem actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    let D := actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT
    D.coarseCurveIndexFiber keep R ⊆
      actualGlobalNormIndexFamily fine physical globalScale globalCenter := by
  dsimp only
  apply CoarseRectangleIncidenceData.coarseCurveIndexFiber_subset_of_retained_source
  intro i r hgood _hkeep
  exact (actualCenteredHalfY1_goodPair_mem_globalNormFamilies base hbase fine
    physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
    globalScale globalCenter ceiling exponent threshold fineT coarseDelta
    coarseT i r hgood).1

/-- Tube-valued counterpart, directly consumable by coarse-fibre sampling
and non-concentration adapters. -/
theorem actualCenteredHalfY1_coarseTubeFiber_subset_globalNormTubeFamily
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    let D := actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT
    D.coarseTubeFiber keep R ⊆
      actualGlobalNormTubeFamily fine physical globalScale globalCenter := by
  dsimp only
  intro T hT
  obtain ⟨i, hi, hTi⟩ :=
    (CoarseRectangleIncidenceData.mem_coarseTubeFiber_iff
      (actualCenteredHalfY1FineCoarseRectangleData base hbase fine physical
        fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent threshold fineT coarseDelta coarseT)
      (keep := keep)).mp hT
  have hiGlobal :=
    actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT keep R hi
  have hiData := (mem_actualGlobalNormIndexFamily_iff fine physical
    globalScale globalCenter).mp hiGlobal
  rw [← hTi]
  apply (mem_actualGlobalNormTubeFamily_iff fine physical globalScale
    globalCenter).mpr
  constructor
  · exact (mem_activeTubeImage_iff fine physical.ambient (fine.tubes i)).mpr
      ⟨i, hiData.1, rfl⟩
  · exact hiData.2

/-- Closest G-prime consumer: the common global family carries its own
canonical maximizer, and every automatically retained rich coarse fibre is
inside it without an anchor or a cross-point family premise. -/
theorem exists_actualCenteredHalfY1_globalNorm_GPrime_bucket_separatedPairLower
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (hgood : D.goodPairs.Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent) (ballRadius : Real)
    (hnearRadiusLower : (radius : Real) <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= 16) :
    exists N : CanonicalNormNonconcentrationData iota,
      N.family =
          actualGlobalNormIndexFamily fine physical globalScale globalCenter ∧
      N.delta = (radius : Real) ∧ N.ceiling = 16 ∧
      (forall i j, N.distance i j = N.distance j i) ∧
      ∃ bucket ∈ Finset.range (coarseDegreeBucketLoss D),
        0 < comparableBase bucket ∧
        D.goodPairs.card <= coarseDegreeBucketLoss D *
          (D.retainedGoodPairs
            (coarseDegreeBucketKeep D bucket)).card ∧
        canonicalCoarseSeparatedPairProducedLower
            (automaticCanonicalRichness N ballRadius)
            (automaticCanonicalNearCap N ballRadius)
            (automaticRichRetainedMassLower D
              (automaticCanonicalRichness N ballRadius)
              (2 * comparableBase bucket))
            (2 * comparableBase bucket) <=
          canonicalCoarseRichSeparatedPairCountTotal N D
            (coarseDegreeBucketKeep D bucket) ballRadius := by
  subst D
  let D := actualCenteredHalfY1FineCoarseRectangleData base hbase fine
    physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
    globalScale globalCenter ceiling exponent threshold fineT coarseDelta
    coarseT
  change D.goodPairs.Nonempty at hgood
  have hfamilies :=
    actualCenteredHalfY1_globalNormFamilies_nonempty_of_goodPairs
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT hgood
  let N := actualGlobalNormIndexData fine physical globalScale globalCenter
    exponent hfamilies.1 hradius hradiusSixteen hexponent
  have hsymm : forall i j, N.distance i j = N.distance j i := by
    intro i j
    exact actualGlobalNormIndexData_distance_comm fine physical globalScale
      globalCenter exponent hfamilies.1 hradius hradiusSixteen hexponent i j
  obtain ⟨bucket, hbucket, hbasePos, hselection, hproduced⟩ :=
    exists_actualGPrime_bucket_separatedPairLower N D ballRadius hgood hsymm
      hnearRadiusLower hnearRadiusUpper
  refine ⟨N, rfl, rfl, rfl, hsymm, bucket, hbucket, hbasePos, hselection, ?_⟩
  apply hproduced
  intro R _hR
  exact actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
    base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB hOuter
    hf hf1 globalScale globalCenter ceiling exponent threshold fineT
    coarseDelta coarseT (coarseDegreeBucketKeep D bucket) R

#print axioms actualGlobalNormTubeFamily
#print axioms actualGlobalNormIndexFamily
#print axioms actualGlobalNormIndexData
#print axioms actualGlobalNormTubeData
#print axioms actualGlobalNormIndexData_distance_comm
#print axioms actualCenteredHalfY1_active_mem_globalNormFamilies
#print axioms actualCenteredHalfY1_goodPair_mem_globalNormFamilies
#print axioms actualCenteredHalfY1_globalNormFamilies_nonempty_of_goodPairs
#print axioms actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
#print axioms actualCenteredHalfY1_coarseTubeFiber_subset_globalNormTubeFamily
#print axioms exists_actualCenteredHalfY1_globalNorm_GPrime_bucket_separatedPairLower

end

end FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1

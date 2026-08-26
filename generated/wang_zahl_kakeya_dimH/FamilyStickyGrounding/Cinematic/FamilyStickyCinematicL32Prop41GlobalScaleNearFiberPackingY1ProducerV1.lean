import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
import FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingY1ProducerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Automatic radius separation for the literal centered-half Y1 image

Essential distinctness alone is not used as a coefficient-separation
statement.  Instead, literal Y1 membership places every active tube inside
the already selected projected critical family.  That family was selected at
the tube radius, and hence supplies the required reduced `(a,b,d)` distance
lower bound.
-/

/-- Every concrete tube in the literal centered-half Y1 active image belongs
to the radius-selected projected critical family, so distinct image tubes are
genuinely radius separated in reduced coefficient distance. -/
theorem activeTubeImage_centeredHalfY1_pairwise_radiusSeparated
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real) :
    let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold
    forall T, T ∈ activeTubeImage fine (Y1.activeAtPoint q) ->
      forall U, U ∈ activeTubeImage fine (Y1.activeAtPoint q) -> T ≠ U ->
        (radius : Real) <= projectedTubePairCoefficientDistance T U := by
  dsimp only
  let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold
  intro T hT U hU hTU
  obtain ⟨i, hi, hiEq⟩ :=
    (mem_activeTubeImage_iff fine (Y1.activeAtPoint q) T).mp hT
  obtain ⟨j, hj, hjEq⟩ :=
    (mem_activeTubeImage_iff fine (Y1.activeAtPoint q) U).mp hU
  have hiData := mem_actualProjectedCenteredHalfTangencyY1_data base hbase
    fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter ceiling exponent threshold q i (by
        simpa only [Y1] using hi)
  have hjData := mem_actualProjectedCenteredHalfTangencyY1_data base hbase
    fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter ceiling exponent threshold q j (by
        simpa only [Y1] using hj)
  have hiCritical : fine.tubes i ∈
      actualProjectedAmbientCriticalFamily fine physical.ambient
        (physical.activeAtPoint q) := by
    exact (Finset.mem_filter.mp hiData.2.1).1
  have hjCritical : fine.tubes j ∈
      actualProjectedAmbientCriticalFamily fine physical.ambient
        (physical.activeAtPoint q) := by
    exact (Finset.mem_filter.mp hjData.2.1).1
  rw [actualProjectedAmbientCriticalFamily_eq_activeAtPoint fine physical q]
    at hiCritical hjCritical
  change fine.tubes i ∈ selectedTubes
    (activeTubeImage fine (physical.activeAtPoint q)) (radius : Real) at hiCritical
  change fine.tubes j ∈ selectedTubes
    (activeTubeImage fine (physical.activeAtPoint q)) (radius : Real) at hjCritical
  rw [hiEq] at hiCritical
  rw [hjEq] at hjCritical
  exact selectedTubes_pairwise_separated
    (activeTubeImage fine (physical.activeAtPoint q)) (radius : Real)
      T hiCritical U hjCritical hTU

/-- The concrete positive-centre Y1 used by the payload inherits the same
radius separation without an additional callback. -/
theorem positiveCenterY1_activeTubeImage_pairwise_radiusSeparated
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real) (tangencyLabel : Int) (q : Real × Real) :
    let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      tangencyLabel
    forall T, T ∈ activeTubeImage fine (Y1.activeAtPoint q) ->
      forall U, U ∈ activeTubeImage fine (Y1.activeAtPoint q) -> T ≠ U ->
        (radius : Real) <= projectedTubePairCoefficientDistance T U := by
  dsimp only
  unfold positiveCenterY1
  apply activeTubeImage_centeredHalfY1_pairwise_radiusSeparated

/-- For a real projected-incidence payload, the abstract same-scale cap and
the radius-separation callback are both discharged.  The only new packing
numerical requirement is that the E2 degree lower bound dominate twice the
explicit ratio-dependent floor-grid cap. -/
theorem exists_payload_active_halfFar_from_center_of_explicitPacking
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure (Real × Real))
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent)
    (hradius : 0 < radius) (hglobalScale : 0 < globalScale)
    (hdegree :
      2 * projectedCoefficientPackingCap (radius : Real) globalScale <=
        pyzE2DegreeLower payload.finalLabel)
    (hpair :
      let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
        outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
        payload.tangencyLabel
      Set.Pairwise (Y1.activeAtPoint payload.q : Set iota) (fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j)))
    (center : Tube radius) :
    let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      payload.tangencyLabel
    exists i, i ∈ Y1.activeAtPoint payload.q ∧
      globalScale / 2 <=
        tubePairCoefficientDistance (fine.tubes i) center := by
  apply exists_payload_active_halfFar_from_center_of_radiusPacking
    mu base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter tangencyExponent payload hradius hglobalScale
      hdegree hpair
  exact positiveCenterY1_activeTubeImage_pairwise_radiusSeparated base hbase
    fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter tangencyExponent payload.tangencyLabel payload.q

#print axioms activeTubeImage_centeredHalfY1_pairwise_radiusSeparated
#print axioms positiveCenterY1_activeTubeImage_pairwise_radiusSeparated
#print axioms exists_payload_active_halfFar_from_center_of_explicitPacking

end

end FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingY1ProducerV1

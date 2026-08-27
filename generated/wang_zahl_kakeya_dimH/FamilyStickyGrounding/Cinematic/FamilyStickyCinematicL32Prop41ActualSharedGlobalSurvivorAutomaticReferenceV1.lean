import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
import FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32TraceTangencyScaleUpperV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Automatic common references for perturbed actual survivor families

The analytic core below converts reduced coefficient distance in one exact
`c` slice into the pointwise `C2` ball used by the PYZ counting endpoint.
The outcome specialization then chooses one retained tube as an anchor.
Every unperturbed retained tube lies in the same global `3B` coefficient
ball, hence is within `6 * globalScale` of that anchor.  The individual trace
perturbation changes only the value jet, so its cost is one copy, rather than
five copies, of `|epsilon * weight T|`.
-/

/-- Exact common-`c` coefficient proximity gives a common pointwise `C2`
reference ball with the sharp worst-jet factor five. -/
theorem pairLocalTubeReference_mem_common_c2Ball_of_coefficientDistance_le
    {radius : NNReal} (T C : Tube radius)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho : Real)
    (hcommonC : tubeGraphC T = tubeGraphC C)
    (hdistance : tubePairCoefficientDistance T C <= rho)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    InPointwiseC2BallOn (Icc A B)
      (pairLocalTubeReference C f f1 f2 hfDeriv hf1Deriv A B hAB)
      (pairLocalTubeReference T f f1 f2 hfDeriv hf1Deriv A B hAB)
      (5 * rho) := by
  intro z hz
  have hdistance_nonneg : 0 <= tubePairCoefficientDistance T C :=
    tubePairCoefficientDistance_nonneg T C
  have hrho : 0 <= rho := hdistance_nonneg.trans hdistance
  have hvalueRaw := abs_traceJet0_le_two_coefficientDistance
    (tubePairDeltaA T C) (tubePairDeltaB T C) (tubePairDeltaD T C)
    (f z) z (hparameter z hz) (hfunction z hz)
  have hfirstRaw := abs_traceJet1_le_four_coefficientDistance
    (tubePairDeltaA T C) (tubePairDeltaB T C) (tubePairDeltaD T C)
    (f z) (f1 z) z (hparameter z hz) (hfunction z hz) (hfirst z hz)
  have hsecondRaw := abs_traceJet2_le_five_coefficientDistance
    (tubePairDeltaA T C) (tubePairDeltaB T C) (tubePairDeltaD T C)
    (f1 z) (f2 z) z (hparameter z hz) (hfirst z hz) (hsecond z hz)
  have hvalue :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
        cinematicTraceValue f
          (tubeGraphA C) (tubeGraphB C) (tubeGraphC C) (tubeGraphD C) z| <=
        5 * rho := by
    rw [tube_cinematicTraceValue_sub_eq_traceFunction T C f hcommonC]
    change |FamilyStickyCinematicL32JetSeparationV1.traceJet0
      (tubePairDeltaA T C) (tubePairDeltaB T C) (tubePairDeltaD T C)
        (f z) z| <= 5 * rho
    change coefficientDistance (tubePairDeltaA T C)
      (tubePairDeltaB T C) (tubePairDeltaD T C) <= rho at hdistance
    linarith
  have hfirstJet :
      |tubeCinematicTraceFirstValue T f f1 z -
        tubeCinematicTraceFirstValue C f f1 z| <= 5 * rho := by
    rw [tubeCinematicTraceFirstValue_sub_eq T C f f1 z, hcommonC,
      sub_self, zero_add]
    change |FamilyStickyCinematicL32JetSeparationV1.traceJet1
      (tubePairDeltaB T C) (tubePairDeltaD T C) (f z) (f1 z) z| <=
        5 * rho
    change coefficientDistance (tubePairDeltaA T C)
      (tubePairDeltaB T C) (tubePairDeltaD T C) <= rho at hdistance
    linarith
  have hsecondJet :
      |tubeCinematicTraceSecondValue T f1 f2 z -
        tubeCinematicTraceSecondValue C f1 f2 z| <= 5 * rho := by
    rw [tubeCinematicTraceSecondValue_sub_eq T C f1 f2 z]
    change |FamilyStickyCinematicL32JetSeparationV1.traceJet2
      (tubePairDeltaB T C) (tubePairDeltaD T C) (f1 z) (f2 z) z| <=
        5 * rho
    change coefficientDistance (tubePairDeltaA T C)
      (tubePairDeltaB T C) (tubePairDeltaD T C) <= rho at hdistance
    linarith
  exact ⟨by
    simpa only [pairLocalTubeReference, tubeC2GraphRectangle] using hvalue,
    by simpa only [pairLocalTubeReference, tubeC2GraphRectangle] using hfirstJet,
    by simpa only [pairLocalTubeReference, tubeC2GraphRectangle] using hsecondJet⟩

/-- Translating the first tube costs only `|s|` in the value jet; its first
and second jets are unchanged. -/
theorem pairLocalTubeReference_traceTranslate_mem_common_c2Ball
    {radius : NNReal} (T C : Tube radius) (s : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho : Real)
    (hcommonC : tubeGraphC T = tubeGraphC C)
    (hdistance : tubePairCoefficientDistance T C <= rho)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    InPointwiseC2BallOn (Icc A B)
      (pairLocalTubeReference C f f1 f2 hfDeriv hf1Deriv A B hAB)
      (pairLocalTubeReference (traceTranslateTube T s)
        f f1 f2 hfDeriv hf1Deriv A B hAB)
      (5 * rho + |s|) := by
  have hbase :=
    pairLocalTubeReference_mem_common_c2Ball_of_coefficientDistance_le
      T C f f1 f2 hfDeriv hf1Deriv A B hAB rho hcommonC hdistance
        hparameter hfunction hfirst hsecond
  intro z hz
  have hdata := hbase z hz
  have hdataValue :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
        cinematicTraceValue f
          (tubeGraphA C) (tubeGraphB C) (tubeGraphC C) (tubeGraphD C) z| <=
        5 * rho := by
    simpa only [pairLocalTubeReference, tubeC2GraphRectangle] using hdata.1
  constructor
  · change |cinematicTraceValue f
        (tubeGraphA (traceTranslateTube T s))
        (tubeGraphB (traceTranslateTube T s))
        (tubeGraphC (traceTranslateTube T s))
        (tubeGraphD (traceTranslateTube T s)) z -
      cinematicTraceValue f
        (tubeGraphA C) (tubeGraphB C) (tubeGraphC C) (tubeGraphD C) z| <=
        5 * rho + |s|
    rw [cinematicTraceValue_traceTranslateTube]
    calc
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z + s -
        cinematicTraceValue f
          (tubeGraphA C) (tubeGraphB C) (tubeGraphC C) (tubeGraphD C) z| =
          |(cinematicTraceValue f
              (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
            cinematicTraceValue f
              (tubeGraphA C) (tubeGraphB C) (tubeGraphC C)
                (tubeGraphD C) z) + s| := by ring_nf
      _ <= |cinematicTraceValue f
              (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
            cinematicTraceValue f
              (tubeGraphA C) (tubeGraphB C) (tubeGraphC C)
                (tubeGraphD C) z| + |s| := abs_add_le _ _
      _ <= 5 * rho + |s| := add_le_add hdataValue le_rfl
  constructor
  · have hle := hdata.2.1.trans
        (le_add_of_nonneg_right (abs_nonneg s))
    simpa only [pairLocalTubeReference, tubeC2GraphRectangle,
      tubeCinematicTraceFirstValue, cinematicTraceFirstValue,
      tubeGraphB_traceTranslateTube, tubeGraphC_traceTranslateTube,
      tubeGraphD_traceTranslateTube] using hle
  · have hle := hdata.2.2.trans
        (le_add_of_nonneg_right (abs_nonneg s))
    simpa only [pairLocalTubeReference, tubeC2GraphRectangle,
      tubeCinematicTraceSecondValue, cinematicTraceSecondValue,
      tubeGraphB_traceTranslateTube, tubeGraphD_traceTranslateTube] using hle

/-! ## Slim finite-family anchor package -/

/-- Only the three fields eliminated by the present automation: a retained
anchor, its induced center/domain, and the uniform perturbed reference fact. -/
structure RetainedPairAutomaticReferenceData
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (weight : Tube radius -> Real) (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (externalTolerance t : Real) where
  anchor : Tube radius
  anchor_mem : anchor ∈ retainedPairTubeFamily fiber T U
  center : C2GraphRectangle
  domain : Set Real
  center_eq : center = pairLocalTubeReference anchor f f1 f2
    hfDeriv hf1Deriv A B hAB
  domain_eq : domain = Icc A B
  reference : forall epsilon, 0 < epsilon ->
    epsilon < externalTolerance -> forall V,
    V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB)
        (3 * t)


/-- A nonempty retained family inside one global coefficient `3B` ball
automatically supplies the common reference used by the endpoint assembly. -/
theorem exists_retainedPairAutomaticReferenceData_of_globalNorm
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (hfiber : fiber.Nonempty)
    (T U : alpha -> Tube radius) (weight : Tube radius -> Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B)
    (globalScale : Real) (globalCenter : Tube radius)
    (externalTolerance t : Real)
    (hexternalTolerance : 0 < externalTolerance)
    (hglobal : forall V, V ∈ retainedPairTubeFamily fiber T U ->
      tubePairCoefficientDistance V globalCenter <= 3 * globalScale)
    (hcommonC : forall V, V ∈ retainedPairTubeFamily fiber T U -> forall W,
      W ∈ retainedPairTubeFamily fiber T U -> tubeGraphC V = tubeGraphC W)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hbudget : 30 * globalScale + externalTolerance *
      finiteActualTubeFamilyWeightEnvelope
        (retainedPairTubeFamily fiber T U) weight <= 3 * t) :
    Nonempty (RetainedPairAutomaticReferenceData fiber T U weight
      f f1 f2 hfDeriv hf1Deriv A B hAB externalTolerance t) := by
  obtain ⟨i0, hi0⟩ := hfiber
  have hanchor : T i0 ∈ retainedPairTubeFamily fiber T U :=
    retainedPair_first_mem fiber T U i0 hi0
  refine ⟨{
    anchor := T i0
    anchor_mem := hanchor
    center := pairLocalTubeReference (T i0) f f1 f2
      hfDeriv hf1Deriv A B hAB
    domain := Icc A B
    center_eq := rfl
    domain_eq := rfl
    reference := ?_
  }⟩
  intro epsilon hepsilon hepsilon_lt V hV
  rw [perturbedRetainedTubeFamily_eq_individuallyTracePerturbedTubeFamily]
    at hV
  simp only [individuallyTracePerturbedTubeFamily, Finset.mem_image] at hV
  let X := Classical.choose hV
  have hX : X ∈ retainedPairTubeFamily fiber T U :=
    (Classical.choose_spec hV).1
  have hXV := (Classical.choose_spec hV).2
  rw [← hXV]
  have hdistance : tubePairCoefficientDistance X (T i0) <=
      6 * globalScale :=
    tubePairCoefficientDistance_le_six_mul_of_common_center
      X (T i0) globalCenter (hglobal X hX) (hglobal (T i0) hanchor)
  have hreference := pairLocalTubeReference_traceTranslate_mem_common_c2Ball
    X (T i0) (epsilon * weight X) f f1 f2 hfDeriv hf1Deriv A B hAB
      (6 * globalScale) (hcommonC X hX (T i0) hanchor) hdistance
      hparameter hfunction hfirst hsecond
  have hweight : |weight X| <=
      finiteActualTubeFamilyWeightEnvelope
        (retainedPairTubeFamily fiber T U) weight :=
    abs_weight_le_finiteFamilyWeightEnvelope weight hX
  have hshift : |epsilon * weight X| <= externalTolerance *
      finiteActualTubeFamilyWeightEnvelope
        (retainedPairTubeFamily fiber T U) weight := by
    rw [abs_mul, abs_of_pos hepsilon]
    exact mul_le_mul hepsilon_lt.le hweight (abs_nonneg _)
      hexternalTolerance.le
  have hradius : 5 * (6 * globalScale) + |epsilon * weight X| <=
      3 * t := by
    nlinarith
  intro z hz
  have hdata := hreference z hz
  exact ⟨hdata.1.trans hradius,
    hdata.2.1.trans hradius, hdata.2.2.trans hradius⟩


/-! ## Literal shared-global survivor specialization -/

/-- The tube carried by an actual global-norm index lies in the defining
coefficient ball of radius `3 * globalScale`. -/
theorem actualGlobalNormIndex_tube_distance_le_three_mul
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (j : actualGlobalNormIndexFamily fine physical globalScale globalCenter) :
    tubePairCoefficientDistance (fine.tubes j.1) globalCenter <=
      3 * globalScale := by
  have hj := (mem_actualGlobalNormIndexFamily_iff fine physical globalScale
    globalCenter).mp j.2
  change projectedTubePairCoefficientDistance (fine.tubes j.1)
    globalCenter <= 3 * globalScale
  exact hj.2
#print axioms RetainedPairAutomaticReferenceData
#print axioms exists_retainedPairAutomaticReferenceData_of_globalNorm
#print axioms pairLocalTubeReference_mem_common_c2Ball_of_coefficientDistance_le
#print axioms pairLocalTubeReference_traceTranslate_mem_common_c2Ball

end


end FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceV1

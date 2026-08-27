import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceOutcomeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticReferenceV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceOutcomeV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Automatic reference for the literal shifted selected family

The selected left tubes carry one fixed three-shift translation.  Its
absolute size is charged once to the global coefficient scale.  Exact
fixed-`c` provenance survives this translation, so both the common-`c` and
common-reference fields are generated rather than supplied as callbacks.
-/

/-- The literal common displacement of the selected left family. -/
def actualY1PaperFineSelectedShift
    {radius : NNReal} (globalDelta tGlobal pairScale eta : Real) : Real :=
  eta *
    (actualY1PaperFineChoiceLambda (radius : Real) globalDelta tGlobal
        pairScale *
      actualY1PaperFineChoiceLocalDelta (radius : Real) globalDelta tGlobal
        pairScale)

/-- One scale controlling both untranslated right tubes and translated left
tubes. -/
def actualY1PaperFineSelectedReferenceScale
    {radius : NNReal} (globalScale globalDelta tGlobal pairScale eta : Real) :
    Real :=
  globalScale +
    |actualY1PaperFineSelectedShift (radius := radius) globalDelta tGlobal
      pairScale eta|

/-- Translating the first coefficient changes reduced coefficient distance
by at most the absolute translation. -/
theorem tubePairCoefficientDistance_traceTranslateTube_le_add
    {radius : NNReal} (T C : Tube radius) (s : Real) :
    tubePairCoefficientDistance (traceTranslateTube T s) C <=
      tubePairCoefficientDistance T C + |s| := by
  have ha :
      |(tubeGraphA T + s) - tubeGraphA C| <=
        |tubeGraphA T - tubeGraphA C| + |s| := by
    calc
      |(tubeGraphA T + s) - tubeGraphA C| =
          |(tubeGraphA T - tubeGraphA C) + s| := by ring_nf
      _ <= |tubeGraphA T - tubeGraphA C| + |s| := abs_add_le _ _
  simp only [tubePairCoefficientDistance, coefficientDistance,
    tubePairDeltaA, tubePairDeltaB, tubePairDeltaD,
    tubeGraphA_traceTranslateTube, tubeGraphB_traceTranslateTube,
    tubeGraphD_traceTranslateTube]
  linarith

/-- Flat common-reference data that can fill the `center`, `domain`,
`common_c`, and `reference` fields of either selected automatic package. -/
structure RetainedPairAutomaticCommonReferenceData
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (weight : Tube radius -> Real) (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (externalTolerance t : Real)
    extends RetainedPairAutomaticReferenceData fiber T U weight f f1 f2
      hfDeriv hf1Deriv A B hAB externalTolerance t where
  common_c : forall V, V ∈ retainedPairTubeFamily fiber T U -> forall W,
    W ∈ retainedPairTubeFamily fiber T U -> tubeGraphC V = tubeGraphC W

/-- Every literal selected tube has the exact `c` value supplied by the
upstream fixed-`c` provenance.  The left translation does not change `c`. -/
theorem actualSharedGlobalPaperFineSelectedRetainedTube_fixed_c
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega ->
        fineLabel)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (hDfine : D.fine = fine) (commonC : Real)
    (C : ActualGlobalNormIndexFamilyFixedCProvenance fine physical globalScale
      globalCenter D commonC)
    (V : Tube radius)
    (hV : V ∈ retainedPairTubeFamily P.selected
      (actualSharedGlobalPaperFineSelectedLeftTube fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega
          labelAt f outerA outerB globalDelta tGlobal pairScale P)
      (actualSharedGlobalPaperFineSelectedRightTube fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega
          labelAt f outerA outerB globalDelta tGlobal pairScale P)) :
    tubeGraphC V = commonC := by
  have hfixed : forall i,
      i ∈ actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
        tubeGraphC (fine.tubes i) = commonC := by
    intro i hi
    have htube : D.fine.tubes i = fine.tubes i :=
      congrArg (fun F : UniformTubeFamily radius iota => F.tubes i) hDfine
    exact (congrArg (fun T : Tube radius => tubeGraphC T) htube).symm.trans
      (C.fixed_c i hi)
  simp only [retainedPairTubeFamily, Finset.mem_union,
    Finset.mem_image] at hV
  rcases hV with ⟨a, _ha, rfl⟩ | ⟨a, _ha, rfl⟩
  · simp only [actualSharedGlobalPaperFineSelectedLeftTube,
      tubeGraphC_traceTranslateTube]
    apply hfixed
    exact (survivorLeftHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega a).1.2
  · simp only [actualSharedGlobalPaperFineSelectedRightTube]
    apply hfixed
    exact (survivorRightHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega a).1.2

/-- Every literal selected tube lies in the enlarged global coefficient ball.
The right side costs `3 * globalScale`; the left side additionally costs the
single fixed translation. -/
theorem actualSharedGlobalPaperFineSelectedRetainedTube_distance_le
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega ->
        fineLabel)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (V : Tube radius)
    (hV : V ∈ retainedPairTubeFamily P.selected
      (actualSharedGlobalPaperFineSelectedLeftTube fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega
          labelAt f outerA outerB globalDelta tGlobal pairScale P)
      (actualSharedGlobalPaperFineSelectedRightTube fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega
          labelAt f outerA outerB globalDelta tGlobal pairScale P)) :
    tubePairCoefficientDistance V globalCenter <=
      3 * actualY1PaperFineSelectedReferenceScale
        (radius := radius) globalScale globalDelta tGlobal pairScale P.eta := by
  simp only [retainedPairTubeFamily, Finset.mem_union,
    Finset.mem_image] at hV
  rcases hV with ⟨a, _ha, rfl⟩ | ⟨a, _ha, rfl⟩
  · let j : actualGlobalNormIndexFamily fine physical globalScale
        globalCenter :=
      ⟨actualSharedGlobalSurvivorLeftIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega a,
        (survivorLeftHitWitness mu nu
          (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
            globalCenter D keep rectangles ballRadius left)
          (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
            globalCenter D keep rectangles ballRadius right) omega a).1.2⟩
    have hbase := actualGlobalNormIndex_tube_distance_le_three_mul fine
      physical globalScale globalCenter j
    have htranslate :=
      tubePairCoefficientDistance_traceTranslateTube_le_add
        (fine.tubes j.1) globalCenter
        (actualY1PaperFineSelectedShift (radius := radius) globalDelta tGlobal
          pairScale P.eta)
    have hscale : tubePairCoefficientDistance (fine.tubes j.1) globalCenter +
        |actualY1PaperFineSelectedShift (radius := radius) globalDelta tGlobal
          pairScale P.eta| <=
          3 * (globalScale +
            |actualY1PaperFineSelectedShift (radius := radius) globalDelta
              tGlobal pairScale P.eta|) := by
      have hs := abs_nonneg
        (actualY1PaperFineSelectedShift (radius := radius) globalDelta
          tGlobal pairScale P.eta)
      dsimp only [j] at hbase ⊢
      linarith
    simpa only [actualSharedGlobalPaperFineSelectedLeftTube,
      actualY1PaperFineSelectedShift,
      actualY1PaperFineSelectedReferenceScale] using htranslate.trans hscale
  · let j : actualGlobalNormIndexFamily fine physical globalScale
        globalCenter :=
      ⟨actualSharedGlobalSurvivorRightIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega a,
        (survivorRightHitWitness mu nu
          (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
            globalCenter D keep rectangles ballRadius left)
          (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
            globalCenter D keep rectangles ballRadius right) omega a).1.2⟩
    have hbase := actualGlobalNormIndex_tube_distance_le_three_mul fine
      physical globalScale globalCenter j
    simp only [actualSharedGlobalPaperFineSelectedRightTube,
      actualY1PaperFineSelectedReferenceScale]
    dsimp only [j] at hbase ⊢
    have hs := abs_nonneg
      (actualY1PaperFineSelectedShift (radius := radius) globalDelta tGlobal
        pairScale P.eta)
    linarith

/-- The literal shifted selected family automatically supplies a common
reference and common-`c` data with canonical finite tube weights.

The only new scalar smallness condition is the displayed budget. -/
theorem exists_actualSharedGlobalPaperFineSelectedAutomaticCommonReferenceData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega ->
        fineLabel)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hOuter : outerA <= outerB)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (hDfine : D.fine = fine) (commonC : Real)
    (C : ActualGlobalNormIndexFamilyFixedCProvenance fine physical globalScale
      globalCenter D commonC)
    (externalTolerance : Real) (hexternalTolerance : 0 < externalTolerance)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hbudget :
      30 * actualY1PaperFineSelectedReferenceScale
          (radius := radius) globalScale globalDelta tGlobal pairScale P.eta +
        externalTolerance * finiteActualTubeFamilyWeightEnvelope
          (actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
            globalScale globalCenter D keep rectangles left right ballRadius
              mu nu omega labelAt f outerA outerB globalDelta tGlobal
                pairScale P)
          (finiteActualTubeWeight
            (actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine
              physical globalScale globalCenter D keep rectangles left right
                ballRadius mu nu omega labelAt f outerA outerB globalDelta
                  tGlobal pairScale P)) <= 3 * pairScale) :
    Nonempty (RetainedPairAutomaticCommonReferenceData P.selected
      (actualSharedGlobalPaperFineSelectedLeftTube fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega
          labelAt f outerA outerB globalDelta tGlobal pairScale P)
      (actualSharedGlobalPaperFineSelectedRightTube fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega
          labelAt f outerA outerB globalDelta tGlobal pairScale P)
      (finiteActualTubeWeight
        (actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P))
      f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter externalTolerance
        pairScale) := by
  let T := actualSharedGlobalPaperFineSelectedLeftTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let U := actualSharedGlobalPaperFineSelectedRightTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let family := retainedPairTubeFamily P.selected T U
  let weight := finiteActualTubeWeight family
  have hfixed : forall V, V ∈ family -> tubeGraphC V = commonC := by
    intro V hV
    apply actualSharedGlobalPaperFineSelectedRetainedTube_fixed_c fine
      physical globalScale globalCenter D keep rectangles left right ballRadius
        mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale P
          hDfine commonC C V
    simpa only [family, T, U] using hV
  have hcommon : forall V, V ∈ family -> forall W, W ∈ family ->
      tubeGraphC V = tubeGraphC W := by
    intro V hV W hW
    exact (hfixed V hV).trans (hfixed W hW).symm
  have hglobal : forall V, V ∈ family ->
      tubePairCoefficientDistance V globalCenter <=
        3 * actualY1PaperFineSelectedReferenceScale
          (radius := radius) globalScale globalDelta tGlobal pairScale
            P.eta := by
    intro V hV
    apply actualSharedGlobalPaperFineSelectedRetainedTube_distance_le fine
      physical globalScale globalCenter D keep rectangles left right ballRadius
        mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale P V
    simpa only [family, T, U] using hV
  have hbudget' :
      30 * actualY1PaperFineSelectedReferenceScale
          (radius := radius) globalScale globalDelta tGlobal pairScale P.eta +
        externalTolerance * finiteActualTubeFamilyWeightEnvelope family
          weight <= 3 * pairScale := by
    simpa only [family, weight, T, U,
      actualSharedGlobalPaperFineSelectedRetainedTubeFamily] using hbudget
  obtain ⟨R⟩ := exists_retainedPairAutomaticReferenceData_of_globalNorm
    P.selected P.selected_nonempty T U weight f f1 f2 hfDeriv hf1Deriv
      outerA outerB hOuter
      (actualY1PaperFineSelectedReferenceScale (radius := radius) globalScale
        globalDelta tGlobal pairScale P.eta)
      globalCenter externalTolerance pairScale hexternalTolerance
      (by simpa only [family] using hglobal)
      (by simpa only [family] using hcommon) hparameter hfunction hfirst
        hsecond (by simpa only [family] using hbudget')
  refine ⟨{ toRetainedPairAutomaticReferenceData := R, common_c := ?_ }⟩
  simpa only [family, T, U] using hcommon

#print axioms tubePairCoefficientDistance_traceTranslateTube_le_add
#print axioms RetainedPairAutomaticCommonReferenceData
#print axioms actualSharedGlobalPaperFineSelectedRetainedTube_fixed_c
#print axioms actualSharedGlobalPaperFineSelectedRetainedTube_distance_le
#print axioms exists_actualSharedGlobalPaperFineSelectedAutomaticCommonReferenceData

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticReferenceV1

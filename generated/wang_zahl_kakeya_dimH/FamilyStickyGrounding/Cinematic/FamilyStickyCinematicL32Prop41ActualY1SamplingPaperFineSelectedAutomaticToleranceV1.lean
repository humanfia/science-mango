import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticReferenceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticToleranceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticToleranceV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
open FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticReferenceV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticToleranceV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Automatic tolerance for the literal shifted selected family

The selected shift is one of `-1, 0, 1`, so its reference scale is bounded
by one copy of the unlabelled shift size.  A strict margin at that uniform
scale then canonically produces both a positive external tolerance and the
reference budget required by the automatic common-reference theorem.
-/

/-- Forget the selected shift label at the cost of one absolute shift. -/
theorem actualY1PaperFineSelectedReferenceScale_le_uniform
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
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) :
    actualY1PaperFineSelectedReferenceScale
        (radius := radius) globalScale globalDelta tGlobal pairScale P.eta <=
      globalScale +
        |actualY1PaperFineChoiceLambda
            (radius : Real) globalDelta tGlobal pairScale *
          actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale| := by
  have heta := P.eta_mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heta
  rcases heta with h | h | h
  · simp [actualY1PaperFineSelectedReferenceScale,
      actualY1PaperFineSelectedShift, h]
  · rw [h]
    simp only [actualY1PaperFineSelectedReferenceScale,
      actualY1PaperFineSelectedShift, zero_mul, abs_zero, add_zero]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · simp [actualY1PaperFineSelectedReferenceScale,
      actualY1PaperFineSelectedShift, h]

/-- A single outcome-independent strict margin supplies the selected
automatic common reference with a canonical positive tolerance. -/
theorem exists_actualSharedGlobalPaperFineSelectedAutomaticCommonReferenceData_of_uniformMargin
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
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hmargin :
      30 * (globalScale +
        |actualY1PaperFineChoiceLambda
            (radius : Real) globalDelta tGlobal pairScale *
          actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale|) <
        3 * pairScale) :
    ∃ externalTolerance, 0 < externalTolerance ∧
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
              mu nu omega labelAt f outerA outerB globalDelta tGlobal
                pairScale P))
        f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter externalTolerance
          pairScale) := by
  let family :=
    actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let weight := finiteActualTubeWeight family
  let referenceScale := actualY1PaperFineSelectedReferenceScale
    (radius := radius) globalScale globalDelta tGlobal pairScale P.eta
  have hscale := actualY1PaperFineSelectedReferenceScale_le_uniform fine
    physical globalScale globalCenter D keep rectangles left right ballRadius
      mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  have hmarginSelected : 30 * referenceScale < 3 * pairScale := by
    apply lt_of_le_of_lt _ hmargin
    exact mul_le_mul_of_nonneg_left (by simpa only [referenceScale] using hscale)
      (by norm_num)
  let externalTolerance := finiteActualReferenceAutomaticTolerance
    referenceScale pairScale family weight
  have hexternal : 0 < externalTolerance := by
    exact finiteActualReferenceAutomaticTolerance_pos family weight
      hmarginSelected
  have hbudget : 30 * referenceScale + externalTolerance *
      finiteActualTubeFamilyWeightEnvelope family weight <= 3 * pairScale := by
    exact finiteActualReferenceAutomaticTolerance_budget family weight
      hmarginSelected
  refine ⟨externalTolerance, hexternal, ?_⟩
  apply exists_actualSharedGlobalPaperFineSelectedAutomaticCommonReferenceData
    fine physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta
        tGlobal pairScale hfDeriv hf1Deriv hOuter P hDfine commonC C
        externalTolerance hexternal hparameter hfunction hfirst hsecond
  simpa only [referenceScale, family, weight,
    actualSharedGlobalPaperFineSelectedRetainedTubeFamily] using hbudget

#print axioms actualY1PaperFineSelectedReferenceScale_le_uniform
#print axioms exists_actualSharedGlobalPaperFineSelectedAutomaticCommonReferenceData_of_uniformMargin

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticToleranceV1

import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedDepthProducerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# A uniform logarithmic depth for every selected paper-fine outcome

The literal selected retained tube family is contained in the union of two
images of zero-colour samples.  Each sample has at most the cardinality of
the global normalized ambient family.  Consequently every outcome has at
most twice the ambient number of retained curves, and the canonical
Marcus--Tardos depth is bounded by one fixed logarithmic expression.
-/

/-- One outcome-independent logarithmic depth for the selected branch. -/
def actualSharedGlobalPaperFineSelectedAutomaticDepth
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius) : Real :=
  (Nat.log 2
    (2 * (actualGlobalNormIndexFamily fine physical globalScale
      globalCenter).card) + 1 : Nat)

theorem actualSharedGlobalPaperFineSelectedAutomaticDepth_nonneg
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius) :
    0 <= actualSharedGlobalPaperFineSelectedAutomaticDepth fine physical
      globalScale globalCenter := by
  unfold actualSharedGlobalPaperFineSelectedAutomaticDepth
  positivity

/-- The literal shifted selected retained family has at most twice as many
curves as the normalized ambient family. -/
theorem actualSharedGlobalPaperFineSelectedRetainedTubeFamily_card_le_two_mul_ambient
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
    (actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale P).card <=
      2 * (actualGlobalNormIndexFamily fine physical globalScale
        globalCenter).card := by
  have hselected :=
    actualSharedGlobalPaperFineSelectedRetainedTubeFamily_card_cast_le_load
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
          pairScale P
  have hleft : (zeroColorSample mu omega.1).card <=
      (actualGlobalNormIndexFamily fine physical globalScale
        globalCenter).card := by
    simpa only [Fintype.card_coe] using
      (Finset.card_le_univ (zeroColorSample mu omega.1))
  have hright : (zeroColorSample nu omega.2).card <=
      (actualGlobalNormIndexFamily fine physical globalScale
        globalCenter).card := by
    simpa only [Fintype.card_coe] using
      (Finset.card_le_univ (zeroColorSample nu omega.2))
  have hload : twoSidedZeroColorLoad mu nu omega <=
      (2 * (actualGlobalNormIndexFamily fine physical globalScale
        globalCenter).card : Nat) := by
    unfold twoSidedZeroColorLoad
    exact_mod_cast (Nat.add_le_add hleft hright).trans_eq (two_mul _).symm
  exact_mod_cast hselected.trans hload

/-- The canonical depth of every selected shifted family is controlled by
the single ambient logarithmic depth above. -/
theorem actualSharedGlobalPaperFineSelected_depth_bound_automatic
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
    (canonicalDepth (FirstGenerationCurve
      (actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
        globalScale globalCenter D keep rectangles left right ballRadius mu nu
          omega labelAt f outerA outerB globalDelta tGlobal pairScale P)) :
            Real) <=
      actualSharedGlobalPaperFineSelectedAutomaticDepth fine physical
        globalScale globalCenter := by
  have hcard :=
    actualSharedGlobalPaperFineSelectedRetainedTubeFamily_card_le_two_mul_ambient
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
          pairScale P
  unfold actualSharedGlobalPaperFineSelectedAutomaticDepth canonicalDepth
  norm_cast
  simpa only [FirstGenerationCurve, Fintype.card_coe] using
    (Nat.add_le_add_right (Nat.log_mono_right (b := 2) hcard) 1)

#print axioms actualSharedGlobalPaperFineSelectedAutomaticDepth
#print axioms actualSharedGlobalPaperFineSelectedRetainedTubeFamily_card_le_two_mul_ambient
#print axioms actualSharedGlobalPaperFineSelected_depth_bound_automatic

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedDepthProducerV1

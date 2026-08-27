import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualCoarseFiberNonconcentrationTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualCoarseFiberRandomSamplingV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1

noncomputable section

universe u v w

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Random sampling on literal coarse fibres

This is the actual-data adapter for the finite sampling endpoint.  The
rectangles are a literal finite subfamily, and their left and right neighbour
sets are the actual coarse-curve metric balls inside `F(R)`.  Fibre
provenance supplies containment in the one canonical finite ambient family.
-/

/-- Simultaneous sampling of the two actual coarse-fibre balls.  One outcome
retains at least one eighth of the selected rectangles and has the paper's
sevenfold load bound in terms of the literal canonical ambient family. -/
theorem exists_actualCoarseFiberTube_sample_with_eighth_survival_and_sevenfold_load
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData (Tube radius))
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (hfiberSubset : forall R, R ∈ rectangles ->
      D.coarseTubeFiber keep R ⊆ N.family)
    (hleftCard : forall R, R ∈ rectangles ->
      mu <= (D.coarseTubeMetricBall keep R N.distance
        ballRadius left).card)
    (hrightCard : forall R, R ∈ rectangles ->
      nu <= (D.coarseTubeMetricBall keep R N.distance
        ballRadius right).card) :
    exists omega : (N.family -> Fin mu) × (N.family -> Fin nu),
      ((rectangles.card : Nat) : Real) / 8 <=
          ((twoSidedZeroColorSurvivors mu nu
            (fun R : rectangles =>
              ambientSubtypeRestriction N.family
                (D.coarseTubeMetricBall keep R.1 N.distance
                  ballRadius left))
            (fun R : rectangles =>
              ambientSubtypeRestriction N.family
                (D.coarseTubeMetricBall keep R.1 N.distance
                  ballRadius right)) omega).card : Real) ∧
        twoSidedZeroColorLoad mu nu omega <=
          7 * ((N.family.card : Real) / (mu : Real) +
            (N.family.card : Real) / (nu : Real)) := by
  have hleftSubset : forall R : rectangles,
      D.coarseTubeMetricBall keep R.1 N.distance ballRadius left ⊆
        N.family := by
    intro R T hT
    exact hfiberSubset R.1 R.2
      ((D.mem_coarseTubeMetricBall_iff keep).mp hT).1
  have hrightSubset : forall R : rectangles,
      D.coarseTubeMetricBall keep R.1 N.distance ballRadius right ⊆
        N.family := by
    intro R T hT
    exact hfiberSubset R.1 R.2
      ((D.mem_coarseTubeMetricBall_iff keep).mp hT).1
  have hleftCard' : forall R : rectangles,
      mu <= (D.coarseTubeMetricBall keep R.1 N.distance
        ballRadius left).card := by
    intro R
    exact hleftCard R.1 R.2
  have hrightCard' : forall R : rectangles,
      nu <= (D.coarseTubeMetricBall keep R.1 N.distance
        ballRadius right).card := by
    intro R
    exact hrightCard R.1 R.2
  simpa using
    (exists_ambientSubfamily_sample_with_eighth_survival_and_sevenfold_load
      (Rectangle := rectangles) (alpha := Tube radius) (beta := Tube radius)
      N.family N.family mu nu
      (fun R : rectangles =>
        D.coarseTubeMetricBall keep R.1 N.distance ballRadius left)
      (fun R : rectangles =>
        D.coarseTubeMetricBall keep R.1 N.distance ballRadius right)
      hleftSubset hrightSubset hleftCard' hrightCard')

#print axioms exists_actualCoarseFiberTube_sample_with_eighth_survival_and_sevenfold_load

end

end FamilyStickyCinematicL32Prop41ActualCoarseFiberRandomSamplingV1

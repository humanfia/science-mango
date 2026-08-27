import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualCoarseFiberRandomSamplingV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualCoarseFiberIndexRandomSamplingV1

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

/-- Index-valued actual coarse-fibre sampler.  The ambient family can be the
canonical index pullback of the norm family, while each neighbour ball is
defined using the projected distance of the literal tubes. -/
theorem exists_actualCoarseFiberIndex_sample_with_eighth_survival_and_sevenfold_load
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (tubeDistance : Tube radius -> Tube radius -> Real)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (hfiberSubset : forall R, R ∈ rectangles ->
      D.coarseCurveIndexFiber keep R ⊆ N.family)
    (hleftCard : forall R, R ∈ rectangles ->
      mu <= (D.coarseCurveMetricBall keep R tubeDistance
        ballRadius left).card)
    (hrightCard : forall R, R ∈ rectangles ->
      nu <= (D.coarseCurveMetricBall keep R tubeDistance
        ballRadius right).card) :
    exists omega : (N.family -> Fin mu) × (N.family -> Fin nu),
      ((rectangles.card : Nat) : Real) / 8 <=
          ((twoSidedZeroColorSurvivors mu nu
            (fun R : rectangles =>
              ambientSubtypeRestriction N.family
                (D.coarseCurveMetricBall keep R.1 tubeDistance
                  ballRadius left))
            (fun R : rectangles =>
              ambientSubtypeRestriction N.family
                (D.coarseCurveMetricBall keep R.1 tubeDistance
                  ballRadius right)) omega).card : Real) ∧
        twoSidedZeroColorLoad mu nu omega <=
          7 * ((N.family.card : Real) / (mu : Real) +
            (N.family.card : Real) / (nu : Real)) := by
  have hleftSubset : forall R : rectangles,
      D.coarseCurveMetricBall keep R.1 tubeDistance ballRadius left ⊆
        N.family := by
    intro R i hi
    exact hfiberSubset R.1 R.2
      ((D.mem_coarseCurveMetricBall_iff keep).mp hi).1
  have hrightSubset : forall R : rectangles,
      D.coarseCurveMetricBall keep R.1 tubeDistance ballRadius right ⊆
        N.family := by
    intro R i hi
    exact hfiberSubset R.1 R.2
      ((D.mem_coarseCurveMetricBall_iff keep).mp hi).1
  have hleftCard' : forall R : rectangles,
      mu <= (D.coarseCurveMetricBall keep R.1 tubeDistance
        ballRadius left).card := by
    intro R
    exact hleftCard R.1 R.2
  have hrightCard' : forall R : rectangles,
      nu <= (D.coarseCurveMetricBall keep R.1 tubeDistance
        ballRadius right).card := by
    intro R
    exact hrightCard R.1 R.2
  simpa using
    (exists_ambientSubfamily_sample_with_eighth_survival_and_sevenfold_load
      (Rectangle := rectangles) (alpha := iota) (beta := iota)
      N.family N.family mu nu
      (fun R : rectangles =>
        D.coarseCurveMetricBall keep R.1 tubeDistance ballRadius left)
      (fun R : rectangles =>
        D.coarseCurveMetricBall keep R.1 tubeDistance ballRadius right)
      hleftSubset hrightSubset hleftCard' hrightCard')

#print axioms exists_actualCoarseFiberIndex_sample_with_eighth_survival_and_sevenfold_load

end

end FamilyStickyCinematicL32Prop41ActualCoarseFiberIndexRandomSamplingV1

import Family8Grounding.Family8FiniteRandomRigidMotionAutomaticMeansV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionAutomaticMeanFrostmanProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8RigidCopyPolynomialJohnKatzTaoV1
open Family8FiniteRandomRigidMotionJohnJointSelectionV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8FiniteRandomRigidMotionJohnFrostmanProducerV1
open Family8FiniteRandomRigidMotionAutomaticMeansV1

noncomputable section

/-!
# One-shot Frostman producer with canonical finite means

This version removes the arbitrary conflict/John mean functions, their
nonnegativity hypotheses, and both callbacks bounding finite sums by those
means.  The remaining scale premises are literal inequalities for the exact
uniform finite-grid averages.
-/

theorem exists_finiteRandomRigidMotion_source_averageMultiplicity_le_frostmanRHS_of_finiteMeans
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {motionChoice iota : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (repetitions conflictThreshold : Nat)
    [NeZero repetitions]
    (A johnCoefficient : Real)
    (conflictCap : motionChoice × iota -> Real)
    (hA : 0 <= A)
    (hconflictCap : forall anchor, 0 <= conflictCap anchor)
    (hjohnCoefficient : 0 <= johnCoefficient)
    (hconflictLoadCap : forall anchor g,
      (rigidConflictLoadNat motion D.family anchor g : Real) <=
        conflictCap anchor)
    (hjohnLoadCap : forall q g,
      (rigidCopyPolynomialJohnLoad motion D.family hD.delta_pos q g).toReal <=
        johnCoefficient *
          (volume
            (representativeTestBody delta hD.delta_pos q : Set Space)).toReal)
    (hconflictScale : forall anchor,
      (repetitions : Real) *
          rigidConflictFiniteMean motion D.family anchor <=
        conflictCap anchor)
    (hjohnScale : forall q,
      (repetitions : Real) *
          rigidJohnFiniteMean motion D.family hD.delta_pos q <=
        johnCoefficient *
          (volume
            (representativeTestBody delta hD.delta_pos q : Set Space)).toReal)
    (htailRoom :
      (Fintype.card
          (RigidJohnJointTest delta motionChoice iota hD.delta_pos) : Real) *
          Real.exp (Real.exp 1 - 1) < Real.exp A)
    (hconflictThreshold : forall anchor,
      A * conflictCap anchor <= (conflictThreshold : Real))
    (hball : forall g i,
      (rigidTube (motion g) (D.family.tubes i)).carrier ⊆
        Metric.closedBall (0 : Space) 1)
    (hdelta0 : delta <= delta0)
    (hdensityBudget :
      (delta : ENNReal) ^ eta <=
        D.shading.shadingDensity /
          (conflictThreshold + 1 : Nat))
    (hbaseBudget :
      (conflictThreshold + 1 : Nat) *
          ((ENNReal.ofReal (A * johnCoefficient) *
              johnCatalogueVolumeConstant) *
            volume (unitBallBody : Set Space)) <=
        (delta : ENNReal) ^ (-eta) *
          ((Fintype.card (Fin repetitions × iota) : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2))) :
    exists omega : Fin repetitions -> motionChoice,
      exists selected : Finset (Fin repetitions × iota),
        selected.Nonempty ∧
        Set.Pairwise (selected : Set (Fin repetitions × iota)) (fun a b =>
          EssentiallyDistinct
            ((indexedRigidCopyDatum
              (fun j => motion (omega j)) D).family.tubes a)
            ((indexedRigidCopyDatum
              (fun j => motion (omega j)) D).family.tubes b)) ∧
        D.shading.averageMultiplicity <=
          (conflictThreshold + 1 : Nat) *
            frostmanMultiplicityRHS delta
              (restrictActualTubeDatum
                (indexedRigidCopyDatum (fun j => motion (omega j)) D)
                selected).actualFamilyVolume epsilon beta := by
  apply
    exists_finiteRandomRigidMotion_source_averageMultiplicity_le_frostmanRHS
      hF motion D hD repetitions conflictThreshold A johnCoefficient
      conflictCap (rigidConflictFiniteMean motion D.family)
      (rigidJohnFiniteMean motion D.family hD.delta_pos)
      hA hconflictCap
  · exact rigidConflictFiniteMean_nonneg motion D.family
  · exact hjohnCoefficient
  · exact rigidJohnFiniteMean_nonneg motion D.family hD.delta_pos
  · exact hconflictLoadCap
  · exact hjohnLoadCap
  · intro anchor
    exact (sum_rigidConflictLoad_eq_card_mul_finiteMean
      motion D.family anchor).le
  · intro q
    exact (sum_rigidJohnLoad_eq_card_mul_finiteMean
      motion D.family hD.delta_pos q).le
  · exact hconflictScale
  · exact hjohnScale
  · exact htailRoom
  · exact hconflictThreshold
  · exact hball
  · exact hdelta0
  · exact hdensityBudget
  · exact hbaseBudget

#print axioms exists_finiteRandomRigidMotion_source_averageMultiplicity_le_frostmanRHS_of_finiteMeans

end
end Family8FiniteRandomRigidMotionAutomaticMeanFrostmanProducerV1

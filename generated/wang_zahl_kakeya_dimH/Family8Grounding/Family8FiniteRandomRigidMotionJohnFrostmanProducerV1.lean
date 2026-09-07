import Family8Grounding.Family8FiniteRandomRigidMotionJohnRefinementProducerV1
import Family8Grounding.Family8FiniteRandomRigidMotionFrostmanConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionJohnFrostmanProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8RigidCopyPolynomialJohnKatzTaoV1
open Family8FiniteRandomRigidMotionJohnJointSelectionV1
open Family8FiniteRandomRigidMotionJohnRefinementProducerV1
open Family8FiniteRandomRigidMotionFrostmanConnectorV1

noncomputable section

/-!
# One-shot random rigid refinement to the Frostman source estimate

This connector hides every property of the existentially selected greedy
subfamily needed by the deterministic Frostman bridge.  Its only scalar
inputs beyond the genuine conflict/John random-selection hypotheses are the
two pre-selection density and unit-ball base budgets.
-/

/-- The joint random conflict/John selector, greedy refinement, global
Katz--Tao estimate, density retention, unit-ball normalization, and Frostman
application all hold for one and the same selected actual subfamily. -/
theorem exists_finiteRandomRigidMotion_source_averageMultiplicity_le_frostmanRHS
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
    (conflictCap conflictMean : motionChoice × iota -> Real)
    (johnMean : CatalogueIndex delta hD.delta_pos -> Real)
    (hA : 0 <= A)
    (hconflictCap : forall anchor, 0 <= conflictCap anchor)
    (hconflictMean : forall anchor, 0 <= conflictMean anchor)
    (hjohnCoefficient : 0 <= johnCoefficient)
    (hjohnMean : forall q, 0 <= johnMean q)
    (hconflictLoadCap : forall anchor g,
      (rigidConflictLoadNat motion D.family anchor g : Real) <=
        conflictCap anchor)
    (hjohnLoadCap : forall q g,
      (rigidCopyPolynomialJohnLoad motion D.family hD.delta_pos q g).toReal <=
        johnCoefficient *
          (volume
            (representativeTestBody delta hD.delta_pos q : Set Space)).toReal)
    (hconflictSum : forall anchor,
      (∑ g : motionChoice,
        (rigidConflictLoadNat motion D.family anchor g : Real)) <=
          (Fintype.card motionChoice : Real) * conflictMean anchor)
    (hjohnSum : forall q,
      (∑ g : motionChoice,
        (rigidCopyPolynomialJohnLoad
          motion D.family hD.delta_pos q g).toReal) <=
          (Fintype.card motionChoice : Real) * johnMean q)
    (hconflictScale : forall anchor,
      (repetitions : Real) * conflictMean anchor <= conflictCap anchor)
    (hjohnScale : forall q,
      (repetitions : Real) * johnMean q <=
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
  obtain ⟨omega, selected, hselectedNonempty, hpair, hadmissible,
      hcard, hmass, _hmultiplicity, hKT⟩ :=
    exists_finiteRandomRigidMotion_refinedDatum_isKatzTao
      motion D hD repetitions conflictThreshold A johnCoefficient
      conflictCap conflictMean johnMean hA hconflictCap hconflictMean
      hjohnCoefficient hjohnMean hconflictLoadCap hjohnLoadCap
      hconflictSum hjohnSum hconflictScale hjohnScale htailRoom
      hconflictThreshold hball
  have hsource :=
    source_averageMultiplicity_le_loss_mul_frostmanRHS_of_refinement
      hF (fun j => motion (omega j)) D hD selected
      (conflictThreshold + 1)
      (ENNReal.ofReal (A * johnCoefficient) * johnCatalogueVolumeConstant)
      hdelta0 hadmissible hcard hmass hKT hdensityBudget hbaseBudget
  exact ⟨omega, selected, hselectedNonempty, hpair, hsource⟩

#print axioms exists_finiteRandomRigidMotion_source_averageMultiplicity_le_frostmanRHS

end
end Family8FiniteRandomRigidMotionJohnFrostmanProducerV1

import Family8Grounding.Family8FiniteRigidMotionOrthogonalNormalizedChoiceBudgetV3
import Family8Grounding.Family8FiniteRigidMotionOrthogonalNormalizedSupportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalNormalizedChernoffV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open FamilyStickyRandomModelTubeCollisionGridV1
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceBudgetV3

noncomputable section

/-!
# Direct Chernoff selector for the literal orthogonal catalogue

The catalogue budget and exact normalized mean discharge all local geometric
choice premises of the existing finite Chernoff layer. The only remaining
inputs here are its two transparent scalar inequalities: repetitions times
the exact mean fit below the trivial one-choice load cap, and the finite test
catalogue fits inside the chosen exponential tail room.
-/

variable {translation iota testIndex : Type}
  [Fintype translation] [Nonempty translation] [DecidableEq translation]
  [Fintype iota] [DecidableEq iota]
  [Fintype testIndex] [DecidableEq testIndex]
  {delta : NNReal}

theorem normalizedRigidHundredLoadNat_le_sourceCard
    (D : ActualTubeDatum delta iota)
    {motionChoice : Type}
    (motion : motionChoice -> RigidMotion)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) (g : motionChoice) :
    (normalizedRigidHundredLoadNat motion D testTube K g : Real) ≤
      (Fintype.card iota : Real) := by
  classical
  have hnat :
      normalizedRigidHundredLoadNat motion D testTube K g ≤
        Fintype.card iota := by
    unfold normalizedRigidHundredLoadNat
    simpa only [Finset.card_univ] using
      Finset.card_filter_le (Finset.univ : Finset iota)
        (fun i =>
          (eighthNormalizedTube
            (rigidTube (motion g) (D.family.tubes i))).carrier ⊆
              (hundredTube (testTube K)).carrier)
  exact_mod_cast hnat

theorem exists_sampledOrthogonalTranslationTuple_all_normalizedHundredLoads_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (henlargedHalf :
      enlargedHundredDirectionCap (delta / 8) ≤ 1 / 2)
    (n : Nat) (hn : 0 < n)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest iota
              (HundredDirectionChoice
                (delta / 8) (normalizedRadius_pos hD)))) : Real) ≤
        (n : Real) *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2)
    (rawTranslation : translation -> Space)
    (testTube : testIndex -> Tube (delta / 8))
    (activeTests : Finset testIndex)
    (repetitions : Nat) (A : Real)
    (hscale :
      (repetitions : Real) *
          orthogonalCatalogueMean translation D hD n ≤
        (Fintype.card iota : Real))
    (htailRoom :
      (activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
        Real.exp A) :
    exists omega : Fin repetitions ->
        OrthogonalTranslationChoice translation D hD n,
      forall K, K ∈ activeTests ->
        (∑ j,
          (normalizedRigidHundredLoadNat
            (sampledOrthogonalTranslationMotion D hD n rawTranslation)
            D testTube K (omega j) : Real)) ≤
          A * (Fintype.card iota : Real) := by
  let motion :=
    sampledOrthogonalTranslationMotion D hD n rawTranslation
  let budget : testIndex -> Nat := fun _ =>
    orthogonalCatalogueChoiceBudget translation D hD n
  let cap : testIndex -> Real := fun _ => Fintype.card iota
  let mean : testIndex -> Real := fun _ =>
    orthogonalCatalogueMean translation D hD n
  have hcardPos := card_orthogonalTranslationChoice_pos
    (translation := translation) D hD n hn
  let _ : Nonempty (OrthogonalTranslationChoice translation D hD n) :=
    Fintype.card_pos_iff.mp hcardPos
  apply exists_rigidMotionTuple_all_normalizedHundredLoads_le
    motion D testTube activeTests budget repetitions cap mean A
  · intro K _hK
    dsimp only [cap]
    positivity
  · intro K _hK
    dsimp only [mean]
    unfold orthogonalCatalogueMean
    positivity
  · intro K _hK g
    dsimp only [cap, motion]
    exact normalizedRigidHundredLoadNat_le_sourceCard
      D (sampledOrthogonalTranslationMotion D hD n rawTranslation)
      testTube K g
  · intro K _hK i
    dsimp only [budget, motion]
    exact normalizedRigidHundredChoiceCount_le_choiceBudget
      D hD henlargedHalf n hround rawTranslation testTube K i
  · intro K _hK
    dsimp only [budget, mean, motion]
    exact orthogonalCatalogue_choiceBudget_balance
      (translation := translation) D hD n hn
  · intro K _hK
    simpa only [cap, mean] using hscale
  · exact htailRoom

#print axioms normalizedRigidHundredLoadNat_le_sourceCard
#print axioms
  exists_sampledOrthogonalTranslationTuple_all_normalizedHundredLoads_le

end
end Family8FiniteRigidMotionOrthogonalNormalizedChernoffV4

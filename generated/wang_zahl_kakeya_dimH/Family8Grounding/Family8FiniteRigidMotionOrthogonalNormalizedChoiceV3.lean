import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationCatalogueV2
import Family8Grounding.Family8FiniteRigidMotionOrthogonalNormalizationV4
import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictTailV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalTranslationCatalogueV2
open Family8FiniteRigidMotionOrthogonalNormalizationV4

noncomputable section

/-!
# The literal orthogonal catalogue discharges the normalized choice count

Apply the sampled rotation and an arbitrary raw translation before the
paper's eighth normalization. The exact normalization identity turns the
result into the already sampled hundred-containment event, with translation
divided by eight. Thus the actual finite-motion choice count inherits the
quadratic catalogue bound without an abstract probability premise.
-/

variable {translation iota testIndex : Type}
  [Fintype translation] [DecidableEq translation]
  [Fintype iota] [DecidableEq iota]
  {delta : NNReal}

theorem normalizedRadius_pos
    {D : ActualTubeDatum delta iota} (hD : D.IsAdmissible) :
    0 < delta / 8 :=
  div_pos hD.delta_pos (by norm_num)

def normalizedSourceTube
    (D : ActualTubeDatum delta iota) (i : iota) : Tube (delta / 8) :=
  eighthNormalizedTube (D.family.tubes i)

abbrev OrthogonalTranslationChoice
    (translation : Type)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat) :=
  HundredRigidSample translation (normalizedSourceTube D)
    (normalizedRadius_pos hD) n

def sampledOrthogonalTranslationMotion
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (rawTranslation : translation -> Space)
    (g : OrthogonalTranslationChoice translation D hD n) : RigidMotion :=
  Family8FiniteRigidMotionOrthogonalTranslationV2.orthogonalTranslationRigidMotion
    (sampledHundredOrthogonal
      (normalizedSourceTube D) (normalizedRadius_pos hD) g.2)
    (rawTranslation g.1)

theorem normalizedRigidHundredChoiceCount_eq_catalogueCard
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (rawTranslation : translation -> Space)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) (i : iota) :
    normalizedRigidHundredChoiceCount
        (sampledOrthogonalTranslationMotion D hD n rawTranslation)
        D testTube K i =
      (sampledHundredRigidContainmentFinset
        (normalizedSourceTube D) (normalizedRadius_pos hD) n
        (fun t => eighthTranslationVector (rawTranslation t))
        i (testTube K)).card := by
  classical
  unfold normalizedRigidHundredChoiceCount
    sampledHundredRigidContainmentFinset
  apply congrArg Finset.card
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold sampledOrthogonalTranslationMotion normalizedSourceTube
  rw [eighthNormalizedTube_orthogonalTranslation]
  rfl

theorem normalizedRigidHundredChoiceCount_le_catalogue
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (henlargedHalf :
      enlargedHundredDirectionCap (delta / 8) ≤ 1 / 2)
    (n : Nat)
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
    (K : testIndex) (i : iota) :
    (normalizedRigidHundredChoiceCount
        (sampledOrthogonalTranslationMotion D hD n rawTranslation)
        D testTube K i : Real) ≤
      (Fintype.card
          (OrthogonalTranslationChoice translation D hD n) : Real) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2) := by
  rw [normalizedRigidHundredChoiceCount_eq_catalogueCard]
  exact card_sampledHundredRigidContainmentFinset_le
    (normalizedSourceTube D) (normalizedRadius_pos hD)
    henlargedHalf n hround
    (fun t => eighthTranslationVector (rawTranslation t)) i (testTube K)

#print axioms normalizedRadius_pos
#print axioms normalizedRigidHundredChoiceCount_eq_catalogueCard
#print axioms normalizedRigidHundredChoiceCount_le_catalogue

end
end Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3

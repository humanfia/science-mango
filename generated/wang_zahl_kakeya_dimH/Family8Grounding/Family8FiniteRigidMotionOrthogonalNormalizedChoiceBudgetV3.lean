import Family8Grounding.Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalNormalizedChoiceBudgetV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalTranslationCatalogueV2
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3

noncomputable section

/-!
# Integer choice budget and exact finite-law mean

Round the proved relative catalogue cap upward once. The resulting natural
number automatically bounds every actual normalized one-tube choice count.
Dividing its total source contribution by the literal catalogue cardinality
then gives the exact mean required by the finite Chernoff interface.
-/

variable {translation iota testIndex : Type}
  [Fintype translation] [DecidableEq translation]
  [Fintype iota] [DecidableEq iota]
  {delta : NNReal}

def orthogonalCatalogueRelativeCap (delta : NNReal) : Real :=
  11 * (enlargedHundredDirectionCap delta : Real) ^ 2

def orthogonalCatalogueChoiceBudget
    (translation : Type) [Fintype translation]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (n : Nat) : Nat :=
  Nat.ceil
    ((Fintype.card
        (OrthogonalTranslationChoice translation D hD n) : Real) *
      orthogonalCatalogueRelativeCap (delta / 8))

theorem card_orthogonalTranslationChoice_pos
    [Nonempty translation]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (n : Nat) (hn : 0 < n) :
    0 < Fintype.card
      (OrthogonalTranslationChoice translation D hD n) := by
  have htranslation : 0 < Fintype.card translation :=
    Fintype.card_pos_iff.mpr inferInstance
  have hscale := scale_le_card_orthogonalPatternSample
    (Family8FiniteRigidMotionOrthogonalHundredCatalogueV2.sourceTubeDirection
      (normalizedSourceTube D))
    (Family8FiniteRigidMotionOrthogonalHundredCatalogueV2.hundredNetDirection
      (delta / 8) (normalizedRadius_pos hD))
    (enlargedHundredDirectionCap (delta / 8)) n
  have hrotation :
      0 < Fintype.card
        (HundredOrthogonalSample
          (normalizedSourceTube D) (normalizedRadius_pos hD) n) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.cast_pos.mpr hn) hscale)
  change 0 < Fintype.card
    (translation × HundredOrthogonalSample
      (normalizedSourceTube D) (normalizedRadius_pos hD) n)
  rw [Fintype.card_prod]
  exact Nat.mul_pos htranslation hrotation

theorem normalizedRigidHundredChoiceCount_le_choiceBudget
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
    normalizedRigidHundredChoiceCount
        (sampledOrthogonalTranslationMotion D hD n rawTranslation)
        D testTube K i ≤
      orthogonalCatalogueChoiceBudget translation D hD n := by
  have hcount := normalizedRigidHundredChoiceCount_le_catalogue
    D hD henlargedHalf n hround rawTranslation testTube K i
  have hceil :
      (Fintype.card
          (OrthogonalTranslationChoice translation D hD n) : Real) *
          orthogonalCatalogueRelativeCap (delta / 8) ≤
        (orthogonalCatalogueChoiceBudget translation D hD n : Real) := by
    exact Nat.le_ceil _
  exact_mod_cast hcount.trans hceil

def orthogonalCatalogueMean
    (translation : Type) [Fintype translation]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (n : Nat) : Real :=
  (Fintype.card iota : Real) *
      (orthogonalCatalogueChoiceBudget translation D hD n : Real) /
    (Fintype.card
      (OrthogonalTranslationChoice translation D hD n) : Real)

theorem orthogonalCatalogue_choiceBudget_balance
    [Nonempty translation]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (n : Nat) (hn : 0 < n) :
    (Fintype.card iota : Real) *
        (orthogonalCatalogueChoiceBudget translation D hD n : Real) ≤
      (Fintype.card
          (OrthogonalTranslationChoice translation D hD n) : Real) *
        orthogonalCatalogueMean translation D hD n := by
  have hcardPos :=
    card_orthogonalTranslationChoice_pos
      (translation := translation) D hD n hn
  have hcardNe :
      (Fintype.card
        (OrthogonalTranslationChoice translation D hD n) : Real) ≠ 0 := by
    exact_mod_cast hcardPos.ne'
  unfold orthogonalCatalogueMean
  field_simp [hcardNe]
  exact le_rfl

#print axioms card_orthogonalTranslationChoice_pos
#print axioms normalizedRigidHundredChoiceCount_le_choiceBudget
#print axioms orthogonalCatalogue_choiceBudget_balance

end
end Family8FiniteRigidMotionOrthogonalNormalizedChoiceBudgetV3

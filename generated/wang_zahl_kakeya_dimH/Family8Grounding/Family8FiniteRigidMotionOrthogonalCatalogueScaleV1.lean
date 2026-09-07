import Family8Grounding.Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalCatalogueScaleV1

open LeanEval.Analysis.WangZahlKakeya
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3

noncomputable section

/-!
# Automatic integer scale for the incidence-pattern catalogue

Choose the rotation sampling scale as the natural ceiling of the finite
pattern cardinal divided by the positive squared cap radius. This removes the
last rounding premise from the literal orthogonal catalogue construction.
-/

variable {iota : Type} [Fintype iota] [DecidableEq iota]
  {delta : NNReal}

def orthogonalCatalogueScale
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Nat :=
  Nat.ceil
    ((Fintype.card
        (Pattern
          (OrthogonalCapTest iota
            (HundredDirectionChoice
              (delta / 8) (normalizedRadius_pos hD)))) : Real) /
      (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2)

theorem orthogonalCatalogueScale_pos
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    0 < orthogonalCatalogueScale D hD := by
  unfold orthogonalCatalogueScale
  rw [Nat.ceil_pos]
  have hpattern :
      0 < Fintype.card
        (Pattern
          (OrthogonalCapTest iota
            (HundredDirectionChoice
              (delta / 8) (normalizedRadius_pos hD)))) :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcap :
      0 < (enlargedHundredDirectionCap (delta / 8) : Real) := by
    exact_mod_cast enlargedHundredDirectionCap_pos
      (normalizedRadius_pos hD)
  exact div_pos (by exact_mod_cast hpattern) (sq_pos_of_pos hcap)

theorem orthogonalCatalogueScale_rounding
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (Fintype.card
        (Pattern
          (OrthogonalCapTest iota
            (HundredDirectionChoice
              (delta / 8) (normalizedRadius_pos hD)))) : Real) ≤
      (orthogonalCatalogueScale D hD : Real) *
        (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2 := by
  let patternCard : Real :=
    Fintype.card
      (Pattern
        (OrthogonalCapTest iota
          (HundredDirectionChoice
            (delta / 8) (normalizedRadius_pos hD))))
  let capSq : Real :=
    (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2
  have hcap :
      0 < (enlargedHundredDirectionCap (delta / 8) : Real) := by
    exact_mod_cast enlargedHundredDirectionCap_pos
      (normalizedRadius_pos hD)
  have hcapSq : 0 < capSq := by
    dsimp only [capSq]
    exact sq_pos_of_pos hcap
  have hceil :
      patternCard / capSq ≤
        (orthogonalCatalogueScale D hD : Real) := by
    exact Nat.le_ceil _
  calc
    (Fintype.card
        (Pattern
          (OrthogonalCapTest iota
            (HundredDirectionChoice
              (delta / 8) (normalizedRadius_pos hD)))) : Real) =
        patternCard := rfl
    _ = (patternCard / capSq) * capSq := by
      field_simp [hcapSq.ne']
    _ ≤ (orthogonalCatalogueScale D hD : Real) * capSq :=
      mul_le_mul_of_nonneg_right hceil hcapSq.le
    _ = (orthogonalCatalogueScale D hD : Real) *
        (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2 := rfl

#print axioms orthogonalCatalogueScale_pos
#print axioms orthogonalCatalogueScale_rounding

end
end Family8FiniteRigidMotionOrthogonalCatalogueScaleV1

import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1

open LeanEval.Analysis.WangZahlKakeya
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1

noncomputable section

/-!
# Scale-only automatic integer scale for the orthogonal catalogue

The orthogonal incidence-pattern catalogue needs only positivity of the
normalized radius.  This version chooses the same natural ceiling as
`Family8FiniteRigidMotionOrthogonalCatalogueScaleV1`, but obtains that
positivity from `0 < delta` through the scale-only product law.  It assumes
no admissibility, unit-ball support, or essential-distinctness property of
the source datum.
-/

variable {iota : Type} [Fintype iota] [DecidableEq iota]
  {delta : NNReal}

/-- The natural ceiling of the finite pattern cardinal divided by the
squared angular-cap radius, using only `0 < delta`. -/
def scaleOnlyOrthogonalCatalogueScale
    (_D : ActualTubeDatum delta iota) (hdelta : 0 < delta) : Nat :=
  Nat.ceil
    ((Fintype.card
        (Pattern
          (OrthogonalCapTest iota
            (HundredDirectionChoice
              (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta)))) : Real) /
      (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2)

/-- The automatic scale is a positive natural number. -/
theorem scaleOnlyOrthogonalCatalogueScale_pos
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) :
    0 < scaleOnlyOrthogonalCatalogueScale D hdelta := by
  unfold scaleOnlyOrthogonalCatalogueScale
  rw [Nat.ceil_pos]
  have hpattern :
      0 < Fintype.card
        (Pattern
          (OrthogonalCapTest iota
            (HundredDirectionChoice
              (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta)))) :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcap :
      0 < (enlargedHundredDirectionCap (delta / 8) : Real) := by
    exact_mod_cast enlargedHundredDirectionCap_pos
      (scaleOnlyNormalizedRadiusPos hdelta)
  exact div_pos (by exact_mod_cast hpattern) (sq_pos_of_pos hcap)

/-- Exact rounding inequality supplied by the ceiling choice. -/
theorem scaleOnlyOrthogonalCatalogueScale_rounding
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) :
    (Fintype.card
        (Pattern
          (OrthogonalCapTest iota
            (HundredDirectionChoice
              (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta)))) : Real) <=
      (scaleOnlyOrthogonalCatalogueScale D hdelta : Real) *
        (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2 := by
  let patternCard : Real :=
    Fintype.card
      (Pattern
        (OrthogonalCapTest iota
          (HundredDirectionChoice
            (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta))))
  let capSq : Real :=
    (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2
  have hcap :
      0 < (enlargedHundredDirectionCap (delta / 8) : Real) := by
    exact_mod_cast enlargedHundredDirectionCap_pos
      (scaleOnlyNormalizedRadiusPos hdelta)
  have hcapSq : 0 < capSq := by
    dsimp only [capSq]
    exact sq_pos_of_pos hcap
  have hceil :
      patternCard / capSq <=
        (scaleOnlyOrthogonalCatalogueScale D hdelta : Real) := by
    exact Nat.le_ceil _
  calc
    (Fintype.card
        (Pattern
          (OrthogonalCapTest iota
            (HundredDirectionChoice
              (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta)))) : Real) =
        patternCard := rfl
    _ = (patternCard / capSq) * capSq := by
      field_simp [hcapSq.ne']
    _ <= (scaleOnlyOrthogonalCatalogueScale D hdelta : Real) * capSq :=
      mul_le_mul_of_nonneg_right hceil hcapSq.le
    _ = (scaleOnlyOrthogonalCatalogueScale D hdelta : Real) *
        (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2 := rfl

#print axioms scaleOnlyOrthogonalCatalogueScale_pos
#print axioms scaleOnlyOrthogonalCatalogueScale_rounding

end
end Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1

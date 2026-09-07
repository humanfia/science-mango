import Family8Grounding.Family8FiniteRigidMotionOrthogonalNormalizedChernoffV4
import Family8Grounding.Family8FiniteRigidMotionOrthogonalCatalogueScaleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalAutomaticChernoffV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceBudgetV3
open Family8FiniteRigidMotionOrthogonalNormalizedChernoffV4
open Family8FiniteRigidMotionOrthogonalCatalogueScaleV1

noncomputable section

/-!
# Chernoff selection at the automatic orthogonal catalogue scale

Specialize the direct selector to the canonical ceiling scale. Positivity and
the finite-pattern rounding inequality are now theorems, so no sampling-scale
or rounding callback remains.
-/

variable {translation iota testIndex : Type}
  [Fintype translation] [Nonempty translation] [DecidableEq translation]
  [Fintype iota] [DecidableEq iota]
  [Fintype testIndex] [DecidableEq testIndex]
  {delta : NNReal}

theorem exists_automaticOrthogonalTranslationTuple_all_normalizedHundredLoads_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (henlargedHalf :
      enlargedHundredDirectionCap (delta / 8) ≤ 1 / 2)
    (rawTranslation : translation -> Space)
    (testTube : testIndex -> Tube (delta / 8))
    (activeTests : Finset testIndex)
    (repetitions : Nat) (A : Real)
    (hscale :
      (repetitions : Real) *
          orthogonalCatalogueMean translation D hD
            (orthogonalCatalogueScale D hD) ≤
        (Fintype.card iota : Real))
    (htailRoom :
      (activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
        Real.exp A) :
    exists omega : Fin repetitions ->
        OrthogonalTranslationChoice translation D hD
          (orthogonalCatalogueScale D hD),
      forall K, K ∈ activeTests ->
        (∑ j,
          (normalizedRigidHundredLoadNat
            (sampledOrthogonalTranslationMotion D hD
              (orthogonalCatalogueScale D hD) rawTranslation)
            D testTube K (omega j) : Real)) ≤
          A * (Fintype.card iota : Real) := by
  exact
    exists_sampledOrthogonalTranslationTuple_all_normalizedHundredLoads_le
      D hD henlargedHalf
      (orthogonalCatalogueScale D hD)
      (orthogonalCatalogueScale_pos D hD)
      (orthogonalCatalogueScale_rounding D hD)
      rawTranslation testTube activeTests repetitions A hscale htailRoom

#print axioms
  exists_automaticOrthogonalTranslationTuple_all_normalizedHundredLoads_le

end
end Family8FiniteRigidMotionOrthogonalAutomaticChernoffV2

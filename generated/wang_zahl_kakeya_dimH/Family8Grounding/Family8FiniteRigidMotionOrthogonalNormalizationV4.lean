import Family8Grounding.Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalNormalizationV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalActionV2
open Family8FiniteRigidMotionOrthogonalTranslationV2

noncomputable section

/-!
# Exact normalization of a rotation-plus-translation

The centered eighth normalization commutes with the orthogonal part and
divides only the translation vector by eight. This is the literal bridge
from the finite orthogonal catalogue to the normalized hundred-containment
choice count used by the paper-strength Chernoff layer.
-/

theorem eighthNormalizedTube_orthogonalTranslation
    {delta : NNReal} (T : Tube delta)
    (U : OrthogonalThree) (t : Space) :
    eighthNormalizedTube
        (rigidTube (orthogonalTranslationRigidMotion U t) T) =
      rigidTube
        (orthogonalTranslationRigidMotion U (eighthTranslationVector t))
        (eighthNormalizedTube T) := by
  rw [Tube.mk.injEq, UnitSegment.mk.injEq]
  constructor
  · simp only [eighthNormalizedTube_axis, eighthNormalizedAxis_base,
      rigidTube_axis, rigidUnitSegment_base, rigidUnitSegment_direction,
      orthogonalTranslationRigidMotion_apply,
      orthogonalTranslationRigidMotion_linear, tubeAxisMidpoint,
      eighthTranslationVector, eighthDilationPoint,
      orthogonalThreeLinearIsometryEquiv_apply, map_add, map_sub, map_smul]
    module
  · simp only [eighthNormalizedTube_axis, eighthNormalizedAxis_direction,
      rigidTube_axis, rigidUnitSegment_direction,
      orthogonalTranslationRigidMotion_linear]

#print axioms eighthNormalizedTube_orthogonalTranslation

end
end Family8FiniteRigidMotionOrthogonalNormalizationV4

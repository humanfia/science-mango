import Family8Grounding.Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
import Family8Grounding.Family8FiniteRandomRigidMotionIncidenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionIncidenceV1
open FamilyStickyActualTubeTranslationV1

noncomputable section

/-!
# Exact translation transport through the B2 normalization

The centered `1/8` normalization is affine, while the subsequent unit-axis
extension leaves directions unchanged.  Consequently translating the raw
tube by `v` translates its normalized tube by exactly `v/8`.  This identity
is the algebraic bridge which lets the finite rigid-motion choice count reuse
the existing literal translation-grid `tubeHitCount` and point-budget stack.
-/

/-- Translation vector seen after the global eighth-dilation. -/
def eighthTranslationVector (v : Space) : Space :=
  (1 / 8 : Real) • v

theorem tubeAxisMidpoint_translateTube
    {delta : NNReal} (T : Tube delta) (v : Space) :
    tubeAxisMidpoint (translateTube T v) =
      v + tubeAxisMidpoint T := by
  simp only [tubeAxisMidpoint, translateTube,
    translateUnitSegment_base, translateUnitSegment_direction]
  module

/-- Normalization commutes exactly with translation, with the vector scaled
by the same eighth-dilation. -/
theorem eighthNormalizedTube_translateTube
    {delta : NNReal} (T : Tube delta) (v : Space) :
    eighthNormalizedTube (translateTube T v) =
      translateTube (eighthNormalizedTube T) (eighthTranslationVector v) := by
  rw [Tube.mk.injEq, UnitSegment.mk.injEq]
  constructor
  · simp only [eighthNormalizedTube_axis, eighthNormalizedAxis_base,
      translateTube,
      translateUnitSegment_base, eighthTranslationVector,
      eighthDilationPoint]
    simp only [tubeAxisMidpoint, translateUnitSegment_base, translateUnitSegment_direction]
    module
  · simp only [eighthNormalizedTube_axis, eighthNormalizedAxis_direction,
      translateTube, translateUnitSegment_direction]

/-- Carrier form used directly by finite containment incidences. -/
theorem eighthNormalizedTube_translateTube_carrier
    {delta : NNReal} (T : Tube delta) (v : Space) :
    (eighthNormalizedTube (translateTube T v)).carrier =
      (fun x => eighthTranslationVector v + x) ''
        (eighthNormalizedTube T).carrier := by
  rw [eighthNormalizedTube_translateTube, translateTube_carrier]

/-- The generic rigid action by a pure translation reduces to the same exact
normalized translation identity. -/
theorem eighthNormalizedTube_rigidTranslation
    {delta : NNReal} (T : Tube delta) (v : Space) :
    eighthNormalizedTube (rigidTube (translationRigidMotion v) T) =
      translateTube (eighthNormalizedTube T) (eighthTranslationVector v) := by
  have htube : rigidTube (translationRigidMotion v) T =
      translateTube T v := by
    rw [Tube.mk.injEq, UnitSegment.mk.injEq]
    constructor
    · simp [rigidTube, rigidUnitSegment, translationRigidMotion, translateTube, translateUnitSegment]
    · rfl
  rw [htube, eighthNormalizedTube_translateTube]

#print axioms tubeAxisMidpoint_translateTube
#print axioms eighthNormalizedTube_translateTube
#print axioms eighthNormalizedTube_translateTube_carrier
#print axioms eighthNormalizedTube_rigidTranslation

end
end Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1

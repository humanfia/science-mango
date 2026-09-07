import Family8Grounding.Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalNormalizedSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRigidMotionOrthogonalTranslationV2
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3

noncomputable section

/-!
# Unit-ball support for every sampled orthogonal catalogue motion

An admissible source tube lies in the unit ball. Any sampled orthogonal part
preserves that ball, and a raw translation of norm at most one places its
image in the radius-two ball. The existing honest eighth normalization then
puts the resulting tube back in the unit ball, exactly as required by the
fixed-John refinement consumer.
-/

variable {translation iota : Type}
  [Fintype translation] [DecidableEq translation]
  [Fintype iota] [DecidableEq iota]
  {delta : NNReal}

theorem sampledOrthogonalTranslation_normalized_carrier_subset_unitBall
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (n : Nat) (rawTranslation : translation -> Space)
    (hraw : forall t, ‖rawTranslation t‖ ≤ 1)
    (g : OrthogonalTranslationChoice translation D hD n)
    (i : iota) :
    (eighthNormalizedTube
      (rigidTube
        (sampledOrthogonalTranslationMotion D hD n rawTranslation g)
        (D.family.tubes i))).carrier ⊆
      Metric.closedBall (0 : Space) 1 := by
  apply eighthNormalizedTube_carrier_subset_unitBall
    (rigidTube
      (sampledOrthogonalTranslationMotion D hD n rawTranslation g)
      (D.family.tubes i)) hD.delta_le_half
  rw [rigidTube_carrier]
  refine (Set.image_mono (hD.contained_in_unit_ball i)).trans ?_
  unfold sampledOrthogonalTranslationMotion
  exact orthogonalTranslationRigidMotion_image_unitBall_subset_two
    (hraw g.1)

#print axioms sampledOrthogonalTranslation_normalized_carrier_subset_unitBall

end
end Family8FiniteRigidMotionOrthogonalNormalizedSupportV1

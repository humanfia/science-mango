import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperNormalizedTranslationUnitSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV2
open FamilyStickyActualTubeTranslationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Honest unit-ball support for normalized translations

A source tube lies in B1 by admissibility.  Translating by a vector of norm
at most one puts it in B2, and the already formalized eighth-normalization
sends that moved tube into B1.  This discharges the literal support premise
of the fixed John catalogue from the actual finite translation law.
-/

/-- A B1 tube translated by a B1 vector lies in B2. -/
theorem rigidTranslationTube_carrier_subset_twoBall
    {delta : NNReal} (T : Tube delta) (v : Space)
    (hT : T.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hv : ‖v‖ ≤ 1) :
    (rigidTube (translationRigidMotion v) T).carrier ⊆
      Metric.closedBall (0 : Space) 2 := by
  rw [rigidTube_translationRigidMotion_carrier, translateTube_carrier]
  rintro _ ⟨x, hx, rfl⟩
  have hxNorm : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hT hx
  have hsum : ‖v + x‖ ≤ 2 := by
    calc
      ‖v + x‖ ≤ ‖v‖ + ‖x‖ := norm_add_le _ _
      _ ≤ 1 + 1 := add_le_add hv hxNorm
      _ = 2 := by norm_num
  simpa [Metric.mem_closedBall, dist_eq_norm] using hsum

/-- Eighth-normalization sends that honestly moved B2 tube into B1. -/
theorem eighthNormalizedRigidTranslationTube_carrier_subset_unitBall
    {delta : NNReal} (T : Tube delta) (v : Space)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hT : T.carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hv : ‖v‖ ≤ 1) :
    (eighthNormalizedTube (rigidTube (translationRigidMotion v) T)).carrier ⊆
      Metric.closedBall (0 : Space) 1 := by
  exact eighthNormalizedTube_carrier_subset_unitBall
    (rigidTube (translationRigidMotion v) T) hdeltaHalf
      (rigidTranslationTube_carrier_subset_twoBall T v hT hv)

/-- The whole normalized candidate catalogue of a B1-supported finite
translation law lies in B1, with no support callback. -/
theorem normalizedRigidCandidateTube_subset_unitBall_of_gridVector_norm_le_one
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (gridVector : translation → Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hgrid : ∀ g, ‖gridVector g‖ ≤ 1) :
    ∀ a : NormalizedRigidCandidate translation iota,
      (normalizedRigidCandidateTube
        (translationCandidateMotion gridVector) D a).carrier ⊆
          Metric.closedBall (0 : Space) 1 := by
  intro a
  simpa only [normalizedRigidCandidateTube, translationCandidateMotion] using
    eighthNormalizedRigidTranslationTube_carrier_subset_unitBall
      (D.family.tubes a.2) (gridVector a.1) hD.delta_le_half
        (hD.contained_in_unit_ball a.2) (hgrid a.1)

#print axioms rigidTranslationTube_carrier_subset_twoBall
#print axioms eighthNormalizedRigidTranslationTube_carrier_subset_unitBall
#print axioms
  normalizedRigidCandidateTube_subset_unitBall_of_gridVector_norm_le_one

end
end Family8FiniteRandomRigidMotionPaperNormalizedTranslationUnitSupportV1

import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
import Family8Grounding.Family8CardinalCWARestrictionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionIncidenceV1

noncomputable section

/-! Fresh normalized selection from a copied family requires only honest
scale and B2 support, not cross-copy essential distinctness in advance. -/

theorem normalizedRestricted_isAdmissible_of_scale_B2
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (selected : Finset iota)
    (hpair : Set.Pairwise (selected : Set iota) (fun a b =>
      EssentiallyDistinct
        ((eighthNormalizedDatum D).family.tubes a)
        ((eighthNormalizedDatum D).family.tubes b))) :
    (restrictActualTubeDatum
      (eighthNormalizedDatum D) selected).IsAdmissible := by
  refine
    { delta_pos := div_pos hdeltaPos (by norm_num)
      delta_le_half :=
        (div_le_self (show 0 <= delta from bot_le)
          (by norm_num : (1 : NNReal) <= 8)).trans hdeltaHalf
      contained_in_unit_ball := ?_
      pairwise_essentiallyDistinct := ?_ }
  · intro a
    change ((eighthNormalizedDatum D).family.tubes a.1).carrier ⊆
      Metric.closedBall (0 : Space) 1
    exact eighthNormalizedDatum_contained_in_unit_ball
      D hdeltaHalf hB2 a.1
  · intro a _ha b _hb hab
    apply hpair a.property b.property
    intro hv
    apply hab
    exact Subtype.ext hv

theorem exists_normalized_refinement_admissible_isKatzTao_of_scale_B2
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    {delta : NNReal} {conflictThreshold : Nat}
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (hconflict : forall a,
      (normalizedConflictIndices D a).card <= conflictThreshold)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily) :
    exists selected : Finset iota,
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).IsAdmissible ∧
      (Fintype.card iota : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass <=
        (conflictThreshold + 1 : Nat) *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.shadingMass ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum (eighthNormalizedDatum D)
          selected).family.bodyFamily ∧
      D.shading.averageMultiplicity <=
        (conflictThreshold + 1 : Nat) *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.averageMultiplicity := by
  obtain ⟨selected, hselected, hpair, hcard, hmass⟩ :=
    exists_normalized_greedyRefinement D hconflict
  refine ⟨selected, hselected, ?_, hcard, hmass, ?_, ?_⟩
  · exact normalizedRestricted_isAdmissible_of_scale_B2
      D hdeltaPos hdeltaHalf hB2 selected hpair
  · exact restrict_eighthNormalizedDatum_isKatzTao
      D hdeltaHalf selected hKT
  · exact source_averageMultiplicity_le_loss_mul_normalizedRestricted
      D selected (conflictThreshold + 1) hmass

theorem source_averageMultiplicity_le_loss_mul_normalizedRestricted_indexedTranslations
    {tau iota : Type} [Fintype tau] [Nonempty tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (v : tau -> Space)
    (D : ActualTubeDatum delta iota)
    (selected : Finset (tau × iota)) (loss : Nat)
    (hmass :
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j => translationRigidMotion (v j)) D)).shading.shadingMass <=
        (loss : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (indexedRigidCopyDatum
                (fun j => translationRigidMotion (v j)) D))
            selected).shading.shadingMass) :
    D.shading.averageMultiplicity <=
      (loss : ENNReal) *
        (restrictActualTubeDatum
          (eighthNormalizedDatum
            (indexedRigidCopyDatum
              (fun j => translationRigidMotion (v j)) D))
          selected).shading.averageMultiplicity := by
  exact (source_averageMultiplicity_le_indexedRigidCopy
      (fun j => translationRigidMotion (v j)) D.family D.shading).trans
    (source_averageMultiplicity_le_loss_mul_normalizedRestricted
      (indexedRigidCopyDatum (fun j => translationRigidMotion (v j)) D)
      selected loss hmass)

#print axioms normalizedRestricted_isAdmissible_of_scale_B2
#print axioms exists_normalized_refinement_admissible_isKatzTao_of_scale_B2
#print axioms source_averageMultiplicity_le_loss_mul_normalizedRestricted_indexedTranslations

end
end Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2

import Family8Grounding.Family8FiniteRandomRigidMotionB2FrostmanConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2FrostmanScaleSupportV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2AutomaticConflictCapV1
open Family8FiniteRandomRigidMotionB2FrostmanConnectorV1

noncomputable section

/-!
# B2 Frostman selection from scale and support data, V2

The fresh normalized greedy selection manufactures pairwise essential
distinctness on its selected subtype.  The unnormalized source therefore
needs only a positive half-scale and radius-two support, not a source
pairwise-distinctness certificate.  This is the form required by actual
Sticky coarse families.

V1 is a failed namespace-opening draft and is not imported.
-/

theorem normalizedRestricted_isAdmissible_of_scale_support
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

theorem exists_normalized_refinement_admissible_isKatzTao_of_scale_support
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
  · exact normalizedRestricted_isAdmissible_of_scale_support
      D hdeltaPos hdeltaHalf hB2 selected hpair
  · exact restrict_eighthNormalizedDatum_isKatzTao
      D hdeltaHalf selected hKT
  · exact source_averageMultiplicity_le_loss_mul_normalizedRestricted
      D selected (conflictThreshold + 1) hmass

theorem exists_normalized_source_averageMultiplicity_le_frostmanRHS_of_scale_support
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    {conflictThreshold : Nat}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (hconflict : forall a,
      (normalizedConflictIndices D a).card <= conflictThreshold)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily)
    (hdelta0 : delta / 8 <= delta0)
    (hdensityBudget :
      ((delta / 8 : NNReal) : ENNReal) ^ eta <=
        (eighthNormalizedDatum D).shading.shadingDensity /
          (conflictThreshold + 1 : Nat))
    (hbaseBudget :
      (conflictThreshold + 1 : Nat) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    exists selected : Finset iota,
      selected.Nonempty ∧
      D.shading.averageMultiplicity <=
        (conflictThreshold + 1 : Nat) *
          frostmanMultiplicityRHS (delta / 8)
            (restrictActualTubeDatum (eighthNormalizedDatum D)
              selected).actualFamilyVolume epsilon beta := by
  let loss := conflictThreshold + 1
  have hloss : NeZero loss :=
    ⟨Nat.ne_of_gt (by dsimp only [loss]; omega)⟩
  obtain ⟨selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, _hmultiplicity⟩ :=
    exists_normalized_refinement_admissible_isKatzTao_of_scale_support
      D hdeltaPos hdeltaHalf hB2 hconflict hKT
  refine ⟨selected, hselected, ?_⟩
  exact
    @source_averageMultiplicity_le_normalized_loss_mul_frostmanRHS_of_refinement
      _ _ _ _ _ _ _ _ hF D selected loss hloss (128 * C) hdelta0
        hadmissible hcard hmass hselectedKT hdensityBudget hbaseBudget

theorem exists_automatic_normalized_source_averageMultiplicity_le_frostmanRHS_of_scale_support
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily)
    (hdelta0 : delta / 8 <= delta0)
    (hdensityBudget :
      ((delta / 8 : NNReal) : ENNReal) ^ eta <=
        (eighthNormalizedDatum D).shading.shadingDensity /
          (Fintype.card iota + 1 : Nat))
    (hbaseBudget :
      (Fintype.card iota + 1 : Nat) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    exists selected : Finset iota,
      selected.Nonempty ∧
      D.shading.averageMultiplicity <=
        (Fintype.card iota + 1 : Nat) *
          frostmanMultiplicityRHS (delta / 8)
            (restrictActualTubeDatum (eighthNormalizedDatum D)
              selected).actualFamilyVolume epsilon beta := by
  exact
    exists_normalized_source_averageMultiplicity_le_frostmanRHS_of_scale_support
      hF D hdeltaPos hdeltaHalf hB2
      (normalizedConflictIndices_card_le_indexCard D)
      hKT hdelta0 hdensityBudget hbaseBudget

#print axioms normalizedRestricted_isAdmissible_of_scale_support
#print axioms
  exists_normalized_refinement_admissible_isKatzTao_of_scale_support
#print axioms
  exists_normalized_source_averageMultiplicity_le_frostmanRHS_of_scale_support
#print axioms
  exists_automatic_normalized_source_averageMultiplicity_le_frostmanRHS_of_scale_support

end
end Family8FiniteRandomRigidMotionB2FrostmanScaleSupportV2

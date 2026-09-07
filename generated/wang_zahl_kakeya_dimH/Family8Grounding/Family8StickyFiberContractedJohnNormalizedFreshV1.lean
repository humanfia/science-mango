import Family8Grounding.Family8StickyFiberContractedJohnProxyDatumV1
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnNormalizedFreshV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Automatic normalized fresh selection for one contracted-John Sticky fibre

The canonical actual proxy datum is supported in the unit ball but its proxy
tubes need not inherit pairwise essential distinctness.  Raw Katz--Tao
control of that same proxy family now supplies the conflict-degree cap
automatically.  The existing weighted greedy theorem then produces the
literal admissible normalized subtype, retaining cardinality, shading mass,
and the original fibre average multiplicity at one explicit finite loss.

The sole analytic/geometric input left by this module is raw Katz--Tao
control of the genuine proxy family; no conflict callback remains.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Raw proxy Katz--Tao control gives a fully automatic admissible fresh
normalized subtype on the canonical active fibre. -/
theorem exists_stickyFiberContractedJohn_normalizedFresh_of_isKatzTao
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho) (k : {k // k ∈ S.activeCoarse})
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C
      (stickyFiberContractedJohnProxyDatum
        S Y hrho hrhoOne k).family.bodyFamily) :
    let D := stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k
    let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
    exists selected : Finset {i // i ∈ S.fiber k.1},
      selected.Nonempty ∧
      (restrictActualTubeDatum (eighthNormalizedDatum D) selected).IsAdmissible ∧
      (Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) <=
        (threshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass <=
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.shadingMass ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      (stickyFiberSourceShading S Y k.1).averageMultiplicity <=
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.averageMultiplicity := by
  dsimp only
  let D := stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k
  let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
  have hfiberNonempty : (S.fiber k.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ := S.parent_surjective k.1 k.2
    exact ⟨i, (S.mem_fiber i k.1).2 ⟨hiActive, hiParent⟩⟩
  let _ : Nonempty {i // i ∈ S.fiber k.1} :=
    Finset.nonempty_coe_sort.mpr hfiberNonempty
  have hproxyPos : 0 < contractedJohnProxyRadius delta rho :=
    stickyFiberContractedJohnProxyDatum_delta_pos hdelta hrho
  have hproxyHalf :
      contractedJohnProxyRadius delta rho <= (2 : NNReal)⁻¹ :=
    stickyFiberContractedJohnProxyDatum_delta_le_half hdeltaRho hrho
  have hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2 := by
    intro i
    exact (stickyFiberContractedJohnProxyDatum_contained_in_unit_ball
      S Y hrho hrhoOne hdeltaRho k i).trans
        (Metric.closedBall_subset_closedBall (by norm_num))
  have hconflict : forall a,
      (normalizedConflictIndices D a).card <= threshold := by
    intro a
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      D hproxyPos hproxyHalf hCfinite hKT a
  obtain ⟨selected, hselected, hpair, hcard, hmass⟩ :=
    exists_normalized_greedyRefinement D hconflict
  have hadmissible :
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).IsAdmissible := by
    refine
      { delta_pos := div_pos hproxyPos (by norm_num)
        delta_le_half :=
          (div_le_self
            (show 0 <= contractedJohnProxyRadius delta rho from bot_le)
            (by norm_num : (1 : NNReal) <= 8)).trans hproxyHalf
        contained_in_unit_ball := ?_
        pairwise_essentiallyDistinct := ?_ }
    · intro i
      change ((eighthNormalizedDatum D).family.tubes i.1).carrier ⊆
        Metric.closedBall (0 : Space) 1
      exact eighthNormalizedDatum_contained_in_unit_ball
        D hproxyHalf hB2 i.1
    · intro i _hi j _hj hij
      apply hpair i.property j.property
      intro hv
      apply hij
      exact Subtype.ext hv
  have hselectedKT : IsKatzTao (128 * C)
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).family.bodyFamily :=
    restrict_eighthNormalizedDatum_isKatzTao
      D hproxyHalf selected hKT
  have havg : D.shading.averageMultiplicity <=
      (threshold + 1 : Nat) *
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).shading.averageMultiplicity :=
    source_averageMultiplicity_le_loss_mul_normalizedRestricted
      D selected (threshold + 1) hmass
  refine ⟨selected, hselected, hadmissible, hcard, hmass,
    hselectedKT, ?_⟩
  have hproxyAvg : D.shading.averageMultiplicity =
      (stickyFiberSourceShading S Y k.1).averageMultiplicity := by
    change (stickyFiberContractedJohnProxyShading
      S Y hrho hrhoOne k).averageMultiplicity =
        (stickyFiberSourceShading S Y k.1).averageMultiplicity
    exact stickyFiberContractedJohnProxyShading_averageMultiplicity
      S Y hrho hrhoOne k
  rw [hproxyAvg] at havg
  simpa only [threshold] using havg

#print axioms
  exists_stickyFiberContractedJohn_normalizedFresh_of_isKatzTao

end

end Family8StickyFiberContractedJohnNormalizedFreshV1

import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
import Family8Grounding.Family8FrozenCoarseB2DensityTransportScaleOnlyV1
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8MassRetainingNormalizedSelectedKatzTaoEndpointV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8RestrictedActualDatumDensityRetentionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# Katz--Tao on one already selected mass-retaining normalized subtype

Unlike the existential fresh-selection endpoint, this adapter keeps a given
literal `selected` set. Thus a geometric count proved for that same selected
set can be combined with the analytic Katz--Tao average estimate without a
second greedy choice. The only geometric support input is the honest B2
carrier bound on the raw proxy datum.
-/

/-- A pairwise, mass-retaining normalized selection is admissible and obeys
the fixed-parameter Katz--Tao estimate on that very same subtype. -/
theorem apply_katzTaoAtParameters_to_massRetaining_normalizedSelected
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hB2 : ∀ i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (selected : Finset iota) (hselected : selected.Nonempty)
    (hpair : Set.Pairwise (selected : Set iota) (fun a b =>
      EssentiallyDistinct
        ((eighthNormalizedDatum D).family.tubes a)
        ((eighthNormalizedDatum D).family.tubes b)))
    (loss : Nat) (hlossPos : 0 < loss)
    (hmass :
      (eighthNormalizedDatum D).shading.shadingMass ≤
        (loss : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.shadingMass)
    {C : ENNReal}
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hdelta0 : delta / 8 ≤ delta0)
    (hdensityBudget :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (128 * (loss : ENNReal)) ≤ D.shading.shadingDensity)
    (hcoefficient :
      128 * C ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    let refined := restrictActualTubeDatum
      (eighthNormalizedDatum D) selected
    selected.Nonempty ∧
      refined.IsAdmissible ∧
      KatzTaoHypotheses refined eta ∧
      refined.shading.averageMultiplicity ≤
        katzTaoMultiplicityRHS (delta / 8) selected.card epsilon beta ∧
      D.shading.averageMultiplicity ≤
        (loss : ENNReal) *
          katzTaoMultiplicityRHS (delta / 8) selected.card epsilon beta := by
  dsimp only
  let _ : Nonempty iota := ⟨hselected.choose⟩
  let refined := restrictActualTubeDatum
    (eighthNormalizedDatum D) selected
  have hadmissible : refined.IsAdmissible := by
    exact normalizedRestricted_isAdmissible_of_scale_B2
      D hdeltaPos hdeltaHalf hB2 selected hpair
  have hselectedKT : IsKatzTao (128 * C) refined.family.bodyFamily := by
    exact restrict_eighthNormalizedDatum_isKatzTao
      D hdeltaHalf selected hKT
  have hloss0 : (loss : ENNReal) ≠ 0 := by simp [hlossPos.ne']
  have hlossTop : (loss : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hnormalizedDensity :
      D.shading.shadingDensity / 128 ≤
        (eighthNormalizedDatum D).shading.shadingDensity :=
    source_shadingDensity_div_128_le_eighthNormalized_of_scale
      D hdeltaPos hdeltaHalf
  have hrefinedDensity :
      (eighthNormalizedDatum D).shading.shadingDensity / (loss : ENNReal) ≤
        refined.shading.shadingDensity := by
    exact source_shadingDensity_div_loss_le_restrictActualTubeDatum
      (eighthNormalizedDatum D) selected (loss : ENNReal) hmass
  have hbudgetDiv :
      ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
        D.shading.shadingDensity / 128 / (loss : ENNReal) := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hloss0) (Or.inl hlossTop)).2
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num : (128 : ENNReal) ≠ 0))
      (Or.inl (by norm_num : (128 : ENNReal) ≠ ∞))).2
    calc
      (((delta / 8 : NNReal) : ENNReal) ^ eta *
          (loss : ENNReal)) * 128 =
          ((delta / 8 : NNReal) : ENNReal) ^ eta *
            (128 * (loss : ENNReal)) := by ac_rfl
      _ ≤ D.shading.shadingDensity := hdensityBudget
  have hselectedDensity :
      ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
        refined.shading.shadingDensity :=
    hbudgetDiv.trans
      ((ENNReal.div_le_div_right hnormalizedDensity (loss : ENNReal)).trans
        hrefinedDensity)
  have hhyp : KatzTaoHypotheses refined eta := by
    refine ⟨hselectedDensity, ?_⟩
    rw [maximalConcentration_le_iff_isKatzTao]
    exact hselectedKT.mono hcoefficient
  have hselectedBound :
      refined.shading.averageMultiplicity ≤
        katzTaoMultiplicityRHS (delta / 8) selected.card epsilon beta := by
    simpa only [refined, Fintype.card_coe] using
      KatzTaoAtParameters.apply hKTP refined hadmissible hdelta0 hhyp
  have hsourceAverage :
      D.shading.averageMultiplicity ≤
        (loss : ENNReal) * refined.shading.averageMultiplicity := by
    simpa only [refined] using
      source_averageMultiplicity_le_loss_mul_normalizedRestricted
        D selected loss hmass
  have hmul :
      (loss : ENNReal) * refined.shading.averageMultiplicity ≤
        (loss : ENNReal) *
          katzTaoMultiplicityRHS (delta / 8) selected.card epsilon beta := by
    gcongr
  exact ⟨hselected, hadmissible, hhyp, hselectedBound,
    hsourceAverage.trans hmul⟩

#print axioms
  apply_katzTaoAtParameters_to_massRetaining_normalizedSelected

end
end Family8MassRetainingNormalizedSelectedKatzTaoEndpointV4

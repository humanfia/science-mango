import Family8Grounding.Family8FiniteRandomRigidMotionB2FreshGreedyV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2AutomaticConflictCapV1
import Family8Grounding.Family8FiniteRandomRigidMotionFrostmanConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2FrostmanConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8FiniteRandomRigidMotionFrostmanConnectorV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2AutomaticConflictCapV1

noncomputable section

/-!
# Frostman connector after honest B2 normalization

This is the normalized-radius analogue of the existing deterministic
connector.  It consumes the fresh greedy output at radius `delta/8`, proves
the selected subtype's Frostman hypotheses internally, and returns a bound
for the original source average multiplicity using its exact invariance under
the eighth-dilation.
-/

theorem source_averageMultiplicity_le_normalized_loss_mul_frostmanRHS_of_refinement
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota)
    (selected : Finset iota)
    (loss : Nat) [NeZero loss]
    (C : ENNReal)
    (hdelta0 : delta / 8 <= delta0)
    (hadmissible :
      (restrictActualTubeDatum (eighthNormalizedDatum D)
        selected).IsAdmissible)
    (hcard : (Fintype.card iota : ENNReal) <=
      (loss : ENNReal) * (selected.card : ENNReal))
    (hmass :
      (eighthNormalizedDatum D).shading.shadingMass <=
        (loss : ENNReal) *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.shadingMass)
    (hKT : IsKatzTao C
      (restrictActualTubeDatum (eighthNormalizedDatum D)
        selected).family.bodyFamily)
    (hdensityBudget :
      ((delta / 8 : NNReal) : ENNReal) ^ eta <=
        (eighthNormalizedDatum D).shading.shadingDensity /
          (loss : ENNReal))
    (hbaseBudget :
      (loss : ENNReal) *
          (C * volume (unitBallBody : Set Space)) <=
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    D.shading.averageMultiplicity <=
      (loss : ENNReal) *
        frostmanMultiplicityRHS (delta / 8)
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).actualFamilyVolume epsilon beta := by
  let full := eighthNormalizedDatum D
  let refined := restrictActualTubeDatum full selected
  have hdensityTransport :
      full.shading.shadingDensity / (loss : ENNReal) <=
        refined.shading.shadingDensity := by
    exact source_shadingDensity_div_loss_le_restrictActualTubeDatum
      full selected (loss : ENNReal) hmass
  have hrefinedDensity :
      ((delta / 8 : NNReal) : ENNReal) ^ eta <=
        refined.shading.shadingDensity := by
    exact hdensityBudget.trans hdensityTransport
  have hrefinedVolume :
      (selected.card : ENNReal) *
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) <=
        refined.actualFamilyVolume := by
    simpa only [refined, full, Fintype.card_coe] using
      card_mul_half_sq_le_actualFamilyVolume
        refined hadmissible.delta_le_half
  have hloss0 : (loss : ENNReal) ≠ 0 := by
    exact_mod_cast (NeZero.ne loss)
  have hlossTop : (loss : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hbase :
      C * volume (unitBallBody : Set Space) <=
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          refined.actualFamilyVolume := by
    apply (ENNReal.mul_le_mul_iff_right hloss0 hlossTop).mp
    calc
      (loss : ENNReal) *
          (C * volume (unitBallBody : Set Space)) <=
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) := hbaseBudget
      _ <= ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          (((loss : ENNReal) * (selected.card : ENNReal)) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) := by
        gcongr
      _ = (loss : ENNReal) *
          (((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
            ((selected.card : ENNReal) *
              (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) := by
        ac_rfl
      _ <= (loss : ENNReal) *
          (((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
            refined.actualFamilyVolume) := by
        gcongr
  have hFrostmanHyp : FrostmanHypotheses refined eta :=
    frostmanHypotheses_of_density_isKatzTao_base
      refined hadmissible eta C hrefinedDensity hKT hbase
  have hrefinedMultiplicity :=
    FrostmanAtParameters.apply hF refined hadmissible hdelta0 hFrostmanHyp
  have hsourceMultiplicity :=
    source_averageMultiplicity_le_loss_mul_normalizedRestricted
      D selected loss hmass
  exact hsourceMultiplicity.trans
    (mul_le_mul' le_rfl hrefinedMultiplicity)

/-- Fresh normalized greedy plus the deterministic Frostman connector.  All
properties of the existential selected subtype are eliminated internally. -/
theorem exists_normalized_source_averageMultiplicity_le_frostmanRHS
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    {conflictThreshold : Nat}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
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
    exists_normalized_refinement_admissible_isKatzTao
      D hD hB2 hconflict hKT
  refine ⟨selected, hselected, ?_⟩
  exact
    @source_averageMultiplicity_le_normalized_loss_mul_frostmanRHS_of_refinement
      _ _ _ _ _ _ _ _ hF D selected loss hloss (128 * C) hdelta0 hadmissible hcard hmass
        hselectedKT hdensityBudget hbaseBudget

/-- The completely automatic finite fallback, obtained by taking the
normalized conflict threshold to be the whole finite index cardinality. -/
theorem exists_automatic_normalized_source_averageMultiplicity_le_frostmanRHS
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
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
  exact exists_normalized_source_averageMultiplicity_le_frostmanRHS
    hF D hD hB2 (normalizedConflictIndices_card_le_indexCard D)
      hKT hdelta0 hdensityBudget hbaseBudget

#print axioms source_averageMultiplicity_le_normalized_loss_mul_frostmanRHS_of_refinement
#print axioms exists_normalized_source_averageMultiplicity_le_frostmanRHS
#print axioms exists_automatic_normalized_source_averageMultiplicity_le_frostmanRHS

end
end Family8FiniteRandomRigidMotionB2FrostmanConnectorV1

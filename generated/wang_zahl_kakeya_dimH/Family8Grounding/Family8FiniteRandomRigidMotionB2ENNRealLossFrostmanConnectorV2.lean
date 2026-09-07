import Family8Grounding.Family8FiniteRandomRigidMotionB2FrostmanConnectorV1
import Mathlib.Tactic

/-!
# Deterministic B2 Frostman connector with an ENNReal retention loss

The existing connector fixes the retention loss to a natural greedy degree.
The retained-parent low-CF branch already carries a closed ENNReal loss.  The
same proof works verbatim once nonzero/finiteness are stated explicitly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionFrostmanConnectorV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8RestrictedActualDatumDensityRetentionV1

noncomputable section

/-- A selected normalized datum reaches the Frostman multiplicity bound with
an arbitrary honest finite ENNReal retention loss. -/
theorem source_averageMultiplicity_le_normalized_ennrealLoss_mul_frostmanRHS
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota)
    (selected : Finset iota)
    (loss C : ENNReal)
    (hloss0 : loss ≠ 0) (hlossTop : loss ≠ ∞)
    (hdelta0 : delta / 8 ≤ delta0)
    (hadmissible :
      (restrictActualTubeDatum (eighthNormalizedDatum D)
        selected).IsAdmissible)
    (hcard : (Fintype.card iota : ENNReal) ≤
      loss * (selected.card : ENNReal))
    (hmass :
      (eighthNormalizedDatum D).shading.shadingMass ≤
        loss *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.shadingMass)
    (hKT : IsKatzTao C
      (restrictActualTubeDatum (eighthNormalizedDatum D)
        selected).family.bodyFamily)
    (hdensityBudget :
      ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
        (eighthNormalizedDatum D).shading.shadingDensity / loss)
    (hbaseBudget :
      loss * (C * volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    D.shading.averageMultiplicity ≤
      loss * frostmanMultiplicityRHS (delta / 8)
        (restrictActualTubeDatum (eighthNormalizedDatum D)
          selected).actualFamilyVolume epsilon beta := by
  let full := eighthNormalizedDatum D
  let refined := restrictActualTubeDatum full selected
  have hdensityTransport :
      full.shading.shadingDensity / loss ≤
        refined.shading.shadingDensity := by
    exact source_shadingDensity_div_loss_le_restrictActualTubeDatum
      full selected loss hmass
  have hrefinedDensity :
      ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
        refined.shading.shadingDensity :=
    hdensityBudget.trans hdensityTransport
  have hrefinedVolume :
      (selected.card : ENNReal) *
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) ≤
        refined.actualFamilyVolume := by
    simpa only [refined, full, Fintype.card_coe] using
      card_mul_half_sq_le_actualFamilyVolume
        refined hadmissible.delta_le_half
  have hbase :
      C * volume (unitBallBody : Set Space) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          refined.actualFamilyVolume := by
    apply (ENNReal.mul_le_mul_iff_right hloss0 hlossTop).mp
    calc
      loss * (C * volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) := hbaseBudget
      _ ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((loss * (selected.card : ENNReal)) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) := by
        gcongr
      _ = loss *
          (((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
            ((selected.card : ENNReal) *
              (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) := by
        ac_rfl
      _ ≤ loss *
          (((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
            refined.actualFamilyVolume) := by
        gcongr
  have hFrostmanHyp : FrostmanHypotheses refined eta :=
    frostmanHypotheses_of_density_isKatzTao_base
      refined hadmissible eta C hrefinedDensity hKT hbase
  have hrefinedMultiplicity :=
    FrostmanAtParameters.apply hF refined hadmissible hdelta0 hFrostmanHyp
  have hsourceMultiplicity : D.shading.averageMultiplicity ≤
      loss * refined.shading.averageMultiplicity := by
    rw [← eighthNormalizedDatum_averageMultiplicity D]
    have hunion : refined.shading.shadedUnion ⊆
        full.shading.shadedUnion :=
      restrictActualTubeDatum_shadedUnion_subset full selected
    unfold Shading.averageMultiplicity
    calc
      full.shading.shadingMass / volume full.shading.shadedUnion ≤
          (loss * refined.shading.shadingMass) /
            volume full.shading.shadedUnion :=
        ENNReal.div_le_div_right hmass _
      _ ≤ (loss * refined.shading.shadingMass) /
            volume refined.shading.shadedUnion :=
        ENNReal.div_le_div_left (measure_mono hunion) _
      _ = loss *
          (refined.shading.shadingMass /
            volume refined.shading.shadedUnion) := by
        simp only [div_eq_mul_inv]
        ac_rfl
  exact hsourceMultiplicity.trans
    (mul_le_mul' le_rfl hrefinedMultiplicity)

#print axioms
  source_averageMultiplicity_le_normalized_ennrealLoss_mul_frostmanRHS

end
end Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2

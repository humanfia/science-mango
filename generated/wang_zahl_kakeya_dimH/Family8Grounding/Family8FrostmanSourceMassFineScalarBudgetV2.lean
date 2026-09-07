import Family8Grounding.Family8LogarithmicSelectedScalarPowerBudgetsV1
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Submission.Kakeya.ConvexFactoring.JointTubeFactoring

/-!
# Frostman source mass discharges the fine scalar budget, V2

Fresh ADD-only successor with the explicit body-mass import.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrostmanSourceMassFineScalarBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8LogarithmicSelectedScalarPowerBudgetsV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- The literal all-index body mass dominates the Frostman source mass. -/
theorem delta_rpow_two_eta_le_bodyMassOn_univ_of_frostman
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {eta : Real} (hF : FrostmanHypotheses D eta) :
    (delta : ENNReal) ^ (2 * eta) <=
      bodyMassOn D.family.bodyFamily Finset.univ := by
  have hmass := delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
  calc
    (delta : ENNReal) ^ (2 * eta) <= D.shading.shadingMass := hmass
    _ <= familyVolume D.family.bodyFamily :=
      D.shading.shadingMass_le_familyVolume
    _ = bodyMassOn D.family.bodyFamily Finset.univ := by
      unfold familyVolume bodyMassOn
      simp

/-- The exact first scalar input of logarithmic selection follows from the
Frostman source-mass floor and the displayed power-envelope budget. -/
theorem fineSource_scalarAbsorption_of_frostman
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {eta coefficientExponent absorbExponent baseExponent : Real}
    (hF : FrostmanHypotheses D eta)
    (sourceA : ENNReal)
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaSmall : delta <= fineSourceScalarThreshold absorbExponent)
    (hcoefficient :
      (2 * (Nat.log 2 (Fintype.card iota) + 1) : Nat) * sourceA <=
        (delta : ENNReal) ^ (-coefficientExponent))
    (hexponent :
      2 * eta + coefficientExponent + absorbExponent <= baseExponent) :
    (131072 : ENNReal) *
          (2 * (Nat.log 2 (Fintype.card iota) + 1) : Nat) *
          (2 : ENNReal) ^ 2 * sourceA <=
      (delta : ENNReal) ^ (-baseExponent) *
        bodyMassOn D.family.bodyFamily Finset.univ := by
  apply fineSource_scalarAbsorption_of_powerEnvelopes
    hD.delta_pos (hD.delta_le_half.trans (by norm_num))
      habsorbExponent hdeltaSmall hcoefficient
  · exact delta_rpow_two_eta_le_bodyMassOn_univ_of_frostman D hD hF
  · exact hexponent

end

end Family8FrostmanSourceMassFineScalarBudgetV2

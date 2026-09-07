import Family8Grounding.Family8FiniteRandomRigidMotionJohnJointTailV1
import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionFrostmanConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8RestrictedActualDatumMassBridgeV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family6CanonicalFrostmanConstantCoreV1

noncomputable section

/-!
# From the random rigid refinement to the Frostman endpoint

The polynomial John selector supplies global Katz--Tao control.  The exact
cross-multiplied bridge `IsKatzTao.isFrostmanIn` shows that the only extra
Frostman input is one scalar normalization in the ambient unit ball.  Here
that normalization is reduced to a pre-selection budget using the retained
product cardinality and the proved lower bound `volume(T) >= delta^2 / 2`.
-/

/-- Every actual `delta`-tube contributes at least `delta^2 / 2` to the
summed actual family volume. -/
theorem card_mul_half_sq_le_actualFamilyVolume
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    (Fintype.card iota : ENNReal) * ((delta : ENNReal) ^ 2 / 2) <=
      D.actualFamilyVolume := by
  unfold ActualTubeDatum.actualFamilyVolume familyVolume
  simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
  calc
    (Fintype.card iota : ENNReal) * ((delta : ENNReal) ^ 2 / 2) =
        ∑ _i : iota, (delta : ENNReal) ^ 2 / 2 := by
          simp [nsmul_eq_mul]
    _ <= ∑ i : iota, volume (D.family.tubes i).carrier := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (D.family.tubes i).half_sq_le_volume_of_le_half hdeltaHalf

/-- Global Katz--Tao control becomes the required ambient Frostman condition
once the single displayed base normalization holds. -/
theorem frostmanHypotheses_of_density_isKatzTao_base
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (eta : Real) (C : ENNReal)
    (hdensity : (delta : ENNReal) ^ eta <=
      D.shading.shadingDensity)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hbase : C * volume (unitBallBody : Set Space) <=
      (delta : ENNReal) ^ (-eta) * D.actualFamilyVolume) :
    FrostmanHypotheses D eta := by
  refine ⟨hdensity, ?_⟩
  apply IsKatzTao.isFrostmanIn hKT
  · intro i
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body,
      coe_unitBallBody] using hD.contained_in_unit_ball i
  · have hambient :
        containedMass D.family.bodyFamily unitBallBody =
          D.actualFamilyVolume := by
      simpa only [ActualTubeDatum.actualFamilyVolume] using
        (containedMass_eq_familyVolume_of_contained
          D.family.bodyFamily unitBallBody (fun i => by
            simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body,
              coe_unitBallBody] using hD.contained_in_unit_ball i))
    rw [hambient]
    exact hbase

/-- The exact deterministic connector consumed immediately after the
one-shot random producer.  Its two new premises are pre-selection scalar
budgets: density after the explicit greedy loss, and the unit-ball base
normalization after the retained-cardinality lower bound. -/
theorem source_averageMultiplicity_le_loss_mul_frostmanRHS_of_refinement
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {tau iota : Type}
    [Fintype tau] [Nonempty tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (motion : tau -> RigidMotion)
    (D : ActualTubeDatum delta iota) (_hD : D.IsAdmissible)
    (selected : Finset (tau × iota))
    (loss : Nat) [NeZero loss]
    (C : ENNReal)
    (hdelta0 : delta <= delta0)
    (hadmissible :
      (restrictActualTubeDatum (indexedRigidCopyDatum motion D)
        selected).IsAdmissible)
    (hcard : (Fintype.card (tau × iota) : ENNReal) <=
      (loss : ENNReal) * (selected.card : ENNReal))
    (hmass :
      (indexedRigidCopyDatum motion D).shading.shadingMass <=
        (loss : ENNReal) *
          (restrictActualTubeDatum (indexedRigidCopyDatum motion D)
            selected).shading.shadingMass)
    (hKT : IsKatzTao C
      (restrictActualTubeDatum (indexedRigidCopyDatum motion D)
        selected).family.bodyFamily)
    (hdensityBudget :
      (delta : ENNReal) ^ eta <=
        D.shading.shadingDensity / (loss : ENNReal))
    (hbaseBudget :
      (loss : ENNReal) *
          (C * volume (unitBallBody : Set Space)) <=
        (delta : ENNReal) ^ (-eta) *
          ((Fintype.card (tau × iota) : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2))) :
    D.shading.averageMultiplicity <=
      (loss : ENNReal) *
        frostmanMultiplicityRHS delta
          (restrictActualTubeDatum (indexedRigidCopyDatum motion D)
            selected).actualFamilyVolume epsilon beta := by
  let full := indexedRigidCopyDatum motion D
  let refined := restrictActualTubeDatum full selected
  have hfullDensity : full.shading.shadingDensity =
      D.shading.shadingDensity := by
    exact indexedRigidCopyShading_shadingDensity
      motion D.family D.shading
  have hdensityTransport :
      full.shading.shadingDensity / (loss : ENNReal) <=
        refined.shading.shadingDensity := by
    exact source_shadingDensity_div_loss_le_restrictActualTubeDatum
      full selected (loss : ENNReal) hmass
  have hrefinedDensity :
      (delta : ENNReal) ^ eta <= refined.shading.shadingDensity := by
    calc
      (delta : ENNReal) ^ eta <=
          D.shading.shadingDensity / (loss : ENNReal) := hdensityBudget
      _ = full.shading.shadingDensity / (loss : ENNReal) := by
        rw [hfullDensity]
      _ <= refined.shading.shadingDensity := hdensityTransport
  have hrefinedVolume :
      (selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) <=
        refined.actualFamilyVolume := by
    simpa only [refined, full, Fintype.card_coe] using
      card_mul_half_sq_le_actualFamilyVolume
        refined hadmissible.delta_le_half
  have hloss0 : (loss : ENNReal) ≠ 0 := by
    exact_mod_cast (NeZero.ne loss)
  have hlossTop : (loss : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hbase :
      C * volume (unitBallBody : Set Space) <=
        (delta : ENNReal) ^ (-eta) * refined.actualFamilyVolume := by
    apply (ENNReal.mul_le_mul_iff_right hloss0 hlossTop).mp
    calc
      (loss : ENNReal) *
          (C * volume (unitBallBody : Set Space)) <=
        (delta : ENNReal) ^ (-eta) *
          ((Fintype.card (tau × iota) : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)) := hbaseBudget
      _ <= (delta : ENNReal) ^ (-eta) *
          (((loss : ENNReal) * (selected.card : ENNReal)) *
            ((delta : ENNReal) ^ 2 / 2)) := by
        gcongr
      _ = (loss : ENNReal) *
          ((delta : ENNReal) ^ (-eta) *
            ((selected.card : ENNReal) *
              ((delta : ENNReal) ^ 2 / 2))) := by
        ac_rfl
      _ <= (loss : ENNReal) *
          ((delta : ENNReal) ^ (-eta) *
            refined.actualFamilyVolume) := by
        gcongr
  have hFrostmanHyp : FrostmanHypotheses refined eta :=
    frostmanHypotheses_of_density_isKatzTao_base
      refined hadmissible eta C hrefinedDensity hKT hbase
  have hrefinedMultiplicity :=
    FrostmanAtParameters.apply hF refined hadmissible hdelta0 hFrostmanHyp
  have hsourceMultiplicity :=
    source_averageMultiplicity_le_loss_mul_rigidCopyRestricted
      motion D selected loss hmass
  exact hsourceMultiplicity.trans
    (mul_le_mul' le_rfl hrefinedMultiplicity)

#print axioms card_mul_half_sq_le_actualFamilyVolume
#print axioms frostmanHypotheses_of_density_isKatzTao_base
#print axioms source_averageMultiplicity_le_loss_mul_frostmanRHS_of_refinement

end
end Family8FiniteRandomRigidMotionFrostmanConnectorV1

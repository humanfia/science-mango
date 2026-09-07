import Family8Grounding.Family8Lemma69ActualTubeDeltaBCThresholdedEq32ComposerV1
import Family8Grounding.Family8FiniteRandomRigidMotionFrostmanConnectorV1
import Mathlib.Tactic

/-!
# Density/cardinality producer for the thresholded Lemma 6.9 scalar seam

The normalized thresholded composer asks for one scalar absorption predicate.
This file reduces that predicate to the familiar actual-tube density and
cardinality payment.  The only cancellation side condition in the predicate,
finiteness of the canonical row scale, follows from the absorption itself
when the requested union floor and Katz--Tao constant are nonzero: otherwise
the left side would be infinite while every finite shading has finite mass.

No bound on the canonical scale, no positive-carrier hypothesis, and no new
geometric premise is introduced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Lemma69DeltaBCThresholdedDensityCardScalarProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Family6AffineConvexVolumeCoreV1
open Family6Lemma69DeltaBCPlankGeometryV1
open Family6Lemma69DeltaBCThresholdedBudgetV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8FiniteRandomRigidMotionFrostmanConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Lemma69ActualTubeDeltaBCThresholdedEq32ComposerV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8SelectedParentAffineShadingTransportV4

noncomputable section

/-- A nonzero normalized absorption automatically rules out an infinite
canonical row scale.  This is strictly weaker than imposing a memberwise
positive carrier-volume floor. -/
theorem deltaBCThresholdedCanonicalScale_ne_top_of_absorption
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F)
    {C delta b c : NNReal}
    (cert : ∀ i, DeltaBCDimensionsCertificate C delta b c (F i))
    (hc : 0 < c) (KT L : ENNReal)
    (hL : L ≠ 0) (hKT : KT ≠ 0)
    (habsorb :
      (affineJacobian (deltaBCNormalizationEquiv c hc) * L) *
          (((plankAngleLevels (deltaBCThresholdedLevels cert hc)).card :
              ENNReal) * KT * deltaBCThresholdedCanonicalScale cert hc Y) ≤
        (deltaBCNormalizedShading c hc Y).shadingMass) :
    deltaBCThresholdedCanonicalScale cert hc Y ≠ ∞ := by
  let J : ENNReal := affineJacobian (deltaBCNormalizationEquiv c hc)
  let levels := plankAngleLevels (deltaBCThresholdedLevels cert hc)
  have hJ : J ≠ 0 :=
    (affineJacobian_pos (deltaBCNormalizationEquiv c hc)).ne'
  have hlevelsNat : levels.card ≠ 0 := by
    apply Finset.card_ne_zero.mpr
    exact ⟨none, by simp [levels, plankAngleLevels]⟩
  have hlevels : (levels.card : ENNReal) ≠ 0 := by
    exact_mod_cast hlevelsNat
  intro hscaleTop
  have hleftTop :
      (J * L) *
          ((levels.card : ENNReal) * KT *
            deltaBCThresholdedCanonicalScale cert hc Y) = ∞ := by
    rw [hscaleTop]
    rw [ENNReal.mul_top (mul_ne_zero hlevels hKT)]
    exact ENNReal.mul_top (mul_ne_zero hJ hL)
  have htopLe : ∞ ≤
      (deltaBCNormalizedShading c hc Y).shadingMass := by
    rw [← hleftTop]
    simpa only [J, levels] using habsorb
  exact (deltaBCNormalizedShading c hc Y).shadingMass_lt_top.ne
    (top_unique htopLe)

/-- The standard tube-volume lower bound and a shading-density floor produce
the full Jacobian-normalized thresholded scalar absorption.  The displayed
`hbudget` is the sole remaining lower scalar payment. -/
theorem deltaBCThresholdedScalarAbsorption_of_densityCardBudget
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    {geometryC plankB plankC : NNReal}
    (cert : ∀ i,
      DeltaBCDimensionsCertificate geometryC delta plankB plankC
        (D.family.bodyFamily i))
    (hplankC : 0 < plankC)
    (KT rawUnionFloor densityFloor : ENNReal)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrawUnionFloor : rawUnionFloor ≠ 0)
    (hKTNonzero : KT ≠ 0)
    (hdensity : densityFloor ≤ D.shading.shadingDensity)
    (hbudget :
      rawUnionFloor *
          (((plankAngleLevels (deltaBCThresholdedLevels cert hplankC)).card :
              ENNReal) * KT *
            deltaBCThresholdedCanonicalScale cert hplankC D.shading) ≤
        densityFloor *
          ((Fintype.card index : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2))) :
    DeltaBCThresholdedScalarAbsorption cert hplankC D.shading KT
      (affineJacobian
          (deltaBCNormalizationEquiv plankC hplankC) * rawUnionFloor) := by
  let e := deltaBCNormalizationEquiv plankC hplankC
  let J : ENNReal := affineJacobian e
  let levels := plankAngleLevels (deltaBCThresholdedLevels cert hplankC)
  let A := deltaBCThresholdedCanonicalScale cert hplankC D.shading
  have hrawAbsorb :
      rawUnionFloor * ((levels.card : ENNReal) * KT * A) ≤
        D.shading.shadingMass := by
    calc
      rawUnionFloor * ((levels.card : ENNReal) * KT * A) ≤
          densityFloor *
            ((Fintype.card index : ENNReal) *
              ((delta : ENNReal) ^ 2 / 2)) := by
        simpa only [levels, A] using hbudget
      _ ≤ D.shading.shadingDensity * D.actualFamilyVolume := by
        exact mul_le_mul' hdensity
          (card_mul_half_sq_le_actualFamilyVolume D hdeltaHalf)
      _ = D.shading.shadingMass := by
        simpa only [ActualTubeDatum.actualFamilyVolume] using
          shadingDensity_mul_familyVolume D.shading
  have hmassTransport :
      (deltaBCNormalizedShading plankC hplankC D.shading).shadingMass =
        J * D.shading.shadingMass := by
    simpa only [J, e, deltaBCNormalizedShading] using
      affineImageShading_shadingMass
        (deltaBCNormalizationEquiv plankC hplankC) D.shading
  have hnormalizedAbsorb :
      (J * rawUnionFloor) * ((levels.card : ENNReal) * KT * A) ≤
        (deltaBCNormalizedShading plankC hplankC D.shading).shadingMass := by
    rw [hmassTransport]
    calc
      (J * rawUnionFloor) * ((levels.card : ENNReal) * KT * A) =
          J * (rawUnionFloor * ((levels.card : ENNReal) * KT * A)) := by
        ac_rfl
      _ ≤ J * D.shading.shadingMass :=
        mul_le_mul' le_rfl hrawAbsorb
  refine ⟨?_, ?_⟩
  · exact deltaBCThresholdedCanonicalScale_ne_top_of_absorption
      D.shading cert hplankC KT rawUnionFloor hrawUnionFloor hKTNonzero
        (by simpa only [J, e, levels, A] using hnormalizedAbsorb)
  · simpa only [J, e, levels, A] using hnormalizedAbsorb

/-- Ready-to-use Equation (32) specialization.  All geometric row data and
the canonical-scale finiteness side condition are internal.  The remaining
lower and upper inputs are literal cross-multiplied scalar budgets. -/
theorem actualTube_eq32_of_lemma69_deltaBCThresholded_densityCardBudgets
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    {geometryC plankB plankC : NNReal}
    (cert : ∀ i,
      DeltaBCDimensionsCertificate geometryC delta plankB plankC
        (D.family.bodyFamily i))
    (hplankC : 0 < plankC)
    (a b : NNReal)
    (CF externalLoss rawUnionFloor KT densityFloor : ENNReal)
    (epsilon beta : Real)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrawUnionFloor : rawUnionFloor ≠ 0)
    (hKTNonzero : KT ≠ 0)
    (hKT : IsKatzTao KT D.family.bodyFamily)
    (hdensity : densityFloor ≤ D.shading.shadingDensity)
    (hlowerScalar :
      rawUnionFloor *
          (((plankAngleLevels (deltaBCThresholdedLevels cert hplankC)).card :
              ENNReal) * KT *
            deltaBCThresholdedCanonicalScale cert hplankC D.shading) ≤
        densityFloor *
          ((Fintype.card index : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)))
    (hupperScalar :
      (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) ≤
        (externalLoss * proposition66AFrostmanFactor delta a b
          (Fintype.card index) CF epsilon beta) * rawUnionFloor) :
    D.shading.averageMultiplicity ≤
      externalLoss * proposition66AFrostmanFactor delta a b
        (Fintype.card index) CF epsilon beta := by
  apply
    actualTube_eq32_of_lemma69_deltaBCThresholded_normalizedScalarPayments
      D cert hplankC a b CF externalLoss rawUnionFloor KT epsilon beta
        hdeltaHalf hKT
  · exact deltaBCThresholdedScalarAbsorption_of_densityCardBudget
      D cert hplankC KT rawUnionFloor densityFloor hdeltaHalf
        hrawUnionFloor hKTNonzero hdensity hlowerScalar
  · exact hupperScalar

#print axioms
  deltaBCThresholdedCanonicalScale_ne_top_of_absorption
#print axioms
  deltaBCThresholdedScalarAbsorption_of_densityCardBudget
#print axioms
  actualTube_eq32_of_lemma69_deltaBCThresholded_densityCardBudgets

end
end Family8Lemma69DeltaBCThresholdedDensityCardScalarProducerV1

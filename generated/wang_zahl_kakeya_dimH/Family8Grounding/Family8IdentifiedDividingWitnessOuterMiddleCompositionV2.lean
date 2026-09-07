import Family8Grounding.Family8IdentifiedDividingWitnessSourceTauFrozenProductV3
import Family8Grounding.Family8OuterMiddleFixedNuEndpointOrchestrationV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessOuterMiddleCompositionV2

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# The exact outer-middle-outer scalar composition

The long branch in Section 8 exposes three actual multiplicity estimates.
The first and third estimates have losses `delta ^ (-2 * eta)` and
`delta ^ (-eta)`, while the middle estimate has gain
`delta ^ (10 * eta)`.  This file proves all bookkeeping after those three
estimates and their literal triple-product decomposition have been produced.

The final theorem uses one identified dividing witness.  Consequently its
stage is definitionally `W.stage`, and the stage bound is discharged by
`W.stage_le`; no independent stage selector or conclusion-valued premise is
introduced here.
-/

/-- The two outside losses give exactly the aggregate loss used by the fixed
positive endpoint. -/
theorem outerLoss_mul_le_threeEta
    {delta : NNReal} {eta : Real} {firstLoss thirdLoss : ENNReal}
    (hdelta : 0 < delta)
    (hFirstLoss : firstLoss <= (delta : ENNReal) ^ (-2 * eta))
    (hThirdLoss : thirdLoss <= (delta : ENNReal) ^ (-eta)) :
    firstLoss * thirdLoss <= (delta : ENNReal) ^ (-3 * eta) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  calc
    firstLoss * thirdLoss <=
        (delta : ENNReal) ^ (-2 * eta) *
          (delta : ENNReal) ^ (-eta) :=
      mul_le_mul' hFirstLoss hThirdLoss
    _ = (delta : ENNReal) ^ (-3 * eta) := by
      rw [show -3 * eta = (-2 * eta) + (-eta) by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

/-- A literal triple-product decomposition and the three separate analytic
estimates imply the factorized inequality consumed by the fixed-nu
endpoint.  `hFactors` is only the normalization/volume recombination; it is
not an average-multiplicity conclusion. -/
theorem tripleProduct_le_outerMiddleFactorization
    {delta : NNReal} {eta : Real}
    {source firstAverage middleAverage thirdAverage : ENNReal}
    {firstLoss thirdLoss firstFactor middleFactor thirdFactor sourceRHS :
      ENNReal}
    (hTriple :
      source <= firstAverage * (middleAverage * thirdAverage))
    (hFirst : firstAverage <= firstLoss * firstFactor)
    (hMiddle : middleAverage <=
      (delta : ENNReal) ^ (10 * eta) * middleFactor)
    (hThird : thirdAverage <= thirdLoss * thirdFactor)
    (hFactors :
      firstFactor * (middleFactor * thirdFactor) <= sourceRHS) :
    source <=
      ((firstLoss * thirdLoss) * (delta : ENNReal) ^ (10 * eta)) *
        sourceRHS := by
  calc
    source <= firstAverage * (middleAverage * thirdAverage) := hTriple
    _ <= (firstLoss * firstFactor) *
        (((delta : ENNReal) ^ (10 * eta) * middleFactor) *
          (thirdLoss * thirdFactor)) :=
      mul_le_mul' hFirst (mul_le_mul' hMiddle hThird)
    _ = ((firstLoss * thirdLoss) *
          (delta : ENNReal) ^ (10 * eta)) *
        (firstFactor * (middleFactor * thirdFactor)) := by
      ac_rfl
    _ <= ((firstLoss * thirdLoss) *
          (delta : ENNReal) ^ (10 * eta)) * sourceRHS :=
      mul_le_mul' le_rfl hFactors

/-- The exact endpoint-shaped scalar output, before choosing a dividing
witness: the aggregate outside loss is existentially exposed together with
its honest `-3 eta` cap. -/
theorem exists_outerLoss_outerMiddleFactorization
    {delta : NNReal} {eta : Real}
    {source firstAverage middleAverage thirdAverage : ENNReal}
    {firstLoss thirdLoss firstFactor middleFactor thirdFactor sourceRHS :
      ENNReal}
    (hdelta : 0 < delta)
    (hTriple :
      source <= firstAverage * (middleAverage * thirdAverage))
    (hFirst : firstAverage <= firstLoss * firstFactor)
    (hFirstLoss : firstLoss <= (delta : ENNReal) ^ (-2 * eta))
    (hMiddle : middleAverage <=
      (delta : ENNReal) ^ (10 * eta) * middleFactor)
    (hThird : thirdAverage <= thirdLoss * thirdFactor)
    (hThirdLoss : thirdLoss <= (delta : ENNReal) ^ (-eta))
    (hFactors :
      firstFactor * (middleFactor * thirdFactor) <= sourceRHS) :
    exists outerLoss : ENNReal,
      outerLoss <= (delta : ENNReal) ^ (-3 * eta) /\
      source <=
        (outerLoss * (delta : ENNReal) ^ (10 * eta)) * sourceRHS := by
  refine ⟨firstLoss * thirdLoss, ?_, ?_⟩
  · exact outerLoss_mul_le_threeEta hdelta hFirstLoss hThirdLoss
  · exact tripleProduct_le_outerMiddleFactorization
      hTriple hFirst hMiddle hThird hFactors

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- One identified dividing witness supplies the stage in the exact shape
required by `mainLemmaOne_of_outerThree_middleTen_factorization`.  The five
remaining hypotheses transparently name the paper's geometric output:
literal triple decomposition, first outer estimate, middle estimate, third
outer estimate, and normalized factor recombination. -/
theorem exists_stage_outerLoss_outerMiddleFactorization
    (D : ActualTubeDatum delta index)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    {firstAverage middleAverage thirdAverage : ENNReal}
    {firstLoss thirdLoss firstFactor middleFactor thirdFactor : ENNReal}
    (hdelta : 0 < delta)
    (hTriple : D.shading.averageMultiplicity <=
      firstAverage * (middleAverage * thirdAverage))
    (hFirst : firstAverage <= firstLoss * firstFactor)
    (hFirstLoss : firstLoss <=
      (delta : ENNReal) ^ (-2 * P.eta W.stage))
    (hMiddle : middleAverage <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) * middleFactor)
    (hThird : thirdAverage <= thirdLoss * thirdFactor)
    (hThirdLoss : thirdLoss <=
      (delta : ENNReal) ^ (-P.eta W.stage))
    (hFactors : firstFactor * (middleFactor * thirdFactor) <=
      frostmanMultiplicityRHS
        delta D.actualFamilyVolume (targetEpsilon / 4) gamma) :
    exists j : Nat, exists outerLoss : ENNReal,
      j <= P.N /\
      outerLoss <= (delta : ENNReal) ^ (-3 * P.eta j) /\
      D.shading.averageMultiplicity <=
        (outerLoss * (delta : ENNReal) ^ (10 * P.eta j)) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (targetEpsilon / 4) gamma := by
  obtain ⟨outerLoss, hOuterLoss, hAverage⟩ :=
    exists_outerLoss_outerMiddleFactorization
      hdelta hTriple hFirst hFirstLoss hMiddle hThird hThirdLoss hFactors
  exact ⟨W.stage, outerLoss, W.stage_le, hOuterLoss, hAverage⟩

end Witness

#print axioms outerLoss_mul_le_threeEta
#print axioms tripleProduct_le_outerMiddleFactorization
#print axioms exists_outerLoss_outerMiddleFactorization
#print axioms Witness.exists_stage_outerLoss_outerMiddleFactorization

end

end Family8IdentifiedDividingWitnessOuterMiddleCompositionV2

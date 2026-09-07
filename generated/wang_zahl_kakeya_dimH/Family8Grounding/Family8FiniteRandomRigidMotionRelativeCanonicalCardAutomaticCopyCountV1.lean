import Family8Grounding.Family8FiniteRandomRigidMotionRelativeCanonicalCardSelectedCardBridgeV1
import Family8Grounding.Family8KatzTaoSamplingMultiplicityV1
import Family8Grounding.Family8SameSelectedQFibreWeightedCrossingValueTransportV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Automatic canonical copy count and arbitrary-slack payment

For the eighth-normalized source, assume only that its canonical Frostman
constant is nonzero and finite.  These two conditions force the contained
mass in the canonical quotient to be nonzero, so the canonical constant is
at least one.  Its natural ceiling therefore gives an actual positive finite
copy count `J` with the sharp two-sided comparison

`C <= J <= 2 * C`.

Consequently `Fin J` supplies the copied-cardinality input with the universal
copy loss `2`.  The remaining interpolation coefficient is
`greedyLoss * 16 ^ (1 - gamma / 2)`.  When `greedyLoss` is finite and the
epsilon gap is strict, the standard finite-constant threshold pays that
coefficient at every sufficiently small positive relative scale.

This file performs no rigid-motion or refinement selection.  It produces the
copy-count and scalar parts which such a geometric selection can use; it
assumes neither source admissibility nor a convex-plank multiplicity bound.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FiniteRandomRigidMotionRelativeCanonicalCardAutomaticCopyCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionRelativeCanonicalCardSelectedCardBridgeV1
open Family8GeneralizedFrostmanCanonicalCardInterpolationV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8KatzTaoSamplingMultiplicityV1
open Family8SameSelectedQFibreWeightedCrossingValueTransportV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- The canonical integer number of copies is the natural ceiling of the
eighth-normalized source canonical Frostman constant. -/
def relativeCanonicalCardCopyCount
    {sourceIndex : Type} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal} (source : ActualTubeDatum delta sourceIndex) : Nat :=
  katzTaoSamplingMultiplicity
    (sourceCanonicalFrostmanConstant (eighthNormalizedDatum source))

/-- A nonzero finite canonical quotient cannot have zero denominator.  This
is the only nondegeneracy step needed to obtain the canonical lower bound;
it uses no admissibility property of the source datum. -/
theorem eighth_source_containedMass_ne_zero_of_canonical_ne_zero_ne_top
    {sourceIndex : Type} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal} (source : ActualTubeDatum delta sourceIndex)
    (hC0 :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ 0)
    (hCtop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ ∞) :
    containedMass
        (eighthNormalizedDatum source).family.bodyFamily unitBallBody ≠ 0 := by
  let F := (eighthNormalizedDatum source).family.bodyFamily
  have hnumerator0 :
      maximalConcentration F * volume (unitBallBody : Set Space) ≠ 0 := by
    intro hzero
    apply hC0
    unfold sourceCanonicalFrostmanConstant canonicalFrostmanConstant
    rw [hzero, ENNReal.zero_div]
  intro hmass0
  apply hCtop
  unfold sourceCanonicalFrostmanConstant canonicalFrostmanConstant
  exact ENNReal.div_eq_top.mpr (Or.inl <| by
    simpa only [F] using And.intro hnumerator0 hmass0)

/-- Nonzero finiteness of the exact canonical constant already implies the
lower bound `1 <= C`; no separate source-admissibility premise is needed. -/
theorem one_le_eighth_sourceCanonicalFrostmanConstant_of_ne_zero_ne_top
    {sourceIndex : Type} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal} (source : ActualTubeDatum delta sourceIndex)
    (hC0 :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ 0)
    (hCtop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ ∞) :
    (1 : ENNReal) <=
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) := by
  change (1 : ENNReal) <= canonicalFrostmanConstant
    (eighthNormalizedDatum source).family.bodyFamily unitBallBody
  exact one_le_canonicalFrostmanConstant_of_containedMass_ne_zero
    (eighthNormalizedDatum source).family.bodyFamily unitBallBody
    (eighth_source_containedMass_ne_zero_of_canonical_ne_zero_ne_top
      source hC0 hCtop)

/-- The automatically chosen copy count is positive. -/
theorem relativeCanonicalCardCopyCount_pos
    {sourceIndex : Type} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal} (source : ActualTubeDatum delta sourceIndex)
    (hC0 :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ 0)
    (hCtop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ ∞) :
    0 < relativeCanonicalCardCopyCount source := by
  unfold relativeCanonicalCardCopyCount
  exact katzTaoSamplingMultiplicity_pos (pos_iff_ne_zero.mpr hC0) hCtop

/-- The natural ceiling retains the whole canonical Frostman constant from
below. -/
theorem eighth_sourceCanonicalFrostmanConstant_le_copyCount
    {sourceIndex : Type} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal} (source : ActualTubeDatum delta sourceIndex)
    (hCtop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ ∞) :
    sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) <=
      (relativeCanonicalCardCopyCount source : ENNReal) := by
  unfold relativeCanonicalCardCopyCount katzTaoSamplingMultiplicity
  apply (ENNReal.toReal_le_toReal hCtop ENNReal.coe_ne_top).mp
  simpa using Nat.le_ceil
    (sourceCanonicalFrostmanConstant (eighthNormalizedDatum source)).toReal

/-- The same ceiling costs at most twice the source canonical constant. -/
theorem copyCount_le_two_mul_eighth_sourceCanonicalFrostmanConstant
    {sourceIndex : Type} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal} (source : ActualTubeDatum delta sourceIndex)
    (hC0 :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ 0)
    (hCtop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ ∞) :
    (relativeCanonicalCardCopyCount source : ENNReal) <=
      2 * sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) := by
  unfold relativeCanonicalCardCopyCount
  exact katzTaoSamplingMultiplicity_coe_le_two_mul
    (one_le_eighth_sourceCanonicalFrostmanConstant_of_ne_zero_ne_top
      source hC0 hCtop)
    hCtop

/-- Every selected subset of the automatically chosen copied index type has
the canonical-cardinality bound with the now-produced copy loss `2`. -/
theorem selected_card_le_two_mul_eighth_sourceCanonical_mul_sourceCard
    {sourceIndex : Type} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal} (source : ActualTubeDatum delta sourceIndex)
    (selected : Finset
      (Fin (relativeCanonicalCardCopyCount source) × sourceIndex))
    (hC0 :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ 0)
    (hCtop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ ∞) :
    (selected.card : ENNReal) <=
      2 * sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) *
        (Fintype.card sourceIndex : ENNReal) := by
  apply
    selected_card_le_copyCardLoss_mul_eighth_sourceCanonical_mul_sourceCard
      source selected 2
  simpa only [Fintype.card_fin] using
    copyCount_le_two_mul_eighth_sourceCanonicalFrostmanConstant
      source hC0 hCtop

/-- The explicit relative-scale threshold which absorbs the complete
copy-count scalar with the universal copy loss `2`. -/
def relativeCanonicalCardCopyCountScalarThreshold
    (greedyLoss : ENNReal) (epsilonF epsilon gamma : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (greedyLoss * (8 * (2 : ENNReal)) ^ (1 - gamma / 2))
    (epsilon - epsilonF)

theorem relativeCanonicalCardCopyCountScalarThreshold_pos
    (greedyLoss : ENNReal) (epsilonF epsilon gamma : Real) :
    0 < relativeCanonicalCardCopyCountScalarThreshold
      greedyLoss epsilonF epsilon gamma :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem relativeCanonicalCardCopyCountScalarThreshold_le_one
    (greedyLoss : ENNReal) {epsilonF epsilon gamma : Real}
    (hgap : epsilonF < epsilon) :
    relativeCanonicalCardCopyCountScalarThreshold
        greedyLoss epsilonF epsilon gamma <= 1 :=
  finiteConstantSmallDeltaThreshold_le_one _ (sub_pos.mpr hgap)

/-- At every positive scale below the explicit threshold, finite greedy loss
and the produced copy loss `2` satisfy the exact scalar ledger consumed by
relative canonical-card interpolation. -/
theorem relativeCanonicalCard_copyCount_two_scalar_le
    {tau : NNReal} {greedyLoss : ENNReal}
    {epsilonF epsilon gamma : Real}
    (hgreedyTop : greedyLoss ≠ ∞)
    (hgap : epsilonF < epsilon) (hgamma : gamma <= 2)
    (htau : 0 < tau)
    (hsmall : tau <= relativeCanonicalCardCopyCountScalarThreshold
      greedyLoss epsilonF epsilon gamma) :
    greedyLoss * (8 * (2 : ENNReal)) ^ (1 - gamma / 2) *
        (tau : ENNReal) ^ (-epsilonF) <=
      (tau : ENNReal) ^ (-epsilon) := by
  let K : ENNReal :=
    greedyLoss * (8 * (2 : ENNReal)) ^ (1 - gamma / 2)
  have hp : 0 <= 1 - gamma / 2 := by linarith
  have hKtop : K ≠ ∞ := by
    dsimp only [K]
    exact ENNReal.mul_ne_top hgreedyTop
      (ENNReal.rpow_ne_top_of_nonneg hp (by norm_num))
  have hK : K <= (tau : ENNReal) ^ (-(epsilon - epsilonF)) := by
    exact finiteConstant_le_delta_negativePower hKtop (sub_pos.mpr hgap)
      htau (by
        simpa only [relativeCanonicalCardCopyCountScalarThreshold, K] using
          hsmall)
  have htau0 : (tau : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr htau.ne'
  have htauTop : (tau : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    greedyLoss * (8 * (2 : ENNReal)) ^ (1 - gamma / 2) *
          (tau : ENNReal) ^ (-epsilonF) =
        K * (tau : ENNReal) ^ (-epsilonF) := by rfl
    _ <= (tau : ENNReal) ^ (-(epsilon - epsilonF)) *
          (tau : ENNReal) ^ (-epsilonF) :=
      mul_le_mul' hK le_rfl
    _ = (tau : ENNReal) ^ (-epsilon) := by
      rw [<- ENNReal.rpow_add _ _ htau0 htauTop]
      congr 1
      ring

/-- One-shot numerical producer.  It chooses a positive integer copy count
with both sharp canonical comparisons and a positive uniform threshold below
which the exact relative canonical-card scalar ledger holds. -/
theorem exists_copyCount_and_relativeCanonicalCard_scalarThreshold
    {sourceIndex : Type} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal} (source : ActualTubeDatum delta sourceIndex)
    (hC0 :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ 0)
    (hCtop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) ≠ ∞)
    {greedyLoss : ENNReal} (hgreedyTop : greedyLoss ≠ ∞)
    {epsilonF epsilon gamma : Real}
    (hgap : epsilonF < epsilon) (hgamma : gamma <= 2) :
    exists J : Nat, 0 < J /\
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) <=
        (J : ENNReal) /\
      (J : ENNReal) <=
        2 * sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) /\
      exists tau0 : NNReal, 0 < tau0 /\ tau0 <= 1 /\
        forall tau : NNReal, 0 < tau -> tau <= tau0 ->
          greedyLoss * (8 * (2 : ENNReal)) ^ (1 - gamma / 2) *
              (tau : ENNReal) ^ (-epsilonF) <=
            (tau : ENNReal) ^ (-epsilon) := by
  refine ⟨relativeCanonicalCardCopyCount source,
    relativeCanonicalCardCopyCount_pos source hC0 hCtop,
    eighth_sourceCanonicalFrostmanConstant_le_copyCount source hCtop,
    copyCount_le_two_mul_eighth_sourceCanonicalFrostmanConstant
      source hC0 hCtop, ?_⟩
  refine ⟨relativeCanonicalCardCopyCountScalarThreshold
      greedyLoss epsilonF epsilon gamma,
    relativeCanonicalCardCopyCountScalarThreshold_pos
      greedyLoss epsilonF epsilon gamma,
    relativeCanonicalCardCopyCountScalarThreshold_le_one
      greedyLoss hgap, ?_⟩
  intro tau htau hsmall
  exact relativeCanonicalCard_copyCount_two_scalar_le hgreedyTop hgap hgamma
    htau hsmall

#print axioms relativeCanonicalCardCopyCount
#print axioms
  eighth_source_containedMass_ne_zero_of_canonical_ne_zero_ne_top
#print axioms
  one_le_eighth_sourceCanonicalFrostmanConstant_of_ne_zero_ne_top
#print axioms relativeCanonicalCardCopyCount_pos
#print axioms eighth_sourceCanonicalFrostmanConstant_le_copyCount
#print axioms
  copyCount_le_two_mul_eighth_sourceCanonicalFrostmanConstant
#print axioms
  selected_card_le_two_mul_eighth_sourceCanonical_mul_sourceCard
#print axioms relativeCanonicalCardCopyCountScalarThreshold
#print axioms relativeCanonicalCardCopyCountScalarThreshold_pos
#print axioms relativeCanonicalCardCopyCountScalarThreshold_le_one
#print axioms relativeCanonicalCard_copyCount_two_scalar_le
#print axioms
  exists_copyCount_and_relativeCanonicalCard_scalarThreshold

end
end Family8FiniteRandomRigidMotionRelativeCanonicalCardAutomaticCopyCountV1

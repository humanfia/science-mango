import Family8Grounding.Family8SameSelectedQFibreWeightedCrossingValueTransportV1
import Mathlib.Tactic

/-!
# Generic destination form of the weighted q-fibre value transport

The finite source loss is attached entirely to the literal source crossing.
The target estimate uses only the universal nondegeneracy of an actual first
crossing, so it should not require a legacy faithful-cover wrapper.  This
file exposes that weakest form for a destination crossing on any supplied
real coherent cover.  Later q-fresh connectors specialize the datum and
cover definitionally to the same successor object.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SameSelectedQFibreGenericWeightedCrossingValueTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8PaperFactorFiniteRunV2
open Family8SameSelectedQFibreCrossingValueTransportV1
open Family8SameSelectedQFibreWeightedCrossingValueTransportV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-! ## Universal target nondegeneracy -/

variable {destinationDelta : NNReal} {destinationIndex : Type}
  [Fintype destinationIndex] [DecidableEq destinationIndex]
  {destinationDepth : Nat}
  {Ddestination : ActualTubeDatum destinationDelta destinationIndex}
  {hDdestination : Ddestination.IsAdmissible}
  {Cdestination : CoherentStickyMultiscaleCover Ddestination.family}
  {Sdestination : FiniteScaleSequence destinationDelta destinationDepth}
  {destinationEpsilon : Real}
  {hDestinationEpsilon : 0 <= destinationEpsilon}
  {destinationEta : Nat -> Real} {N : Nat}

/-- Every literal first crossing has normalized canonical Frostman constant
at least one.  No relation to a source datum or hierarchy is required. -/
theorem one_le_actualCrossingValue
    (Wdestination : FirstParentwiseNormalizedCrossingWitness
      Ddestination hDdestination Cdestination Sdestination
        destinationEpsilon hDestinationEpsilon destinationEta N) :
    (1 : ENNReal) <= actualCrossingValue Wdestination := by
  let T := paperBufferedIntervalCover
    Ddestination hDdestination Cdestination Sdestination
    destinationEpsilon hDestinationEpsilon Wdestination.m
    Wdestination.rho Wdestination.buffered
  have htauPos : 0 < Sdestination.tau Wdestination.m :=
    hDdestination.delta_pos.trans_le
      (Sdestination.delta_le_tau Wdestination.m)
  have hmass0 : containedMass
      (T.fiberFamily Wdestination.q.1)
      (T.activeCoarseFamily Wdestination.q) ≠ 0 := by
    rw [containedMass_fiberFamily_parent_eq_familyVolume]
    exact (fiberFamilyVolume_pos T htauPos Wdestination.q).ne'
  unfold actualCrossingValue parentNormalizedFiberCFAt
  exact one_le_canonicalFrostmanConstant_of_containedMass_ne_zero
    (T.fiberFamily Wdestination.q.1)
    (T.activeCoarseFamily Wdestination.q) hmass0

/-! ## Literal source loss -/

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real}
  {Wsource : FirstParentwiseNormalizedCrossingWitness
    D hD C S epsilon hepsilon eta N}
  {step : SameObjectCrossingPaperStep Wsource}

/-- The exact card/floor loss is nonzero because the selected active parent
has a nonempty literal source fibre. -/
theorem sourceRawQFibreCardFloorLoss_ne_zero :
    sourceRawQFibreCardFloorLoss (Wsrc := Wsource) ≠ 0 := by
  unfold sourceRawQFibreCardFloorLoss
  apply ENNReal.div_ne_zero.2
  constructor
  · have hfiber :
        ((sourceRawCrossingCover (Wsrc := Wsource)).fiber
          Wsource.q.1).Nonempty := by
      obtain ⟨i, hi, hip⟩ :=
        (sourceRawCrossingCover (Wsrc := Wsource)).parent_surjective
          Wsource.q.1 Wsource.q.2
      exact ⟨i,
        ((sourceRawCrossingCover (Wsrc := Wsource)).mem_fiber
          i Wsource.q.1).2 ⟨hi, hip⟩⟩
    have hcard :
        0 < Fintype.card
          {i // i ∈ (sourceRawCrossingCover (Wsrc := Wsource)).fiber
            Wsource.q.1} := by
      simpa only [Fintype.card_coe] using Finset.card_pos.mpr hfiber
    exact_mod_cast hcard.ne'
  · exact sourceMassRatioFloor_ne_top (Wsrc := Wsource)

/-- Weakest target-polymorphic weighted value theorem.  Object consistency
is imposed later by typing `Wdestination` on the literal q-fibre successor
datum and cover; no relation is needed to prove this scalar estimate. -/
theorem crossingValue_le_cardFloorLoss_mul_anyDestination
    (step : SameObjectCrossingPaperStep Wsource)
    (Wdestination : FirstParentwiseNormalizedCrossingWitness
      Ddestination hDdestination Cdestination Sdestination
        destinationEpsilon hDestinationEpsilon destinationEta N) :
    actualCrossingValue Wsource <=
      sourceRawQFibreCardFloorLoss (Wsrc := Wsource) *
        actualCrossingValue Wdestination := by
  calc
    actualCrossingValue Wsource <=
        sourceRawQFibreCardFloorLoss (Wsrc := Wsource) :=
      sourceCrossingValue_le_cardFloorLoss step
    _ = sourceRawQFibreCardFloorLoss (Wsrc := Wsource) * 1 := by simp
    _ <= sourceRawQFibreCardFloorLoss (Wsrc := Wsource) *
          actualCrossingValue Wdestination := by
      gcongr
      exact one_le_actualCrossingValue Wdestination

#print axioms one_le_actualCrossingValue
#print axioms sourceRawQFibreCardFloorLoss_ne_zero
#print axioms crossingValue_le_cardFloorLoss_mul_anyDestination

end
end Family8SameSelectedQFibreGenericWeightedCrossingValueTransportV1

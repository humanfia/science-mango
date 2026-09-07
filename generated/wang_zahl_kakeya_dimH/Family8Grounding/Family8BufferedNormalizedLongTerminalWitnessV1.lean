import Family8Grounding.Family8RelevantDef212LongBufferedAdjacentUpperV1

/-!
# A normalized long-terminal witness on the genuine buffered parent pair

The older `NormalizedLongIntervalWitness` stores its adjacent estimate on
the raw coherent `tau -> theta` cover.  The selected-parent construction
instead gives an honest commuting pair whose upper tubes have radius
`theta + 4*tau`.  These covers are not definitionally equal.

This file records the selected pair literally and reruns the terminal branch
of the finite selector with that exact object.  It therefore supplies an
ADD-only consumer path without asserting a false equality with the raw
coherent interval cover.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8BufferedNormalizedLongTerminalWitnessV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CompatibleStickyScalePairCUniformFrostmanV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongSeparatedBufferedAdjacentFrostmanV1
open Family8LongSeparatedBufferedCompatiblePairV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalRelevantDef212InputsV5
open Family8ParameterLadderFourSeparationThresholdV1
open Family8ParameterLadderV1
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The literal long-terminal object delivered by the selected-parent route.
Its middle barrier remains on the coherent covers used by the selector, while
its adjacent upper is attached to the genuinely commuting buffered pair. -/
structure BufferedNormalizedLongTerminalWitness
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (P : ParameterLadder epsilon0 beta gamma)
    (S : FiniteScaleSequence delta depth) where
  m : Fin depth
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= P.N
  long : S.IsLong P.epsilon m
  compatiblePair :
    CompatibleStickyScalePair
      (longTauCover D C S m)
      (bufferedUpperScaleCover (longThetaCover D C S m) (4 * S.tau m))
  source_upper :
    parentNormalizedFiberCFMax (longTauCover D C S m) <=
      (((S.tau m / delta : NNReal) : ENNReal) ^ P.eta (stage - 1))
  adjacent_upper :
    parentNormalizedFiberCFMax
        (CompatibleStickyScalePair.intervalCover compatiblePair) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        P.eta (stage - 1))
  middle_lower : forall rho, S.IsBuffered P.epsilon m rho ->
    (((rho / S.tau m : NNReal) : ENNReal) ^ P.eta stage) <=
      normalizedFiberCFValueAt C S m rho

namespace BufferedNormalizedLongTerminalWitness

/-- A terminal barrier and relevant Definition 2.12 endpoint data produce the
literal buffered normalized witness at the terminal stage `P.N`. -/
noncomputable def of_longTerminalActualBarrier_relevantDef212
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    {K : NNReal}
    (H : RelevantFiniteSequenceDef212Inputs C S P.epsilon K)
    (delta0 : NNReal)
    (hdelta : delta <=
      Family8ParameterLadderFourSeparationThresholdV1.parameterLadderFourSeparatedDelta0
        P delta0)
    (hFine : D.family.refinement.refined.Nonempty)
    (m : Fin depth) (hlong : S.IsLong P.epsilon m)
    (hbarrier : forall rho : NNReal,
      (hbuffered : S.IsBuffered P.epsilon m rho) ->
        (((rho / S.tau m : NNReal) : ENNReal) ^ P.eta P.N) <=
          parentNormalizedFiberCFMax
            (C.intervalScaleCover (S.tau m) rho
              (S.delta_le_tau m)
              (actualDatum_tau_le_of_isBuffered
                D hD S P.epsilon_pos.le m rho hbuffered)
              (buffered_le_one S P.epsilon_pos.le m rho hbuffered)))
    (htauHalf : S.tau m <= (2 : NNReal)⁻¹)
    (hsourceError :
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^
          P.eta (P.N - 1)))
    (hadjacentError :
      relevantLongBufferedAdjacentError D C S K m <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          P.eta (P.N - 1))) :
    BufferedNormalizedLongTerminalWitness D C P S where
  m := m
  stage := P.N
  stage_pos := P.N_pos
  stage_le := le_rfl
  long := hlong
  compatiblePair :=
    relevantLongBufferedPair D hD C S P H delta0 hdelta hFine m hlong
  source_upper := by
    exact (relevantLongBufferedNormalizedEndpointBounds
      D hD C S P H delta0 hdelta hFine m hlong htauHalf
        hsourceError hadjacentError).1
  adjacent_upper := by
    exact (relevantLongBufferedNormalizedEndpointBounds
      D hD C S P H delta0 hdelta hFine m hlong htauHalf
        hsourceError hadjacentError).2
  middle_lower := by
    intro rho hbuffered
    rw [actualDatum_normalizedFiberCFValueAt_eq_of_isBuffered
      D hD C S P.epsilon_pos.le m rho hbuffered]
    exact hbarrier rho hbuffered

end BufferedNormalizedLongTerminalWitness

/-- The finite selector with its terminal branch attached to the actual
buffered selected-parent pair.  The all-large and first-crossing alternatives
are unchanged. -/
theorem allLarge_or_bufferedNormalizedLongTerminalWitness_or_firstCrossing
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    {K : NNReal}
    (H : RelevantFiniteSequenceDef212Inputs C S P.epsilon K)
    (delta0 : NNReal)
    (hdelta : delta <=
      Family8ParameterLadderFourSeparationThresholdV1.parameterLadderFourSeparatedDelta0
        P delta0)
    (hFine : D.family.refinement.refined.Nonempty)
    (htauHalf : forall m : Fin depth, S.IsLong P.epsilon m ->
      S.tau m <= (2 : NNReal)⁻¹)
    (hsourceError : forall m : Fin depth,
      forall _hlong : S.IsLong P.epsilon m,
        ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) <=
          (((S.tau m / delta : NNReal) : ENNReal) ^
            P.eta (P.N - 1)))
    (hadjacentError : forall m : Fin depth,
      forall _hlong : S.IsLong P.epsilon m,
        relevantLongBufferedAdjacentError D C S K m <=
          (((S.theta m / S.tau m : NNReal) : ENNReal) ^
            P.eta (P.N - 1))) :
    ((S.AllStepsLarge P.epsilon \/
        Nonempty (BufferedNormalizedLongTerminalWitness D C P S)) \/
      Nonempty (FirstActualNormalizedCrossingWitness
        D hD C S P.epsilon P.epsilon_pos.le P.eta P.N)) := by
  rcases
      Family8NormalizedCFDividingWitnessFiniteSelectionV6.CoherentStickyMultiscaleCover.allLarge_or_longTerminalActualBarrier_or_firstActualNormalizedCrossing
        D hD C S P.epsilon P.epsilon_pos.le P.eta P.N with
    hterminal | hfirst
  · left
    rcases hterminal with hall | ⟨m, hlong, hbarrier⟩
    · exact Or.inl hall
    · exact Or.inr ⟨
        BufferedNormalizedLongTerminalWitness.of_longTerminalActualBarrier_relevantDef212
          D hD C S P H delta0 hdelta hFine m hlong hbarrier
            (htauHalf m hlong) (hsourceError m hlong)
            (hadjacentError m hlong)⟩
  · right
    exact FirstActualNormalizedCrossingWitness.nonempty_of_selector_output
      hfirst

#print axioms
  BufferedNormalizedLongTerminalWitness.of_longTerminalActualBarrier_relevantDef212
#print axioms
  allLarge_or_bufferedNormalizedLongTerminalWitness_or_firstCrossing

end
end Family8BufferedNormalizedLongTerminalWitnessV1

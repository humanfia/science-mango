import Family8Grounding.Family8NormalizedCFDividingWitnessFiniteSelectionV6

open scoped ENNReal NNReal

namespace Family8NormalizedLongIntervalWitnessV1

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV6.CoherentStickyMultiscaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# A paper-normalized long-interval witness

The finite selector works with the parent-normalized canonical Frostman
constant.  The older `IdentifiedFrostmanDividingWitness` instead stores the
absolute `fiberDeltaMax`; converting between them costs the genuine parent
fibre-mass ratio and therefore cannot be a definitional rewrite.

This structure retains the selector's literal normalized quantities.  It is
the honest stopping object for the Eq. (45)--(46) route and prevents the
scale-ratio loss from being silently discarded.
-/


/-- A selected long interval with all three paper-normalized values attached
to their literal coherent covers. -/
structure NormalizedLongIntervalWitness
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (C : CoherentStickyMultiscaleCover fine)
    {depth : Nat} (N : Nat) (epsilon : Real) (eta : Nat -> Real)
    (S : FiniteScaleSequence delta depth) where
  m : Fin depth
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  long : S.IsLong epsilon m
  source_upper :
    parentNormalizedFiberCFMax
        (C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))) <=
      (((S.tau m / delta : NNReal) : ENNReal) ^ eta (stage - 1))
  adjacent_upper :
    parentNormalizedFiberCFMax
        (C.intervalScaleCover (S.tau m) (S.theta m)
          (S.delta_le_tau m) (S.tau_le_theta m)
          (S.theta_le_one m)) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  middle_lower : forall rho, S.IsBuffered epsilon m rho ->
    (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
      normalizedFiberCFValueAt C S m rho

namespace NormalizedLongIntervalWitness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The literal long-terminal branch of V6 becomes a normalized witness as
soon as the two genuine outside estimates at stage `N - 1` are available. -/
def of_longTerminalActualBarrier
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (hepsilon : 0 <= epsilon) (hN : 1 <= N)
    (m : Fin depth) (hlong : S.IsLong epsilon m)
    (hbarrier : forall rho : NNReal,
      (hbuffered : S.IsBuffered epsilon m rho) ->
        (((rho / S.tau m : NNReal) : ENNReal) ^ eta N) <=
          parentNormalizedFiberCFMax
            (C.intervalScaleCover (S.tau m) rho
              (S.delta_le_tau m)
              (actualDatum_tau_le_of_isBuffered
                D hD S hepsilon m rho hbuffered)
              (buffered_le_one S hepsilon m rho hbuffered)))
    (hsource :
      parentNormalizedFiberCFMax
          (C.base.cover (S.tau m) (S.delta_le_tau m)
            ((S.tau_le_theta m).trans (S.theta_le_one m))) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1)))
    (hadjacent :
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (N - 1))) :
    NormalizedLongIntervalWitness D.family C N epsilon eta S where
  m := m
  stage := N
  stage_pos := hN
  stage_le := le_rfl
  long := hlong
  source_upper := hsource
  adjacent_upper := hadjacent
  middle_lower := by
    intro rho hbuffered
    rw [actualDatum_normalizedFiberCFValueAt_eq_of_isBuffered
      D hD C S hepsilon m rho hbuffered]
    exact hbarrier rho hbuffered

end NormalizedLongIntervalWitness

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- V6 with its long-terminal alternative converted to the faithful
normalized witness.  The first strict crossing is preserved verbatim for the
recursive `G'` branch; it is not weakened to a conclusion-valued callback. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstActualNormalizedCrossing
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) (hN : 1 <= N)
    (hsource : forall m : Fin depth,
      parentNormalizedFiberCFMax
          (C.base.cover (S.tau m) (S.delta_le_tau m)
            ((S.tau_le_theta m).trans (S.theta_le_one m))) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1)))
    (hadjacent : forall m : Fin depth,
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (N - 1))) :
    (S.AllStepsLarge epsilon ∨
      Nonempty
        (NormalizedLongIntervalWitness D.family C N epsilon eta S)) ∨
      ∃ stage : Nat, stage <= N ∧
        (∃ m : Fin depth, ∃ rho : NNReal,
          ∃ _hnotLarge : ¬ S.IsLarge epsilon m,
          ∃ hbuffered : S.IsBuffered epsilon m rho,
            parentNormalizedFiberCFMax
                (C.intervalScaleCover (S.tau m) rho
                  (S.delta_le_tau m)
                  (actualDatum_tau_le_of_isBuffered
                    D hD S hepsilon m rho hbuffered)
                  (buffered_le_one S hepsilon m rho hbuffered)) <
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) ∧
        ∀ earlier : Nat, earlier < stage ->
          ∀ m : Fin depth, ¬ S.IsLarge epsilon m ->
            ∀ rho : NNReal, (hbuffered : S.IsBuffered epsilon m rho) ->
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta earlier) <=
                parentNormalizedFiberCFMax
                  (C.intervalScaleCover (S.tau m) rho
                    (S.delta_le_tau m)
                    (actualDatum_tau_le_of_isBuffered
                      D hD S hepsilon m rho hbuffered)
                    (buffered_le_one S hepsilon m rho hbuffered)) := by
  rcases
      allLarge_or_longTerminalActualBarrier_or_firstActualNormalizedCrossing
        D hD C S epsilon hepsilon eta N with
    hterminal | hfirst
  · left
    rcases hterminal with hall | ⟨m, hlong, hbarrier⟩
    · exact Or.inl hall
    · exact Or.inr ⟨
        NormalizedLongIntervalWitness.of_longTerminalActualBarrier
          D hD C S hepsilon hN m hlong hbarrier
            (hsource m) (hadjacent m)⟩
  · exact Or.inr hfirst

#print axioms NormalizedLongIntervalWitness.of_longTerminalActualBarrier
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstActualNormalizedCrossing

end CoherentStickyMultiscaleCover

end
end Family8NormalizedLongIntervalWitnessV1

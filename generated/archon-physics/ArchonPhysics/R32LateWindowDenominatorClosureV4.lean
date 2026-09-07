import ArchonPhysics.R32ConcreteLateWindowPersistenceV3

/-!
# R32: automatic late-window denominator closure

Raw `l1` closeness to the unit-total frozen two-band profile forces total
weight at least `1 - epsilon`.  This file feeds that exact floor into the
corrected V2 reduced/canonical bridge.  The resulting normalization loss is
`2 * epsilon / (1 - epsilon)`, and `epsilon <= 1 / 33` preserves a canonical
gap of at least `1 / 16`.

No persistence event, probability estimate, hitting time, kinetic limit, or
thermalization conclusion is introduced.
-/

namespace ArchonPhysics.R32LateWindowDenominatorClosureV4

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.R32ConcreteLateWindowPersistenceV3
open ArchonPhysics.R32FrozenEnergyDilution
open ArchonPhysics.R32LateWindowNormalizationStability

noncomputable section

/-! ## Raw distance closes the denominator -/

/-- Reverse triangle inequality for total weight, specialized to the exact
unit-total frozen profile. -/
theorem one_sub_le_totalWeight_of_l1Distance_frozen
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (w :
      ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N ->
        Real)
    (epsilon : Real)
    (hraw : l1Distance w (frozenTwoBandEnergy N) <= epsilon) :
    1 - epsilon <= totalWeight w := by
  have hsum : |totalWeight w - 1| <= epsilon := by
    calc
      |totalWeight w - 1| =
          |∑ k :
            ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
            (w k - frozenTwoBandEnergy N k)| := by
        unfold totalWeight
        rw [Finset.sum_sub_distrib, sum_frozenTwoBandEnergy_eq_one hN]
      _ <= ∑ k :
          ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
          |w k - frozenTwoBandEnergy N k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = l1Distance w (frozenTwoBandEnergy N) := rfl
      _ <= epsilon := hraw
  have hlower := (abs_le.mp hsum).1
  linarith

/-- Raw closeness of the exact reduced positive-mode late-window profile
supplies the floor `1 - epsilon`. -/
theorem one_sub_le_reducedPositiveLateWindowTotalWeight_of_raw_close
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (m : Lattice.PositiveMassConfig N)
    (z : Real -> ReducedPhaseSpace m) (mu T epsilon : Real)
    (hraw :
      l1Distance
          (lateWindowAverage
            (reducedTrajectoryPositiveEnergyProfile m z) mu T)
          (frozenTwoBandEnergy N) <= epsilon) :
    1 - epsilon <=
      totalWeight
        (lateWindowAverage
          (reducedTrajectoryPositiveEnergyProfile m z) mu T) :=
  one_sub_le_totalWeight_of_l1Distance_frozen hN _ epsilon hraw

/-! ## Reduced and canonical exact-observable consequences -/

/-- A raw reduced physical late-window error below one needs no external
energy-denominator premise. -/
theorem reducedTrajectoryPositiveLateWindowL1Distance_lower_of_raw_close
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z : Real -> ReducedPhaseSpace m) (mu T epsilon : Real)
    (hepsilonOne : epsilon < 1)
    (hraw :
      l1Distance
          (lateWindowAverage
            (reducedTrajectoryPositiveEnergyProfile m z) mu T)
          (frozenTwoBandEnergy N) <= epsilon) :
    (1 / 8 : Real) - (2 / (1 - epsilon)) * epsilon <=
      reducedTrajectoryPositiveLateWindowL1Distance m z mu T := by
  have hdenominator : 1 - epsilon <=
      totalWeight
        (lateWindowAverage
          (reducedTrajectoryPositiveEnergyProfile m z) mu T) :=
    one_sub_le_reducedPositiveLateWindowTotalWeight_of_raw_close
      hN m z mu T epsilon hraw
  have hlower := normalized_windowProfile_distance_from_uniform_lower
    hN
    (fun _U : Real =>
      lateWindowAverage (reducedTrajectoryPositiveEnergyProfile m z) mu T)
    ({T} : Set Real) (1 - epsilon) epsilon (sub_pos.mpr hepsilonOne)
    (by
      intro _U _hU
      exact hdenominator)
    (by
      intro _U _hU
      exact hraw)
    T (Set.mem_singleton T)
  rw [frozenPositiveUniformEnergy_eq_positiveModeMask m hsimple] at hlower
  simpa [reducedTrajectoryPositiveLateWindowL1Distance] using hlower

/-- Canonical exact-observable lower bound with the automatic floor
`1 - epsilon`. -/
theorem canonicalFrozenLateWindowL1Distance_lower_of_raw_close
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)))
    (z : Real -> ReducedPhaseSpace
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega))
    (mu T epsilon : Real) (hepsilonOne : epsilon < 1)
    (hmatch : forall t,
      canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta g (1 / 4) omega, t) =
        embedReducedPoint
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t))
    (hraw :
      l1Distance
          (lateWindowAverage
            (reducedTrajectoryPositiveEnergyProfile
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) z) mu T)
          (frozenTwoBandEnergy N) <= epsilon) :
    (1 / 8 : Real) - (2 / (1 - epsilon)) * epsilon <=
      canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu T omega := by
  let m := canonicalIIDMassPhaseEnsemble.restrictPositiveMass
    (N := N) omega
  have hlower :=
    reducedTrajectoryPositiveLateWindowL1Distance_lower_of_raw_close
      hN m hsimple z mu T epsilon hepsilonOne hraw
  have hobservable :
      canonicalFrozenLateWindowL1Distance
          (N := N) kappa beta g hbeta (1 / 4) mu T omega =
        reducedTrajectoryPositiveLateWindowL1Distance m z mu T := by
    exact sampledPositiveLateWindowL1Distance_eq_reduced_of_match
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g (1 / 4))
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
      kappa beta g omega z hmatch mu T
  rw [hobservable]
  exact hlower

/-- The automatic-floor threshold `epsilon <= 1 / 33` preserves a canonical
late-window distance of at least `1 / 16`. -/
theorem one_sixteenth_le_canonicalFrozenLateWindowL1Distance_of_raw_close
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)))
    (z : Real -> ReducedPhaseSpace
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega))
    (mu T epsilon : Real) (hepsilon : 0 <= epsilon)
    (hbudget : epsilon <= 1 / 33)
    (hmatch : forall t,
      canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta g (1 / 4) omega, t) =
        embedReducedPoint
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t))
    (hraw :
      l1Distance
          (lateWindowAverage
            (reducedTrajectoryPositiveEnergyProfile
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) z) mu T)
          (frozenTwoBandEnergy N) <= epsilon) :
    (1 / 16 : Real) <=
      canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu T omega := by
  have hepsilonOne : epsilon < 1 := by
    linarith
  have hlower := canonicalFrozenLateWindowL1Distance_lower_of_raw_close
    hN kappa beta g hbeta omega hsimple z mu T epsilon hepsilonOne
    hmatch hraw
  have hnormalizedBudget :
      (2 / (1 - epsilon)) * epsilon <= (1 / 16 : Real) := by
    calc
      (2 / (1 - epsilon)) * epsilon =
          (2 * epsilon) / (1 - epsilon) := by ring
      _ <= (1 / 16 : Real) := by
        rw [div_le_iff₀ (sub_pos.mpr hepsilonOne)]
        linarith
  linarith

#print axioms one_sub_le_totalWeight_of_l1Distance_frozen
#print axioms reducedTrajectoryPositiveLateWindowL1Distance_lower_of_raw_close
#print axioms canonicalFrozenLateWindowL1Distance_lower_of_raw_close
#print axioms one_sixteenth_le_canonicalFrozenLateWindowL1Distance_of_raw_close

end

end ArchonPhysics.R32LateWindowDenominatorClosureV4

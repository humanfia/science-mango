import ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
import ArchonPhysics.GlobalReducedParametricFlowAdapter
import ArchonPhysics.R32CanonicalFreeFlowIdentificationV2
import ArchonPhysics.R32CanonicalModalErrorReadbackV1
import ArchonPhysics.R32FrozenEnergyDilution
import ArchonPhysics.R32ModalEnergyL1Stability

/-!
# R32 canonical/reduced modal readback

This file transfers the coefficient-exact canonical Parseval identity and the
canonical zero-coupling frozen modal profile to the genuine reduced
trajectories supplied by a physical realization.  It also records the exact
free modal norm and the resulting dimension-free raw modal-energy `L1` bound.
-/

namespace ArchonPhysics.R32CanonicalReducedModalReadbackV1

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.CanonicalRandomMicroscopicCertificate
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.FiniteModalEnergyL1Stability
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.R32CanonicalDuhamelForceBridgeV3
open ArchonPhysics.R32CanonicalExactFreeBridgeV3
open ArchonPhysics.R32CanonicalFreeFlowIdentificationV2
open ArchonPhysics.R32CanonicalModalErrorReadbackV1
open ArchonPhysics.R32DiluteNonlinearStability
open ArchonPhysics.R32FrozenEnergyDilution
open ArchonPhysics.R32ModalEnergyL1Stability
open ArchonPhysics.R32WeightedModalErrorParseval
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform

noncomputable section

variable {N : Nat} [NeZero N]

/-- The weighted modal vector read from the ambient canonical flow is exactly
the one read from any matching reduced trajectory. -/
theorem canonicalWeightedOrderedHarmonicPhaseVector_eq_reduced_of_match
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace)
    (z : Real → ReducedPhaseSpace (canonicalMass (N := N) omega))
    (hmatch : ∀ time,
      canonicalRandomMassPhaseGlobalFlow N kappa beta coupling hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta coupling a omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta coupling (z time))
    (time : Real) :
    canonicalWeightedOrderedHarmonicPhaseVector (N := N)
        kappa beta coupling hbeta a omega time =
      reducedOrderedHarmonicPhaseVector
        (canonicalMass (N := N) omega) (z time) := by
  funext mode
  unfold canonicalWeightedOrderedHarmonicPhaseVector
    weightedOrderedHarmonicPhaseVector reducedOrderedHarmonicPhaseVector
    canonicalMassWeightedPositionPath canonicalMassWeightedMomentumPath
    massWeightedPosition massWeightedMomentum
    canonicalPhysicalPositionPath canonicalPhysicalMomentumPath
  rw [hmatch time]
  rfl

/-- Exact coefficient-one Parseval identity in the genuine reduced phase
space, after matching both the actual and zero-coupling ambient flows. -/
theorem reducedModalDistance_eq_canonicalErrorEnergy_of_matches
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (zExact zFree : Real →
      ReducedPhaseSpace (canonicalMass (N := N) omega))
    (hmatchExact : ∀ time,
      canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta g a omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta g (zExact time))
    (hmatchFree : ∀ time,
      canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta 0 a omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta 0 (zFree time))
    (time : Real) :
    phaseSpaceL2Distance
        (reducedOrderedHarmonicPhaseVector
          (canonicalMass (N := N) omega) (zExact time))
        (reducedOrderedHarmonicPhaseVector
          (canonicalMass (N := N) omega) (zFree time)) =
      canonicalErrorEnergy (N := N)
        kappa beta g hbeta a omega time := by
  rw [← canonicalWeightedOrderedHarmonicPhaseVector_eq_reduced_of_match
      kappa beta g hbeta a omega zExact hmatchExact time,
    ← canonicalWeightedOrderedHarmonicPhaseVector_eq_reduced_of_match
      kappa beta 0 hbeta a omega zFree hmatchFree time]
  exact canonicalWeightedModalDistance_eq_canonicalErrorEnergy
    kappa beta g hbeta a omega hsimple time

/-- A reduced trajectory matching the canonical zero-coupling flow has the
frozen two-band energy in every ordered mode and at every time. -/
theorem reducedFreeModeEnergy_eq_frozen_of_match
    (hN : 3 ≤ N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (zFree : Real → ReducedPhaseSpace (canonicalMass (N := N) omega))
    (hmatchFree : ∀ time,
      canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta 0 (1 / 4) omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta 0 (zFree time))
    (time : Real) (mode : OrderedModeIndex N) :
    reducedPhysicalOrderedModeEnergy
        (canonicalMass (N := N) omega) (zFree time) mode =
      frozenTwoBandEnergy N mode := by
  rw [← sampledPhysicalOrderedModeEnergyAlongFlow_eq_reduced_at
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta 0 (1 / 4))
    (canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta)
    kappa beta 0 omega zFree hmatchFree time mode]
  exact canonicalFreeFlowModeEnergy_eq_frozenTwoBandEnergy
    hN kappa beta hbeta omega hsimple time mode

/-- Unit frozen modal energy is exactly a `sqrt 2` phase-space norm. -/
theorem reducedFreePhaseSpaceL2Norm_eq_sqrt_two
    (hN : 3 ≤ N) (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (zFree : Real → ReducedPhaseSpace m)
    (hFreeEnergy : ∀ time mode,
      reducedPhysicalOrderedModeEnergy m (zFree time) mode =
        frozenTwoBandEnergy N mode)
    (time : Real) :
    phaseSpaceL2Norm
        (reducedOrderedHarmonicPhaseVector m (zFree time)) =
      Real.sqrt 2 := by
  have hpoint : ∀ mode : OrderedModeIndex N,
      ‖reducedOrderedHarmonicPhaseVector m (zFree time) mode‖ ^ 2 =
        2 * frozenTwoBandEnergy N mode := by
    intro mode
    have hmode := harmonicEnergyProfile_reducedOrderedHarmonicPhaseVector
      m hsimple (zFree time) mode
    rw [hFreeEnergy time mode] at hmode
    unfold harmonicEnergyProfile at hmode
    linarith
  unfold phaseSpaceL2Norm amplitudeL2Norm
  congr 1
  calc
    (∑ mode : OrderedModeIndex N,
        ‖reducedOrderedHarmonicPhaseVector m (zFree time) mode‖ ^ 2) =
        ∑ mode : OrderedModeIndex N,
          2 * frozenTwoBandEnergy N mode := by
      exact Finset.sum_congr rfl fun mode _hmode => hpoint mode
    _ = 2 * ∑ mode : OrderedModeIndex N,
        frozenTwoBandEnergy N mode := by rw [Finset.mul_sum]
    _ = 2 := by rw [sum_frozenTwoBandEnergy_eq_one hN, mul_one]

/-- The physical bond seminorm is bounded by the complete weighted modal
phase-space norm, with coefficient one. -/
theorem norm_massWeightedBond_le_phaseSpaceL2Norm
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (x y : WeightedConfiguration N) :
    ‖massWeightedBond m x‖ ≤
      phaseSpaceL2Norm (weightedOrderedHarmonicPhaseVector m x y) := by
  have hphase := phaseSpaceL2Norm_weighted_sq m hsimple x y
  have hbond := norm_massWeightedBond_sq m x
  change ‖massWeightedBond m x‖ ^ 2 =
    @inner Real (WeightedConfiguration N) _ x (harmonicOperator m x) at hbond
  have hphase0 :
      0 ≤ phaseSpaceL2Norm
        (weightedOrderedHarmonicPhaseVector m x y) :=
    amplitudeL2Norm_nonneg _
  have hbond0 : 0 ≤ ‖massWeightedBond m x‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖y‖]

/-- The unit canonical free orbit has a dimension-free physical bond `L2`
bound.  This is the exact premise needed by the V3 Duhamel bootstrap. -/
theorem norm_canonicalFreePhysicalBond_le_sqrt_two_of_match
    (hN : 3 ≤ N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (zFree : Real → ReducedPhaseSpace (canonicalMass (N := N) omega))
    (hmatchFree : ∀ time,
      canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta 0 (1 / 4) omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta 0 (zFree time))
    (time : Real) :
    ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta (1 / 4) omega time)‖ ≤
      Real.sqrt 2 := by
  let m := canonicalMass (N := N) omega
  let x := canonicalMassWeightedPositionPath (N := N)
    kappa beta 0 hbeta (1 / 4) omega time
  let y := canonicalMassWeightedMomentumPath (N := N)
    kappa beta 0 hbeta (1 / 4) omega time
  have hfreeEnergy : ∀ t mode,
      reducedPhysicalOrderedModeEnergy m (zFree t) mode =
        frozenTwoBandEnergy N mode := by
    intro t mode
    exact reducedFreeModeEnergy_eq_frozen_of_match
      hN kappa beta hbeta omega hsimple zFree hmatchFree t mode
  have hphaseNorm :
      phaseSpaceL2Norm (weightedOrderedHarmonicPhaseVector m x y) =
        Real.sqrt 2 := by
    change phaseSpaceL2Norm
        (canonicalWeightedOrderedHarmonicPhaseVector (N := N)
          kappa beta 0 hbeta (1 / 4) omega time) = Real.sqrt 2
    rw [canonicalWeightedOrderedHarmonicPhaseVector_eq_reduced_of_match
      kappa beta 0 hbeta (1 / 4) omega zFree hmatchFree time]
    exact reducedFreePhaseSpaceL2Norm_eq_sqrt_two
      hN m hsimple zFree hfreeEnergy time
  have hbond : ‖massWeightedBond m x‖ ≤
      phaseSpaceL2Norm (weightedOrderedHarmonicPhaseVector m x y) :=
    norm_massWeightedBond_le_phaseSpaceL2Norm m hsimple x y
  have hbondReadback : massWeightedBond m x =
      bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta (1 / 4) omega time) := by
    change massWeightedBond m
        (sqrtMassTransform m
          (canonicalPhysicalPositionPath (N := N)
            kappa beta 0 hbeta (1 / 4) omega time)) = _
    exact massWeightedBond_sqrtMassTransform m _
  rw [hbondReadback, hphaseNorm] at hbond
  exact hbond

/-- Dimension-free raw modal-energy error obtained from the exact canonical
error energy and the unit free modal norm. -/
theorem reducedModalEnergyL1_le_canonicalErrorPolynomial_of_matches
    (hN : 3 ≤ N) (kappa beta g : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (zExact zFree : Real →
      ReducedPhaseSpace (canonicalMass (N := N) omega))
    (hmatchExact : ∀ time,
      canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta g (1 / 4) omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta g (zExact time))
    (hmatchFree : ∀ time,
      canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta 0 (1 / 4) omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta 0 (zFree time))
    (time : Real) :
    (∑ mode : OrderedModeIndex N,
      |reducedPhysicalOrderedModeEnergy
          (canonicalMass (N := N) omega) (zExact time) mode -
        reducedPhysicalOrderedModeEnergy
          (canonicalMass (N := N) omega) (zFree time) mode|) ≤
      (1 / 2 : Real) *
        canonicalErrorEnergy (N := N)
          kappa beta g hbeta (1 / 4) omega time *
        (canonicalErrorEnergy (N := N)
            kappa beta g hbeta (1 / 4) omega time +
          2 * Real.sqrt 2) := by
  let m := canonicalMass (N := N) omega
  let W := reducedOrderedHarmonicPhaseVector m (zExact time)
  let WFree := reducedOrderedHarmonicPhaseVector m (zFree time)
  let error := canonicalErrorEnergy (N := N)
    kappa beta g hbeta (1 / 4) omega time
  have hdistance : phaseSpaceL2Distance W WFree = error := by
    exact reducedModalDistance_eq_canonicalErrorEnergy_of_matches
      kappa beta g hbeta (1 / 4) omega hsimple
      zExact zFree hmatchExact hmatchFree time
  have hfreeEnergy : ∀ t mode,
      reducedPhysicalOrderedModeEnergy m (zFree t) mode =
        frozenTwoBandEnergy N mode := by
    intro t mode
    exact reducedFreeModeEnergy_eq_frozen_of_match
      hN kappa beta hbeta omega hsimple zFree hmatchFree t mode
  have hfreeNorm : phaseSpaceL2Norm WFree = Real.sqrt 2 := by
    exact reducedFreePhaseSpaceL2Norm_eq_sqrt_two
      hN m hsimple zFree hfreeEnergy time
  have hactualNorm : phaseSpaceL2Norm W ≤ error + Real.sqrt 2 := by
    calc
      phaseSpaceL2Norm W ≤
          phaseSpaceL2Distance W WFree + phaseSpaceL2Norm WFree :=
        phaseSpaceL2Norm_le_distance_add W WFree
      _ = error + Real.sqrt 2 := by rw [hdistance, hfreeNorm]
  have hbase := reducedPhysicalOrderedModeEnergy_l1_le
    m hsimple (zExact time) (zFree time)
  change (∑ mode : OrderedModeIndex N,
      |reducedPhysicalOrderedModeEnergy m (zExact time) mode -
        reducedPhysicalOrderedModeEnergy m (zFree time) mode|) ≤
    (1 / 2 : Real) * phaseSpaceL2Distance W WFree *
      (phaseSpaceL2Norm W + phaseSpaceL2Norm WFree) at hbase
  calc
    (∑ mode : OrderedModeIndex N,
      |reducedPhysicalOrderedModeEnergy m (zExact time) mode -
        reducedPhysicalOrderedModeEnergy m (zFree time) mode|) ≤
        (1 / 2 : Real) * phaseSpaceL2Distance W WFree *
          (phaseSpaceL2Norm W + phaseSpaceL2Norm WFree) := hbase
    _ = (1 / 2 : Real) * error *
          (phaseSpaceL2Norm W + Real.sqrt 2) := by
      rw [hdistance, hfreeNorm]
    _ ≤ (1 / 2 : Real) * error *
          ((error + Real.sqrt 2) + Real.sqrt 2) := by
      gcongr
      exact mul_nonneg (by norm_num)
        (canonicalErrorEnergy_nonneg
          kappa beta g hbeta (1 / 4) omega time)
    _ = (1 / 2 : Real) * error *
          (error + 2 * Real.sqrt 2) := by ring

#print axioms canonicalWeightedOrderedHarmonicPhaseVector_eq_reduced_of_match
#print axioms reducedModalDistance_eq_canonicalErrorEnergy_of_matches
#print axioms reducedFreeModeEnergy_eq_frozen_of_match
#print axioms reducedFreePhaseSpaceL2Norm_eq_sqrt_two
#print axioms norm_massWeightedBond_le_phaseSpaceL2Norm
#print axioms norm_canonicalFreePhysicalBond_le_sqrt_two_of_match
#print axioms reducedModalEnergyL1_le_canonicalErrorPolynomial_of_matches

end

end ArchonPhysics.R32CanonicalReducedModalReadbackV1

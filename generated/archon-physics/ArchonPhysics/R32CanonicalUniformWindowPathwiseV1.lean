import ArchonPhysics.PositiveHarmonicEnergyAlongCoerciveFlow
import ArchonPhysics.R32CanonicalPhysicalFreeBondWholeWindow
import ArchonPhysics.R32CanonicalReducedModalReadbackV1
import ArchonPhysics.R32ConcreteLateWindowPersistenceV3
import ArchonPhysics.R32LateWindowDenominatorClosureV4
import ArchonPhysics.R32PhysicalSignedCanonicalFreeBondBridge

/-!
# R32 canonical uniform-window pathwise persistence

On one physical realization, a single free-orbit dilute event on the full
kinetic window controls every shorter late-window endpoint.  The V3 Duhamel
bootstrap gives a uniform harmonic error `E`; exact modal readback converts it
to the raw loss `rho = E (E + 2 sqrt(2)) / 2`; continuity supplies all interval
integrability; and the V4 denominator closure gives the variable-`rho`
normalized lower bound.  No fixed numerical threshold or persistence
conclusion is assumed.
-/

namespace ArchonPhysics.R32CanonicalUniformWindowPathwiseV1

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.CanonicalRandomMicroscopicCertificate
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.FiniteModalEnergyL1Stability
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveHarmonicEnergyAlongCoerciveFlow
open ArchonPhysics.R32CanonicalDuhamelForceBridgeV3
open ArchonPhysics.R32CanonicalExactFreeBridgeV3
open ArchonPhysics.R32CanonicalPhysicalFreeBondWholeWindow
open ArchonPhysics.R32CanonicalReducedModalReadbackV1
open ArchonPhysics.R32ConcreteLateWindowPersistenceV3
open ArchonPhysics.R32DiluteBootstrapClosureCompleteV3
open ArchonPhysics.R32DiluteNonlinearStability
open ArchonPhysics.R32FrozenEnergyDilution
open ArchonPhysics.R32LateWindowDenominatorClosureV4
open ArchonPhysics.R32ModalEnergyL1Stability
open ArchonPhysics.R32PhysicalSignedCanonicalFreeBondBridge
open ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final
open ArchonPhysics.R32WeightedModalErrorParseval
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- Uniform coefficient-one modal distance budget produced by the V3
kinetic-window bootstrap. -/
def canonicalKineticModalErrorBudget
    (kappa beta C T g : Real) : Real :=
  kineticConstant (canonicalDuhamelConstant kappa beta) C T * g ^ 3

/-- Dimension-free raw modal `L1` loss associated with the harmonic error
budget and the exact free norm `sqrt 2`. -/
def canonicalKineticRawModalLoss
    (kappa beta C T g : Real) : Real :=
  (1 / 2 : Real) * canonicalKineticModalErrorBudget kappa beta C T g *
    (canonicalKineticModalErrorBudget kappa beta C T g + 2 * Real.sqrt 2)

/-- One full-window free dilute event gives the variable-loss frozen lower
bound simultaneously at every positive kinetic endpoint `tau <= T`. -/
theorem canonical_uniformWindow_pathwise_lower
    (hN : 3 ≤ N) (kappa beta g C T mu : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hphysical : PhysicalRealization (N := N)
      kappa beta g hbeta (1 / 4) omega)
    (hg : 0 < g) (hT : 0 < T)
    (hmu : 0 ≤ mu) (hmuOne : mu < 1)
    (hfreeCeiling : Real.sqrt 2 ≤ C)
    (hgSmall : g ≤ couplingThreshold
      (canonicalDuhamelConstant kappa beta) C T)
    (hfreeSup : ∀ time ∈ Icc (0 : Real) (T / g ^ 2), ∀ i,
      |bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta (1 / 4) omega time) i| ≤ g ^ 4)
    (hloss : canonicalKineticRawModalLoss kappa beta C T g < 1) :
    ∀ tau : Real, 0 < tau → tau ≤ T →
      (1 / 8 : Real) -
          (2 / (1 - canonicalKineticRawModalLoss kappa beta C T g)) *
            canonicalKineticRawModalLoss kappa beta C T g ≤
        canonicalFrozenLateWindowL1Distance
          (N := N) kappa beta g hbeta (1 / 4) mu
            (tau / g ^ 2) omega := by
  have hphysicalForDuhamel := hphysical
  rcases hphysical with
    ⟨hsimple, zExact, _hzExact0, hzExact, hmatchExact, _hmodeExact⟩
  obtain ⟨zFree, _hzFree0, _hzFree, hmatchFree, _henergyFree⟩ :=
    canonicalRandomMassPhaseTrajectory_matches_reduced_of_simple
      canonicalIIDMassPhaseEnsemble hN
      (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
      kappa beta 0 hbeta omega hsimple
  let m := canonicalMass (N := N) omega
  let error := canonicalKineticModalErrorBudget kappa beta C T g
  let rho := canonicalKineticRawModalLoss kappa beta C T g
  have hK : 0 ≤ canonicalDuhamelConstant kappa beta := by
    unfold canonicalDuhamelConstant
    positivity
  have hC : 0 ≤ C := (Real.sqrt_nonneg 2).trans hfreeCeiling
  have herror0 : 0 ≤ error := by
    dsimp [error, canonicalKineticModalErrorBudget]
    exact mul_nonneg
      (kineticConstant_pos hK hC hT.le).le (pow_nonneg hg.le 3)
  have hrho0 : 0 ≤ rho := by
    dsimp [rho, canonicalKineticRawModalLoss]
    positivity
  have hfreeEnergy : ∀ time mode,
      reducedPhysicalOrderedModeEnergy m (zFree time) mode =
        frozenTwoBandEnergy N mode := by
    intro time mode
    exact reducedFreeModeEnergy_eq_frozen_of_match
      hN kappa beta hbeta omega hsimple zFree hmatchFree time mode
  have hfreeNorm : ∀ time,
      phaseSpaceL2Norm
          (reducedOrderedHarmonicPhaseVector m (zFree time)) =
        Real.sqrt 2 := by
    intro time
    exact reducedFreePhaseSpaceL2Norm_eq_sqrt_two
      hN m hsimple zFree hfreeEnergy time
  have hfreeL2 : ∀ time ∈ Icc (0 : Real) (T / g ^ 2),
      ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta (1 / 4) omega time)‖ ≤ Real.sqrt 2 := by
    intro time _htime
    exact norm_canonicalFreePhysicalBond_le_sqrt_two_of_match
      hN kappa beta hbeta omega hsimple zFree hmatchFree time
  have herror : ∀ time ∈ Icc (0 : Real) (T / g ^ 2),
      canonicalErrorEnergy (N := N)
          kappa beta g hbeta (1 / 4) omega time ≤ error := by
    simpa only [error, canonicalKineticModalErrorBudget] using
      (canonicalErrorEnergy_le_kineticScale_of_physicalRealization
        (N := N) hN kappa beta g C T hbeta
        (initialAmplitude := (1 / 4 : Real))
        (by norm_num) (by norm_num) omega hphysicalForDuhamel
        hg hC hT.le hgSmall (Real.sqrt 2) (Real.sqrt_nonneg 2)
        hfreeCeiling hfreeSup hfreeL2)
  have hzExactContinuous : Continuous zExact :=
    continuous_iff_continuousAt.mpr fun time =>
      (hzExact time).continuousAt
  intro tau htau htauT
  have hgSq : 0 < g ^ 2 := sq_pos_of_pos hg
  have hscaledT : tau / g ^ 2 ≤ T / g ^ 2 :=
    (div_le_div_iff_of_pos_right hgSq).2 htauT
  have hscaledPos : 0 < tau / g ^ 2 := div_pos htau hgSq
  have hExactIntegrable : ∀ mode : OrderedModeIndex N,
      IntervalIntegrable
        (fun time => reducedTrajectoryPositiveEnergyProfile
          m zExact time mode) volume
        (mu * (tau / g ^ 2)) (tau / g ^ 2) := by
    intro mode
    have hcontinuous : Continuous
        (fun time => reducedTrajectoryPositiveEnergyProfile
          m zExact time mode) := by
      change Continuous
        (fun time => reducedPositiveOrderedEnergyProfile
          m zExact time mode)
      exact continuous_reducedPositiveOrderedEnergyProfile
        m zExact hzExactContinuous mode
    exact hcontinuous.intervalIntegrable
      (mu * (tau / g ^ 2)) (tau / g ^ 2)
  have hstate : ∀ time ∈
      Icc (mu * (tau / g ^ 2)) (tau / g ^ 2),
      (1 / 2 : Real) *
          phaseSpaceL2Distance
            (reducedOrderedHarmonicPhaseVector m (zExact time))
            (reducedOrderedHarmonicPhaseVector m (zFree time)) *
          (phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (zExact time)) +
            phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (zFree time))) ≤ rho := by
    intro time htime
    have htime0 : 0 ≤ time := by
      exact (mul_nonneg hmu hscaledPos.le).trans htime.1
    have htimeFull : time ∈ Icc (0 : Real) (T / g ^ 2) :=
      ⟨htime0, htime.2.trans hscaledT⟩
    have hdistance : phaseSpaceL2Distance
        (reducedOrderedHarmonicPhaseVector m (zExact time))
        (reducedOrderedHarmonicPhaseVector m (zFree time)) =
      canonicalErrorEnergy (N := N)
        kappa beta g hbeta (1 / 4) omega time := by
      exact reducedModalDistance_eq_canonicalErrorEnergy_of_matches
        kappa beta g hbeta (1 / 4) omega hsimple
        zExact zFree hmatchExact hmatchFree time
    have hdistanceBound : phaseSpaceL2Distance
        (reducedOrderedHarmonicPhaseVector m (zExact time))
        (reducedOrderedHarmonicPhaseVector m (zFree time)) ≤ error := by
      rw [hdistance]
      exact herror time htimeFull
    have hactualNorm :
        phaseSpaceL2Norm
            (reducedOrderedHarmonicPhaseVector m (zExact time)) ≤
          error + Real.sqrt 2 := by
      calc
        phaseSpaceL2Norm
            (reducedOrderedHarmonicPhaseVector m (zExact time)) ≤
            phaseSpaceL2Distance
                (reducedOrderedHarmonicPhaseVector m (zExact time))
                (reducedOrderedHarmonicPhaseVector m (zFree time)) +
              phaseSpaceL2Norm
                (reducedOrderedHarmonicPhaseVector m (zFree time)) :=
          phaseSpaceL2Norm_le_distance_add _ _
        _ ≤ error + Real.sqrt 2 := by
          rw [hfreeNorm time]
          exact add_le_add hdistanceBound le_rfl
    calc
      (1 / 2 : Real) *
            phaseSpaceL2Distance
              (reducedOrderedHarmonicPhaseVector m (zExact time))
              (reducedOrderedHarmonicPhaseVector m (zFree time)) *
          (phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (zExact time)) +
            phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (zFree time))) ≤
          (1 / 2 : Real) * error *
            ((error + Real.sqrt 2) + Real.sqrt 2) := by
        rw [hfreeNorm time]
        gcongr
        exact add_nonneg (amplitudeL2Norm_nonneg _) (Real.sqrt_nonneg 2)
      _ = rho := by
        dsimp [rho, canonicalKineticRawModalLoss]
        ring
  have hraw :
      l1Distance
          (lateWindowAverage
            (reducedTrajectoryPositiveEnergyProfile m zExact) mu
              (tau / g ^ 2))
          (frozenTwoBandEnergy N) ≤ rho := by
    exact reducedPositiveLateWindow_raw_close_frozen
      hN m hsimple zExact zFree mu (tau / g ^ 2) rho
      hmu hmuOne hscaledPos hrho0 hExactIntegrable hfreeEnergy hstate
  exact canonicalFrozenLateWindowL1Distance_lower_of_raw_close
    hN kappa beta g hbeta omega hsimple zExact mu (tau / g ^ 2) rho
    (by simpa only [rho] using hloss) hmatchExact hraw

/-- The event-shaped form of `canonical_uniformWindow_pathwise_lower`.
Membership in the measurable physical signed free-grid event supplies the
whole-window free-orbit hypothesis through the exact canonical `g = 0`
bond identification. -/
theorem canonical_uniformWindow_pathwise_lower_of_freeGridGood
    (hN : 3 ≤ N) (kappa beta g C T mu : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hphysical : PhysicalRealization (N := N)
      kappa beta g hbeta (1 / 4) omega)
    (hg : 0 < g) (hT : 0 < T)
    (hmu : 0 ≤ mu) (hmuOne : mu < 1)
    (hfreeCeiling : Real.sqrt 2 ≤ C)
    (hgSmall : g ≤ couplingThreshold
      (canonicalDuhamelConstant kappa beta) C T)
    (hgood : omega ∈
      canonicalPhysicalSignedFreeGridGood (N := N) T g)
    (hloss : canonicalKineticRawModalLoss kappa beta C T g < 1) :
    ∀ tau : Real, 0 < tau → tau ≤ T →
      (1 / 8 : Real) -
          (2 / (1 - canonicalKineticRawModalLoss kappa beta C T g)) *
            canonicalKineticRawModalLoss kappa beta C T g ≤
        canonicalFrozenLateWindowL1Distance
          (N := N) kappa beta g hbeta (1 / 4) mu
            (tau / g ^ 2) omega := by
  have hfreeSup : ∀ time ∈ Icc (0 : Real) (T / g ^ 2), ∀ i,
      |bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta (1 / 4) omega time) i| ≤ g ^ 4 := by
    intro time htime i
    rw [canonicalExactFreePhysicalPositionPathBond_eq_physicalSignedHaar
      hN kappa beta hbeta omega hgood.1 time i]
    exact canonicalPhysicalSignedFreeGridGood_implies_wholeWindow_bound
      hN T g hT.le hg hgood i time htime
  exact canonical_uniformWindow_pathwise_lower
    hN kappa beta g C T mu hbeta omega hphysical hg hT hmu hmuOne
      hfreeCeiling hgSmall hfreeSup hloss

#print axioms canonical_uniformWindow_pathwise_lower
#print axioms canonical_uniformWindow_pathwise_lower_of_freeGridGood

end

end ArchonPhysics.R32CanonicalUniformWindowPathwiseV1

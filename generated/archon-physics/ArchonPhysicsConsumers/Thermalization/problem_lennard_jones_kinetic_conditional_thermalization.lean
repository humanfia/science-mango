import ArchonPhysics.LennardJonesKineticConditionalThermalization

/-!
# Consumer: conditional LJ kinetic thermalization root

This target checks the lower-level conditional endpoints without claiming that
random-phase propagation, FGR, or microscopic--kinetic convergence has been
derived from the Hamiltonian.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Filter MeasureTheory
open ArchonPhysics
open ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.LennardJonesKineticConditionalThermalization
open ArchonPhysics.LennardJonesMeasurableWindowThermalizationTime
open ArchonPhysics.LennardJonesThermodynamicHittingTransfer
open ArchonPhysics.MeasurableMicroscopicWindowThermalizationTime
open ArchonPhysics.PaperSpectralEntropyCriterion
open ArchonPhysics.PaperXiHalfNotEquipartition
open ArchonPhysics.ThermalizationTransfer

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [PseudoMetricSpace E]

/-- Exact algebra behind the exponent conversion: inverse-square in `g`
becomes inverse-first-power in LJ energy density. -/
theorem problem_lennardJones_conditionalRoot_couplingSquared_is_energyLinear
    {depth r0 energyDensity : Real}
    (hdepth : 0 < depth) (hr0 : 0 < r0) (he : 0 <= energyDensity) :
    kineticCouplingMagnitude depth r0 energyDensity ^ 2 =
      49 * energyDensity / (32 * depth) :=
  kineticCouplingMagnitude_sq hdepth hr0 he

/-- The measurable rational event and its literal positive-window semantics. -/
theorem problem_lennardJones_conditionalRoot_rationalWindow_semantics
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (startReal duration threshold failureTolerance : Real)
    (N : Nat) (g : Real) (start : ENNReal) (hduration : 0 < duration)
    (heval : forall q : Rat, Measurable fun omega =>
      distanceAtCoupling micro equilibrium N g omega (q : Real))
    (hcontinuous : forall omega,
      Continuous (distanceAtCoupling micro equilibrium N g omega)) :
    MeasurableSet (rationalStrictWindowBadEventAtCoupling micro equilibrium
        startReal duration threshold N g) /\
      (start ∈ measurableWindowThermalizationCandidatesAtCoupling P micro
          equilibrium threshold duration failureTolerance N g <->
        0 < start /\ start < (⊤ : ENNReal) /\
          P.real (realStrictWindowBadEvent
            (distanceAtCoupling micro equilibrium N g)
            start.toReal duration threshold) <= failureTolerance) := by
  exact ⟨
    rationalWindowBadEvent_measurable micro equilibrium startReal duration
      threshold N g heval,
    rationalWindowCandidate_iff_literalRealWindow P micro equilibrium
      threshold duration failureTolerance N g hduration hcontinuous start⟩

/-- The static `xi = 1/2` paper criterion is not full equipartition. -/
theorem problem_lennardJones_conditionalRoot_paperXi_half_counterexample :
    paperXi energy monitored = 1 / 2 /\
      l1Distance (normalizedWeights energy)
        (uniformWeights : Fin 2 -> Real) = 1 / 2 :=
  paperXi_half_static_counterexample

/-- The FGR certificate field gives the conditional LJ energy exponent `-1`
law; the certificate remains an input through `root`. -/
theorem problem_lennardJones_conditionalRoot_energyDensityTime_law
    (P : Measure Omega) [IsProbabilityMeasure P]
    (ljMicro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (windowThreshold kineticDuration failureTolerance : Real)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (crossingThreshold tauStar depth r0 : Real)
    (root : ConditionalRoot P ljMicro equilibrium windowThreshold
      kineticDuration failureTolerance sizeCutoff kineticDistance
      crossingThreshold tauStar depth r0)
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r0) :
    ConvergesInProbabilityTo P
      (fun j _omega =>
        ENNReal.ofReal (s.energyDensity j / depth) *
          lennardJonesMeasurableKineticScaledWindowThermalizationTime P
            ljMicro equilibrium windowThreshold kineticDuration
            failureTolerance depth r0 (s.systemSize j) (s.energyDensity j))
      (ENNReal.ofReal ((32 / 49 : Real) * tauStar)) :=
  root.energyDensityTime_law P ljMicro equilibrium windowThreshold
    kineticDuration failureTolerance sizeCutoff kineticDistance
    crossingThreshold tauStar depth r0 s

/-- The separate persistence fields give the existing shrinking-error,
expanding-duration diagonal endpoint. -/
theorem problem_lennardJones_conditionalRoot_joint_persistence
    (P : Measure Omega) [IsProbabilityMeasure P]
    (ljMicro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (windowThreshold kineticDuration failureTolerance : Real)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (crossingThreshold tauStar depth r0 : Real)
    (root : ConditionalRoot P ljMicro equilibrium windowThreshold
      kineticDuration failureTolerance sizeCutoff kineticDistance
      crossingThreshold tauStar depth r0)
    (precisionIndex durationIndex sizeIndex : Nat -> Nat)
    (hprecision : Tendsto precisionIndex atTop atTop)
    (hduration : Tendsto durationIndex atTop atTop)
    (hsize : ∀ᶠ j in atTop,
      shrinkingToleranceExpandingDurationSizeCutoff P root.persistenceMicro
        root.persistenceKinetic root.persistenceStart root.persistenceThreshold
        root.persistenceFixedWindowMicroToKinetic
        (precisionIndex j) (durationIndex j) <= sizeIndex j) :
    Tendsto
        (fun j => root.persistenceThreshold (precisionIndex j))
        atTop (nhds 0) /\
      Tendsto
        (fun j => P.real (microscopicEquilibriumWindowBadEvent
          root.persistenceMicro equilibrium
          (root.persistenceStart (precisionIndex j))
          (root.persistenceStart (precisionIndex j) +
            (durationIndex j : Real))
          (root.persistenceThreshold (precisionIndex j)) (sizeIndex j)))
        atTop (nhds 0) :=
  root.jointShrinkingErrorExpandingDuration_persistence P ljMicro equilibrium
    windowThreshold kineticDuration failureTolerance sizeCutoff kineticDistance
    crossingThreshold tauStar depth r0 precisionIndex durationIndex sizeIndex
    hprecision hduration hsize

#print axioms problem_lennardJones_conditionalRoot_couplingSquared_is_energyLinear
#print axioms problem_lennardJones_conditionalRoot_rationalWindow_semantics
#print axioms problem_lennardJones_conditionalRoot_paperXi_half_counterexample
#print axioms problem_lennardJones_conditionalRoot_energyDensityTime_law
#print axioms problem_lennardJones_conditionalRoot_joint_persistence

end

end ArchonPhysicsConsumers.Thermalization

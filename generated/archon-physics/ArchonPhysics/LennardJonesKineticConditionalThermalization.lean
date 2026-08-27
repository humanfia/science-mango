import ArchonPhysics.LennardJonesMeasurableWindowThermalizationTime
import ArchonPhysics.PaperXiHalfNotEquipartition

/-!
# Conditional kinetic thermalization root for Lennard--Jones chains

This module is a lower-level conditional endpoint, not a first-principles
derivation.  Its scaling field explicitly assumes the existing transparent
wave-kinetic/Fermi-golden-rule certificate.  Its persistence fields explicitly
assume fixed-window microscopic--kinetic convergence and a kinetic equilibrium
tail.  In particular, this file does **not** close random-phase propagation,
derive FGR from the random-mass Hamiltonian, or construct a microscopic--
kinetic limit.

The exponents have two different variables and must not be conflated.  The
effective kinetic law is `Tc ~ g^(-2)`.  For the cubic LJ coupling,
`g_LJ(e)^2 = 49 e / (32 D)`, so the same law is
`Tc ~ (32 / 49) D e^(-1)` in energy density: exponent `-2` in `g`, but exponent
`-1` in `e`.

The paper's static `xi = 1/2` criterion is also kept separate.  An exact
two-mode counterexample shows that this scalar equality can coexist with
full-mode `l1` error `1/2`; it therefore cannot replace the measurable
rational-window persistence semantics below.
-/

namespace ArchonPhysics.LennardJonesKineticConditionalThermalization

open Filter MeasureTheory
open ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.LennardJonesMeasurableWindowThermalizationTime
open ArchonPhysics.LennardJonesThermodynamicHittingTransfer
open ArchonPhysics.MeasurableMicroscopicWindowThermalizationTime
open ArchonPhysics.PaperSpectralEntropyCriterion
open ArchonPhysics.PaperXiHalfNotEquipartition
open ArchonPhysics.ThermalizationTransfer

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [PseudoMetricSpace E]

/-- Transparent conditional root for the new LJ kinetic scope.

`fgrScalingCertificate` is the unresolved LJ wave-kinetic/FGR input.  The
remaining fields instantiate the generic shrinking-error, expanding-duration
theorem.  `persistenceMicro` is deliberately explicit rather than silently
identified with `ljMicro`: constructing the correct rescaled LJ path and
proving its fixed-window convergence are part of the missing microscopic
theory. -/
structure ConditionalRoot
    (P : Measure Omega) [IsProbabilityMeasure P]
    (ljMicro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (windowThreshold kineticDuration failureTolerance : Real)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (crossingThreshold tauStar depth r0 : Real) where
  /-- Explicit, unconstructed microscopic--kinetic/FGR scaling certificate. -/
  fgrScalingCertificate :
    LennardJonesMeasurableKineticScaledWindowScalingCertificate P ljMicro
      equilibrium windowThreshold kineticDuration failureTolerance
      sizeCutoff kineticDistance crossingThreshold tauStar depth r0
  /-- Microscopic path used by the generic persistence transfer. -/
  persistenceMicro : Nat -> Omega -> Real -> E
  /-- Deterministic kinetic comparison trajectory. -/
  persistenceKinetic : Real -> E
  /-- Precision-dependent proposed settling starts. -/
  persistenceStart : Nat -> Real
  /-- Precision-dependent equilibrium tolerances. -/
  persistenceThreshold : Nat -> Real
  /-- The admitted equilibrium error shrinks to zero. -/
  persistenceThreshold_tendsto_zero :
    Tendsto persistenceThreshold atTop (nhds 0)
  /-- The kinetic trajectory lies within half the admitted error after each
  precision-dependent start. -/
  persistenceKinetic_tail : forall precision : Nat, forall time : Real,
    persistenceStart precision <= time ->
      dist (persistenceKinetic time) equilibrium <
        persistenceThreshold precision / 2
  /-- Unresolved fixed-window microscopic--kinetic convergence.  The generic
  theorem diagonalizes these statements; this root does not prove them. -/
  persistenceFixedWindowMicroToKinetic : forall precision duration : Nat,
    Tendsto
      (fun N => P.real (microscopicKineticWindowBadEvent persistenceMicro
        persistenceKinetic (persistenceStart precision)
        (persistenceStart precision + (duration : Real))
        (persistenceThreshold precision / 2) N))
      atTop (nhds 0)

/-! ## Measurable rational-window semantics -/

/-- At fixed coupling and size, rational-time measurability is enough for the
strict window bad event to be measurable. -/
theorem rationalWindowBadEvent_measurable
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (start duration threshold : Real) (N : Nat) (g : Real)
    (heval : forall q : Rat, Measurable fun omega =>
      distanceAtCoupling micro equilibrium N g omega (q : Real)) :
    MeasurableSet (rationalStrictWindowBadEventAtCoupling micro equilibrium
      start duration threshold N g) :=
  measurableSet_rationalStrictWindowBadEventAtCoupling micro equilibrium
    start duration threshold N g heval

/-- With positive duration and pathwise continuity, the countable candidate
has exactly the literal all-real-times strict-window meaning. -/
theorem rationalWindowCandidate_iff_literalRealWindow
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat) (g : Real)
    (hduration : 0 < duration)
    (hcontinuous : forall omega,
      Continuous (distanceAtCoupling micro equilibrium N g omega))
    (start : ENNReal) :
    start ∈ measurableWindowThermalizationCandidatesAtCoupling P micro
        equilibrium threshold duration failureTolerance N g <->
      0 < start /\ start < (⊤ : ENNReal) /\
        P.real (realStrictWindowBadEvent
          (distanceAtCoupling micro equilibrium N g)
          start.toReal duration threshold) <= failureTolerance :=
  mem_measurableWindowThermalizationCandidatesAtCoupling_iff_real P micro
    equilibrium threshold duration failureTolerance N g hduration hcontinuous
    start

/-! ## Static limitation of the paper threshold -/

/-- The published half-threshold alone does not imply full-mode
equipartition: the explicit profile has `paperXi = 1/2` and full-mode `l1`
error `1/2`. -/
theorem paperXi_half_static_counterexample :
    paperXi energy monitored = 1 / 2 /\
      l1Distance (normalizedWeights energy)
        (uniformWeights : Fin 2 -> Real) = 1 / 2 :=
  exists_paperXi_half_with_fullMode_error_half

/-! ## Named conditional endpoints -/

/-- Conditional LJ energy-density law.  This is the `g^(-2)` effective law
converted by the exact cubic identity into the energy exponent `-1`:

`(e_j / D) Tc(N_j,e_j) -> (32 / 49) tauStar` in probability. -/
theorem ConditionalRoot.energyDensityTime_law
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
  lennardJonesMeasurableKineticScaledWindow_energyDensityTime_law P ljMicro
    equilibrium windowThreshold kineticDuration failureTolerance sizeCutoff
    kineticDistance crossingThreshold tauStar depth r0
    root.fgrScalingCertificate s

/-- Conditional thermodynamic persistence endpoint.

Along every admitted diagonal with shrinking precision error, expanding finite
duration, and size above the constructed two-parameter cutoff, both the error
and the probability of any failure on the full window tend to zero.  This is
not an infinite-time statement for any fixed finite chain. -/
theorem ConditionalRoot.jointShrinkingErrorExpandingDuration_persistence
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
        atTop (nhds 0) := by
  exact equilibriumBadProbability_and_threshold_tendsto_zero_along_joint_limit
    P root.persistenceMicro root.persistenceKinetic equilibrium
    root.persistenceStart root.persistenceThreshold
    root.persistenceThreshold_tendsto_zero root.persistenceKinetic_tail
    root.persistenceFixedWindowMicroToKinetic precisionIndex durationIndex
    sizeIndex hprecision hduration hsize

end

end ArchonPhysics.LennardJonesKineticConditionalThermalization

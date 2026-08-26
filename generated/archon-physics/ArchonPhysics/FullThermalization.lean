import ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction
import ArchonPhysics.EnergyDensityThermalization
import ArchonPhysics.WeightedDegenerateTwoTimeF2Certificate

/-!
# Full conditional nonzero-mode thermalization certificate

For the frozen iid random-mass lattice, F1 is already unconditional: the
canonical positive-mode observable, its measurable closed hitting-time
representative, and its almost-everywhere physical interpretation are supplied
by the imported canonical reduction.

This module packages exactly the two remaining conditional inputs:

* an F2 robust two-time window for a genuine finite collision flow;
* an F3 local-uniform microscopic-to-kinetic approximation for the same
  kinetic distance.

The certificate contains no high-probability law, no hitting-time conclusion,
and no copy of the desired theorem.  The final law is derived by the
almost-everywhere two-time hitting transfer.
-/

namespace ArchonPhysics

open ArchonPhysics
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction
open ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
open ArchonPhysics.HamiltonianScaling
open ArchonPhysics.EnergyDensityThermalization
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.WeightedDegenerateTwoTimeF2Certificate
open Filter MeasureTheory Topology


local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩
noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Fintype Triad] [Nonempty Mode]

/--
Minimal non-circular certificate for the complete conditional release law.

The kinetic field is F2 and constructs the positive finite kinetic-time window.
The microscopic field is F3 and compares the actual canonical positive-mode
distance with precisely that F2 trajectory.  The frozen F1 construction is not
a field: it is already proved by the canonical observable and hitting-time
modules.
-/
structure FullThermalizationCertificate
    (model : FiniteCollisionModel Mode Triad)
    (actionZero : Mode → Real)
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (sizeCutoff : Real → Nat) where
  kinetic :
    RobustTwoTimeF2Certificate model actionZero mu delta
  threshold_below_frozen_initial : delta < 1 / 8
  microscopic :
    KineticWindowApproximation kappa beta hbeta mu delta sizeCutoff
      (kineticEquipartitionProfile model.collisionData
        kinetic.unitFlow.trajectory mu)

/--
The full conditional nonzero-mode thermalization law.

Along every admissible thermodynamic/weak-coupling joint limit, the
probability that the actual frozen positive-mode equilibration time lies in
the F2 inverse-square window tends to one.
-/
theorem fullNonzeroModeThermalizationLaw
    {model : FiniteCollisionModel Mode Triad}
    {actionZero : Mode → Real}
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real → Nat}
    (certificate : FullThermalizationCertificate model actionZero
      kappa beta hbeta mu delta sizeCutoff) :
    HighProbabilityG2Bounds
      canonicalIIDMassPhaseEnsemble.probability
      (measurableClosedEquilibrationTime
        kappa beta hbeta mu delta)
      sizeCutoff certificate.kinetic.lower certificate.kinetic.upper := by
  exact
    KineticWindowApproximation.toHighProbabilityG2Bounds_of_twoTimeWindow
      certificate.kinetic.mu_nonnegative
      certificate.kinetic.mu_less_one
      certificate.threshold_below_frozen_initial
      certificate.microscopic
      certificate.kinetic.robust_window

/--
Energy-density form of the same full conditional law.

The admitted coupling path is identified with
g = lambda * epsilon^((degree - 2) / 2); the resulting physical hitting-time
window has the exact inverse energy-density scale.
-/
theorem fullNonzeroModeEnergyDensityThermalizationLaw
    {model : FiniteCollisionModel Mode Triad}
    {actionZero : Mode → Real}
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real → Nat}
    (certificate : FullThermalizationCertificate model actionZero
      kappa beta hbeta mu delta sizeCutoff)
    (lambda : Real) (degree : Nat) (hdegree : 3 ≤ degree)
    (hlambda : lambda ≠ 0)
    (jointLimit : AdmissibleJointLimit sizeCutoff)
    (epsilon : Nat → Real) (hepsilon : ∀ j, 0 < epsilon j)
    (hcoupling : ∀ j,
      jointLimit.coupling j =
        effectiveCoupling lambda (epsilon j) degree) :
    Tendsto
      (fun j => canonicalIIDMassPhaseEnsemble.probability
        (energyDensityWindowEvent
          (measurableClosedEquilibrationTime
            kappa beta hbeta mu delta)
          certificate.kinetic.lower certificate.kinetic.upper
          (jointLimit.systemSize j) lambda (epsilon j) degree))
      atTop (nhds 1) := by
  exact
    EnergyDensityThermalization.HighProbabilityG2Bounds.energyDensity_corollary
      canonicalIIDMassPhaseEnsemble.probability
      (measurableClosedEquilibrationTime
        kappa beta hbeta mu delta)
      sizeCutoff certificate.kinetic.lower certificate.kinetic.upper
      (fullNonzeroModeThermalizationLaw certificate)
      lambda degree hdegree hlambda jointLimit epsilon hepsilon hcoupling

end

end ArchonPhysics

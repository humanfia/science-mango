import ArchonPhysics.CanonicalRandomMicroscopicCertificate
import ArchonPhysics.RandomMassPhaseInitialData
import ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter

/-!
# R32 canonical exact/free mass-weighted error bridge

The canonical nonlinear flow at coupling `g` and the canonical harmonic flow
at coupling `0` start from the same frozen mass/phase physical position and
momentum.  On `PhysicalRealization`, the exact path is an existing reduced
Hamilton trajectory.  The same simple-spectrum initial point is fed to the
existing reduced-flow theorem at `g = 0`, so the free dynamics are likewise
projected from a proved ODE rather than assumed.

For the mass-weighted errors `deltaX = X_exact - X_free` and
`deltaY = Y_exact - Y_free`, the resulting equations are

`deltaX' = deltaY`,

`deltaY' = -H deltaX + transformedNonlinearForce(exact)`,

with zero initial error.  Derivatives use `HasMassWeightedDerivAt`, whose
fixed `PiLp` instances are also selected locally here.  The final acceleration
rewrite is performed first as a vector identity and then passed to
`congr_deriv`; it never asks Lean to identify that predicate with a
`HasDerivAt` carrying the reducible `WithLp` module instance.
-/

namespace ArchonPhysics.R32CanonicalExactFreeBridgeV3

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CanonicalRandomMicroscopicCertificate
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
open ArchonPhysics.ReducedModeTransform
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/- Match exactly the instances fixed by `HasMassWeightedDerivAt`. -/
local instance canonicalWeightedAddCommGroup :
    AddCommGroup (WeightedConfiguration N) :=
  (PiLp.normedAddCommGroup 2
    (fun _ : Lattice.Site N => Real)).toAddCommGroup

local instance canonicalWeightedModule :
    Module Real (WeightedConfiguration N) :=
  (PiLp.normedSpace 2 Real
    (fun _ : Lattice.Site N => Real)).toModule

local instance canonicalWeightedTopologicalSpace :
    TopologicalSpace (WeightedConfiguration N) :=
  (PiLp.normedAddCommGroup 2
    (fun _ : Lattice.Site N => Real)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The positive mass realization carried by a canonical sample. -/
abbrev canonicalMass (omega : RandomEnsemble.SampleSpace) :
    Lattice.PositiveMassConfig N :=
  canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega

/-- Physical position along the canonical flow at the displayed coupling. -/
def canonicalPhysicalPositionPath
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (a : Real)
    (omega : RandomEnsemble.SampleSpace) :
    Real → HilbertConfiguration N :=
  fun time =>
    (canonicalRandomMassPhaseGlobalFlow N kappa beta coupling hbeta
      (canonicalPhaseInitialSample (N := N)
        kappa beta coupling a omega, time)).2.1

/-- Physical canonical momentum along the same canonical flow. -/
def canonicalPhysicalMomentumPath
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (a : Real)
    (omega : RandomEnsemble.SampleSpace) :
    Real → HilbertConfiguration N :=
  fun time =>
    (canonicalRandomMassPhaseGlobalFlow N kappa beta coupling hbeta
      (canonicalPhaseInitialSample (N := N)
        kappa beta coupling a omega, time)).2.2

/-- `X = sqrt(M) q` along the canonical flow. -/
def canonicalMassWeightedPositionPath
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (a : Real)
    (omega : RandomEnsemble.SampleSpace) :
    Real → WeightedConfiguration N :=
  massWeightedPosition (canonicalMass (N := N) omega)
    (canonicalPhysicalPositionPath (N := N)
      kappa beta coupling hbeta a omega)

/-- `Y = M^(-1/2) p` along the canonical flow. -/
def canonicalMassWeightedMomentumPath
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (a : Real)
    (omega : RandomEnsemble.SampleSpace) :
    Real → WeightedConfiguration N :=
  massWeightedMomentum (canonicalMass (N := N) omega)
    (canonicalPhysicalMomentumPath (N := N)
      kappa beta coupling hbeta a omega)

/-- The mass-weighted exact-minus-free position error. -/
def canonicalExactFreePositionError
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) :
    Real → WeightedConfiguration N :=
  fun time =>
    canonicalMassWeightedPositionPath (N := N)
        kappa beta g hbeta a omega time -
      canonicalMassWeightedPositionPath (N := N)
        kappa beta 0 hbeta a omega time

/-- The mass-weighted exact-minus-free momentum error. -/
def canonicalExactFreeMomentumError
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) :
    Real → WeightedConfiguration N :=
  fun time =>
    canonicalMassWeightedMomentumPath (N := N)
        kappa beta g hbeta a omega time -
      canonicalMassWeightedMomentumPath (N := N)
        kappa beta 0 hbeta a omega time

/-- The nonlinear source evaluated on the exact physical path. -/
def canonicalExactNonlinearForcePath
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) :
    Real → WeightedConfiguration N :=
  fun time =>
    transformedNonlinearForce (canonicalMass (N := N) omega)
      kappa beta g
      (canonicalPhysicalPositionPath (N := N)
        kappa beta g hbeta a omega time)

/-- The harmonic operator bundled for the energy-Duhamel interface. -/
def harmonicOperatorCLM (m : Lattice.PositiveMassConfig N) :
    WeightedConfiguration N →L[Real] WeightedConfiguration N :=
  LinearMap.toContinuousLinearMap (harmonicOperator m)

@[simp] theorem harmonicOperatorCLM_apply
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    harmonicOperatorCLM m x = harmonicOperator m x := by
  rfl

/-- The nonlinear residual vanishes at effective coupling zero. -/
@[simp] theorem transformedNonlinearForce_zero_coupling
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (q : HilbertConfiguration N) :
    transformedNonlinearForce m kappa beta 0 q = 0 := by
  simp [transformedNonlinearForce, nonlinearPotentialGradient,
    nonlinearPotentialDerivative]

/-! The physical components of the initial ambient sample do not depend on
the coupling coordinate stored in its parameter component. -/

@[simp] theorem canonicalPhysicalPositionPath_zero
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (a : Real)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalPhysicalPositionPath (N := N)
        kappa beta coupling hbeta a omega 0 =
      initialPhysicalPosition canonicalIIDMassPhaseEnsemble a omega := by
  unfold canonicalPhysicalPositionPath
  rw [canonicalRandomMassPhaseGlobalFlow_zero]
  rfl

@[simp] theorem canonicalPhysicalMomentumPath_zero
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (a : Real)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalPhysicalMomentumPath (N := N)
        kappa beta coupling hbeta a omega 0 =
      initialPhysicalMomentum canonicalIIDMassPhaseEnsemble a omega := by
  unfold canonicalPhysicalMomentumPath
  rw [canonicalRandomMassPhaseGlobalFlow_zero]
  rfl

@[simp] theorem canonicalMassWeightedPositionPath_zero
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (a : Real)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalMassWeightedPositionPath (N := N)
        kappa beta coupling hbeta a omega 0 =
      sqrtMassTransform (canonicalMass (N := N) omega)
        (initialPhysicalPosition canonicalIIDMassPhaseEnsemble a omega) := by
  unfold canonicalMassWeightedPositionPath massWeightedPosition
  rw [canonicalPhysicalPositionPath_zero]

@[simp] theorem canonicalMassWeightedMomentumPath_zero
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (a : Real)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalMassWeightedMomentumPath (N := N)
        kappa beta coupling hbeta a omega 0 =
      inverseSqrtMassTransform (canonicalMass (N := N) omega)
        (initialPhysicalMomentum canonicalIIDMassPhaseEnsemble a omega) := by
  unfold canonicalMassWeightedMomentumPath massWeightedMomentum
  rw [canonicalPhysicalMomentumPath_zero]

/-- Exact mass-weighted forced-harmonic error equations for the two concrete
canonical global flows. -/
structure CanonicalExactFreeErrorEquations
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) : Prop where
  position_zero :
    canonicalExactFreePositionError (N := N)
      kappa beta g hbeta a omega 0 = 0
  momentum_zero :
    canonicalExactFreeMomentumError (N := N)
      kappa beta g hbeta a omega 0 = 0
  position_derivative : ∀ time,
    HasMassWeightedDerivAt
      (canonicalExactFreePositionError (N := N)
        kappa beta g hbeta a omega)
      (canonicalExactFreeMomentumError (N := N)
        kappa beta g hbeta a omega time) time
  momentum_derivative : ∀ time,
    HasMassWeightedDerivAt
      (canonicalExactFreeMomentumError (N := N)
        kappa beta g hbeta a omega)
      (-harmonicOperatorCLM (canonicalMass (N := N) omega)
          (canonicalExactFreePositionError (N := N)
            kappa beta g hbeta a omega time) +
        canonicalExactNonlinearForcePath (N := N)
          kappa beta g hbeta a omega time) time

/-- Obtain both equations by projecting the exact and free reduced ODEs. -/
theorem canonicalExactFreeErrorEquations_of_physicalRealization
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hphysical : PhysicalRealization (N := N)
      kappa beta g hbeta a omega) :
    CanonicalExactFreeErrorEquations (N := N)
      kappa beta g hbeta a omega := by
  rcases hphysical with
    ⟨hsimple, zExact, _hzExact0, hzExact, hmatchExact, _hmode⟩
  obtain ⟨zFree, _hzFree0, hzFree, hmatchFree, _henergyFree⟩ :=
    canonicalRandomMassPhaseTrajectory_matches_reduced_of_simple
      canonicalIIDMassPhaseEnsemble hN ha0 ha1
      kappa beta 0 hbeta omega hsimple

  let qExact : Real → HilbertConfiguration N :=
    fun time => ((zExact time).1 : HilbertConfiguration N)
  let pExact : Real → HilbertConfiguration N :=
    fun time => ((zExact time).2 : HilbertConfiguration N)
  let qFree : Real → HilbertConfiguration N :=
    fun time => ((zFree time).1 : HilbertConfiguration N)
  let pFree : Real → HilbertConfiguration N :=
    fun time => ((zFree time).2 : HilbertConfiguration N)

  have hDynamicsExact : HasExplicitHamiltonDerivatives
      (canonicalMass (N := N) omega) kappa beta g pExact qExact := by
    intro time
    constructor
    · simpa [pExact, qExact, reducedVelocity_coe] using
        hasDerivAt_reducedPosition_coe
          (canonicalMass (N := N) omega) kappa beta g (hzExact time)
    · simpa [pExact, qExact, reducedPotentialGradient_coe] using
        hasDerivAt_reducedMomentum_coe
          (canonicalMass (N := N) omega) kappa beta g (hzExact time)
  have hDynamicsFree : HasExplicitHamiltonDerivatives
      (canonicalMass (N := N) omega) kappa beta 0 pFree qFree := by
    intro time
    constructor
    · simpa [pFree, qFree, reducedVelocity_coe] using
        hasDerivAt_reducedPosition_coe
          (canonicalMass (N := N) omega) kappa beta 0 (hzFree time)
    · simpa [pFree, qFree, reducedPotentialGradient_coe] using
        hasDerivAt_reducedMomentum_coe
          (canonicalMass (N := N) omega) kappa beta 0 (hzFree time)

  have hqExact : ∀ time,
      canonicalPhysicalPositionPath (N := N)
          kappa beta g hbeta a omega time = qExact time := by
    intro time
    unfold canonicalPhysicalPositionPath
    rw [hmatchExact time]
    rfl
  have hpExact : ∀ time,
      canonicalPhysicalMomentumPath (N := N)
          kappa beta g hbeta a omega time = pExact time := by
    intro time
    unfold canonicalPhysicalMomentumPath
    rw [hmatchExact time]
    rfl
  have hmatchFreeGlobal : ∀ time,
      canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta
          (canonicalPhaseInitialSample (N := N)
            kappa beta 0 a omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta 0 (zFree time) := by
    intro time
    exact hmatchFree time
  have hqFree : ∀ time,
      canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta a omega time = qFree time := by
    intro time
    unfold canonicalPhysicalPositionPath
    rw [hmatchFreeGlobal time]
    rfl
  have hpFree : ∀ time,
      canonicalPhysicalMomentumPath (N := N)
          kappa beta 0 hbeta a omega time = pFree time := by
    intro time
    unfold canonicalPhysicalMomentumPath
    rw [hmatchFreeGlobal time]
    rfl

  have hXExactEq :
      canonicalMassWeightedPositionPath (N := N)
          kappa beta g hbeta a omega =
        massWeightedPosition (canonicalMass (N := N) omega) qExact := by
    funext time
    unfold canonicalMassWeightedPositionPath massWeightedPosition
    rw [hqExact time]
  have hYExactEq :
      canonicalMassWeightedMomentumPath (N := N)
          kappa beta g hbeta a omega =
        massWeightedMomentum (canonicalMass (N := N) omega) pExact := by
    funext time
    unfold canonicalMassWeightedMomentumPath massWeightedMomentum
    rw [hpExact time]
  have hXFreeEq :
      canonicalMassWeightedPositionPath (N := N)
          kappa beta 0 hbeta a omega =
        massWeightedPosition (canonicalMass (N := N) omega) qFree := by
    funext time
    unfold canonicalMassWeightedPositionPath massWeightedPosition
    rw [hqFree time]
  have hYFreeEq :
      canonicalMassWeightedMomentumPath (N := N)
          kappa beta 0 hbeta a omega =
        massWeightedMomentum (canonicalMass (N := N) omega) pFree := by
    funext time
    unfold canonicalMassWeightedMomentumPath massWeightedMomentum
    rw [hpFree time]

  have hXExact : ∀ time,
      HasMassWeightedDerivAt
        (canonicalMassWeightedPositionPath (N := N)
          kappa beta g hbeta a omega)
        (canonicalMassWeightedMomentumPath (N := N)
          kappa beta g hbeta a omega time) time := by
    intro time
    rw [hXExactEq, hYExactEq]
    exact (massWeightedEquations_of_explicitHamiltonDerivatives
      (canonicalMass (N := N) omega) kappa beta g
      hDynamicsExact time).1
  have hYExact : ∀ time,
      HasMassWeightedDerivAt
        (canonicalMassWeightedMomentumPath (N := N)
          kappa beta g hbeta a omega)
        (-harmonicOperator (canonicalMass (N := N) omega)
            (canonicalMassWeightedPositionPath (N := N)
              kappa beta g hbeta a omega time) +
          canonicalExactNonlinearForcePath (N := N)
            kappa beta g hbeta a omega time) time := by
    intro time
    rw [hYExactEq, hXExactEq]
    unfold canonicalExactNonlinearForcePath
    rw [hqExact time]
    exact (massWeightedEquations_of_explicitHamiltonDerivatives
      (canonicalMass (N := N) omega) kappa beta g
      hDynamicsExact time).2
  have hXFree : ∀ time,
      HasMassWeightedDerivAt
        (canonicalMassWeightedPositionPath (N := N)
          kappa beta 0 hbeta a omega)
        (canonicalMassWeightedMomentumPath (N := N)
          kappa beta 0 hbeta a omega time) time := by
    intro time
    rw [hXFreeEq, hYFreeEq]
    exact (massWeightedEquations_of_explicitHamiltonDerivatives
      (canonicalMass (N := N) omega) kappa beta 0
      hDynamicsFree time).1
  have hYFree : ∀ time,
      HasMassWeightedDerivAt
        (canonicalMassWeightedMomentumPath (N := N)
          kappa beta 0 hbeta a omega)
        (-harmonicOperator (canonicalMass (N := N) omega)
          (canonicalMassWeightedPositionPath (N := N)
            kappa beta 0 hbeta a omega time)) time := by
    intro time
    rw [hYFreeEq, hXFreeEq]
    simpa only [transformedNonlinearForce_zero_coupling, add_zero] using
      (massWeightedEquations_of_explicitHamiltonDerivatives
        (canonicalMass (N := N) omega) kappa beta 0
        hDynamicsFree time).2

  refine
    { position_zero := ?_
      momentum_zero := ?_
      position_derivative := ?_
      momentum_derivative := ?_ }
  · simp [canonicalExactFreePositionError]
  · simp [canonicalExactFreeMomentumError]
  · intro time
    change HasMassWeightedDerivAt
      (fun s =>
        canonicalMassWeightedPositionPath (N := N)
            kappa beta g hbeta a omega s -
          canonicalMassWeightedPositionPath (N := N)
            kappa beta 0 hbeta a omega s)
      (canonicalMassWeightedMomentumPath (N := N)
          kappa beta g hbeta a omega time -
        canonicalMassWeightedMomentumPath (N := N)
          kappa beta 0 hbeta a omega time) time
    exact (hXExact time).sub (hXFree time)
  · intro time
    change HasMassWeightedDerivAt
      (fun s =>
        canonicalMassWeightedMomentumPath (N := N)
            kappa beta g hbeta a omega s -
          canonicalMassWeightedMomentumPath (N := N)
            kappa beta 0 hbeta a omega s)
      (-harmonicOperatorCLM (canonicalMass (N := N) omega)
          (canonicalMassWeightedPositionPath (N := N)
              kappa beta g hbeta a omega time -
            canonicalMassWeightedPositionPath (N := N)
              kappa beta 0 hbeta a omega time) +
        canonicalExactNonlinearForcePath (N := N)
          kappa beta g hbeta a omega time) time
    have hacceleration :
        (-harmonicOperator (canonicalMass (N := N) omega)
              (canonicalMassWeightedPositionPath (N := N)
                kappa beta g hbeta a omega time) +
            canonicalExactNonlinearForcePath (N := N)
              kappa beta g hbeta a omega time) -
          (-harmonicOperator (canonicalMass (N := N) omega)
            (canonicalMassWeightedPositionPath (N := N)
              kappa beta 0 hbeta a omega time)) =
        -harmonicOperatorCLM (canonicalMass (N := N) omega)
            (canonicalMassWeightedPositionPath (N := N)
                kappa beta g hbeta a omega time -
              canonicalMassWeightedPositionPath (N := N)
                kappa beta 0 hbeta a omega time) +
          canonicalExactNonlinearForcePath (N := N)
            kappa beta g hbeta a omega time := by
      simp only [harmonicOperatorCLM_apply]
      rw [map_sub]
      abel
    exact ((hYExact time).sub (hYFree time)).congr_deriv hacceleration

/-- Almost surely, the canonical exact/free errors obey the system above. -/
theorem canonicalExactFreeErrorEquations_ae
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      CanonicalExactFreeErrorEquations (N := N)
        kappa beta g hbeta a omega := by
  filter_upwards
    [physicalRealization_ae hN ha0 ha1 kappa beta g hbeta]
      with omega hphysical
  exact canonicalExactFreeErrorEquations_of_physicalRealization
    hN ha0 ha1 kappa beta g hbeta omega hphysical

#print axioms canonicalExactFreeErrorEquations_of_physicalRealization
#print axioms canonicalExactFreeErrorEquations_ae

end

end ArchonPhysics.R32CanonicalExactFreeBridgeV3

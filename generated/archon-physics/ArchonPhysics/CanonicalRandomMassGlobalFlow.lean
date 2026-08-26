import ArchonPhysics.CanonicalReducedParametricGlobalFlow
import ArchonPhysics.RandomMassReducedPhaseInitialData

/-!
# One canonical global flow shared by all random-mass samples

The pointwise continuation theorem constructs the correct cutoff flow, but its
existential quantifiers occur after one mass realization and one initial
state have been fixed.  This module reorders those quantifiers.

A `UniformRandomMassEnergyShell` stores a common mass box, inverse-mass box,
Poincare estimate, coupling parameters, and initial energy ceiling.  Its joint
compact shell determines one cutoff radius and hence one
`canonicalCutoffFlow`.  That same function is then proved to match every
genuine reduced trajectory whose initial state lies below the common energy
ceiling.  Composing it with the globally measurable random initial point gives
one measurable random trajectory map without choosing a flow sample by
sample.

The final specialization uses the fixed iid mass support `[4/5,6/5]`.  The
only model-specific input still exposed is the uniform nonlinear initial
energy bound `H`; no such bound is asserted in this file.
-/

namespace ArchonPhysics.CanonicalRandomMassGlobalFlow

open ArchonPhysics
open ArchonPhysics.CanonicalGlobalMeasurableFlow
open ArchonPhysics.CanonicalReducedParametricGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianGlobalExistence
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.JointMassEnergyCompactness
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.UniformMassGaugeCoercivity

noncomputable section

variable {N : Nat} [NeZero N]

/-- Uniform deterministic data used to choose a single joint cutoff radius.
The energy ceiling `H` is intended to be supplied by the random initial-energy
bound layer. -/
structure UniformRandomMassEnergyShell (N : Nat) [NeZero N] where
  C : Real
  mLower : Real
  mUpper : Real
  uLower : Real
  uUpper : Real
  kappa : Real
  beta : Real
  g : Real
  H : Real
  hC : 0 ≤ C
  hPoincare : ∀ (m : Lattice.PositiveMassConfig N)
    (q : Lattice.Configuration N),
    (∑ i, m.mass i * q i = 0) →
      ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖
  hmLowerPos : 0 < mLower
  huLowerNonneg : 0 ≤ uLower
  hbeta : 2 * kappa ^ 2 / 9 < beta

/-- A positive mass realization obeys all four common box bounds. -/
def UniformRandomMassEnergyShell.MassAdmissible
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) : Prop :=
  ∀ i, shell.mLower ≤ m.mass i ∧ m.mass i ≤ shell.mUpper ∧
    shell.uLower ≤ (m.mass i)⁻¹ ∧ (m.mass i)⁻¹ ≤ shell.uUpper

/-- Compactness of the joint shell supplies one radius before any mass
sample or initial state is selected. -/
theorem UniformRandomMassEnergyShell.exists_cutoffRadius
    (shell : UniformRandomMassEnergyShell N) :
    ∃ R : Real, 0 ≤ R ∧
      ∀ x ∈ jointMassInverseEnergySublevel (N := N)
          shell.mLower shell.mUpper shell.uLower shell.uUpper
          shell.kappa shell.beta shell.g shell.H,
        ‖jointPointToParametric shell.kappa shell.beta shell.g x‖ ≤ R := by
  exact exists_jointMassInverseEnergySublevel_parametric_norm_bound
    shell.hC shell.hPoincare shell.hmLowerPos shell.huLowerNonneg shell.hbeta

/-- The common cutoff radius selected from the entire joint shell. -/
def UniformRandomMassEnergyShell.cutoffRadius
    (shell : UniformRandomMassEnergyShell N) : Real :=
  Classical.choose shell.exists_cutoffRadius

theorem UniformRandomMassEnergyShell.cutoffRadius_nonneg
    (shell : UniformRandomMassEnergyShell N) :
    0 ≤ shell.cutoffRadius :=
  (Classical.choose_spec shell.exists_cutoffRadius).1

theorem UniformRandomMassEnergyShell.norm_jointPointToParametric_le_cutoffRadius
    (shell : UniformRandomMassEnergyShell N)
    {x : MassInversePhysicalPhaseSpace N}
    (hx : x ∈ jointMassInverseEnergySublevel
      shell.mLower shell.mUpper shell.uLower shell.uUpper
      shell.kappa shell.beta shell.g shell.H) :
    ‖jointPointToParametric shell.kappa shell.beta shell.g x‖ ≤
      shell.cutoffRadius :=
  (Classical.choose_spec shell.exists_cutoffRadius).2 x hx

/-- The single canonical cutoff flow attached to the whole uniform shell.
It has no mass-sample or initial-state argument. -/
def canonicalRandomMassGlobalFlow
    (shell : UniformRandomMassEnergyShell N) :
    ParametricPhaseSpace N × Real → ParametricPhaseSpace N :=
  canonicalCutoffFlow parameterizedHamiltonVectorField
    parameterizedHamiltonVectorField_contDiff shell.cutoffRadius
    shell.cutoffRadius_nonneg

theorem measurable_canonicalRandomMassGlobalFlow
    (shell : UniformRandomMassEnergyShell N) :
    Measurable (canonicalRandomMassGlobalFlow shell) := by
  exact canonicalCutoffFlow_measurable parameterizedHamiltonVectorField
    parameterizedHamiltonVectorField_contDiff shell.cutoffRadius
    shell.cutoffRadius_nonneg

@[simp] theorem canonicalRandomMassGlobalFlow_zero
    (shell : UniformRandomMassEnergyShell N) (x : ParametricPhaseSpace N) :
    canonicalRandomMassGlobalFlow shell (x, 0) = x := by
  exact canonicalCutoffFlow_zero parameterizedHamiltonVectorField
    parameterizedHamiltonVectorField_contDiff shell.cutoffRadius
    shell.cutoffRadius_nonneg x

/-- Quantifier-reordered continuation theorem: one already-fixed canonical
flow matches every admissible fixed-mass reduced trajectory below `H`. -/
theorem canonicalRandomMassGlobalFlow_matches_reduced
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (hmass : shell.MassAdmissible m)
    (z0 : ReducedPhaseSpace m)
    (henergy0 : reducedHamiltonian m shell.kappa shell.beta shell.g z0 ≤
      shell.H) :
    ∃ z : Real → ReducedPhaseSpace m,
      z 0 = z0 ∧
      (∀ t, HasDerivAt z
        (reducedVectorField m shell.kappa shell.beta shell.g (z t)) t) ∧
      (∀ t, canonicalRandomMassGlobalFlow shell
          (embedReducedPoint m shell.kappa shell.beta shell.g z0, t) =
        embedReducedPoint m shell.kappa shell.beta shell.g (z t)) ∧
      (∀ t, ‖canonicalRandomMassGlobalFlow shell
          (embedReducedPoint m shell.kappa shell.beta shell.g z0, t)‖ ≤
        shell.cutoffRadius) ∧
      (∀ t, HasDerivAt
        (fun s ↦ canonicalRandomMassGlobalFlow shell
          (embedReducedPoint m shell.kappa shell.beta shell.g z0, s))
        (parameterizedHamiltonVectorField
          (canonicalRandomMassGlobalFlow shell
            (embedReducedPoint m shell.kappa shell.beta shell.g z0, t))) t) ∧
      (∀ t, reducedHamiltonian m shell.kappa shell.beta shell.g (z t) =
        reducedHamiltonian m shell.kappa shell.beta shell.g z0) ∧
      ∀ t, reducedJointPoint m (z t) ∈
        jointMassInverseEnergySublevel shell.mLower shell.mUpper
          shell.uLower shell.uUpper shell.kappa shell.beta shell.g shell.H := by
  obtain ⟨z, hz0, hz⟩ :=
    exists_global_reducedTrajectory m shell.hbeta shell.g z0
  have hjoint : ∀ t, reducedJointPoint m (z t) ∈
      jointMassInverseEnergySublevel shell.mLower shell.mUpper
        shell.uLower shell.uUpper shell.kappa shell.beta shell.g shell.H :=
    fun t ↦ reducedTrajectory_jointPoint_mem m shell.mLower shell.mUpper
      shell.uLower shell.uUpper shell.kappa shell.beta shell.g shell.H
      (fun i ↦ (hmass i).1) (fun i ↦ (hmass i).2.1)
      (fun i ↦ (hmass i).2.2.1) (fun i ↦ (hmass i).2.2.2)
      z0 hz0 hz henergy0 t
  have hembeddedInside : ∀ t,
      ‖embedReducedPoint m shell.kappa shell.beta shell.g (z t)‖ ≤
        shell.cutoffRadius := by
    intro t
    rw [← jointPointToParametric_reducedJointPoint]
    exact shell.norm_jointPointToParametric_le_cutoffRadius (hjoint t)
  have hembeddedDeriv : ∀ t, HasDerivAt
      (fun s ↦ embedReducedPoint m shell.kappa shell.beta shell.g (z s))
      (parameterizedHamiltonVectorField
        (embedReducedPoint m shell.kappa shell.beta shell.g (z t))) t :=
    fun t ↦ hasDerivAt_embedReducedPoint m shell.kappa shell.beta shell.g (hz t)
  have hmatch : (fun t ↦ canonicalRandomMassGlobalFlow shell
      (embedReducedPoint m shell.kappa shell.beta shell.g z0, t)) =
      fun t ↦ embedReducedPoint m shell.kappa shell.beta shell.g (z t) := by
    unfold canonicalRandomMassGlobalFlow
    apply canonicalCutoffFlow_eq_of_global_solution_inside
      parameterizedHamiltonVectorField parameterizedHamiltonVectorField_contDiff
      shell.cutoffRadius shell.cutoffRadius_nonneg
    · simp [hz0]
    · exact hembeddedDeriv
    · exact hembeddedInside
  have hmatchPoint : ∀ t, canonicalRandomMassGlobalFlow shell
      (embedReducedPoint m shell.kappa shell.beta shell.g z0, t) =
        embedReducedPoint m shell.kappa shell.beta shell.g (z t) :=
    fun t ↦ congrFun hmatch t
  refine ⟨z, hz0, hz, hmatchPoint, ?_, ?_, ?_, hjoint⟩
  · intro t
    rw [hmatchPoint t]
    exact hembeddedInside t
  · intro t
    simpa only [hmatchPoint] using hembeddedDeriv t
  · exact fun t ↦ reducedHamiltonian_eq_initial_of_global_trajectory
      m shell.kappa shell.beta shell.g z0 hz0 hz t

variable {Omega : Type*} [MeasurableSpace Omega]

/-- One random trajectory map obtained by feeding every sample into the same
canonical flow. -/
def canonicalRandomMassTrajectory
    (shell : UniformRandomMassEnergyShell N)
    (ensemble : IIDMassPhaseEnsemble Omega) (a : Real) :
    Omega × Real → ParametricPhaseSpace N :=
  fun p ↦ canonicalRandomMassGlobalFlow shell
    (parametricInitialSample ensemble shell.kappa shell.beta shell.g a p.1, p.2)

theorem measurable_canonicalRandomMassTrajectory
    (shell : UniformRandomMassEnergyShell N)
    (ensemble : IIDMassPhaseEnsemble Omega) (a : Real) :
    Measurable (canonicalRandomMassTrajectory shell ensemble a) := by
  apply (measurable_canonicalRandomMassGlobalFlow shell).comp
  exact ((measurable_parametricInitialSample ensemble
    shell.kappa shell.beta shell.g a).comp measurable_fst).prodMk measurable_snd

@[simp] theorem canonicalRandomMassTrajectory_zero
    (shell : UniformRandomMassEnergyShell N)
    (ensemble : IIDMassPhaseEnsemble Omega) (a : Real) (omega : Omega) :
    canonicalRandomMassTrajectory shell ensemble a (omega, 0) =
      parametricInitialSample ensemble shell.kappa shell.beta shell.g a omega := by
  exact canonicalRandomMassGlobalFlow_zero shell _

/-- On a simple sample, a uniform nonlinear initial-energy bound is enough to
identify the shared random trajectory with a genuine reduced solution. -/
theorem canonicalRandomMassTrajectory_matches_reduced_of_energy_le
    (shell : UniformRandomMassEnergyShell N)
    (ensemble : IIDMassPhaseEnsemble Omega) (a : Real) (omega : Omega)
    (hsimple : OrderedSingleModeProjector.SimpleOrderedSpectrum
      (MeasurableOrderedModeCoupling.Harmonic.harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)))
    (hmass : shell.MassAdmissible
      (ensemble.restrictPositiveMass (N := N) omega))
    (henergy : reducedHamiltonian
      (ensemble.restrictPositiveMass (N := N) omega)
      shell.kappa shell.beta shell.g
      (reducedInitialStateOfSimple ensemble a omega hsimple) ≤ shell.H) :
    ∃ z : Real → ReducedPhaseSpace
        (ensemble.restrictPositiveMass (N := N) omega),
      z 0 = reducedInitialStateOfSimple ensemble a omega hsimple ∧
      (∀ t, HasDerivAt z
        (reducedVectorField (ensemble.restrictPositiveMass (N := N) omega)
          shell.kappa shell.beta shell.g (z t)) t) ∧
      (∀ t, canonicalRandomMassTrajectory shell ensemble a (omega, t) =
        embedReducedPoint (ensemble.restrictPositiveMass (N := N) omega)
          shell.kappa shell.beta shell.g (z t)) ∧
      ∀ t, reducedHamiltonian
        (ensemble.restrictPositiveMass (N := N) omega)
          shell.kappa shell.beta shell.g (z t) =
        reducedHamiltonian (ensemble.restrictPositiveMass (N := N) omega)
          shell.kappa shell.beta shell.g
            (reducedInitialStateOfSimple ensemble a omega hsimple) := by
  obtain ⟨z, hz0, hz, hmatch, _hbound, _hderiv, henergyConserved, _hjoint⟩ :=
    canonicalRandomMassGlobalFlow_matches_reduced shell
      (ensemble.restrictPositiveMass (N := N) omega) hmass
      (reducedInitialStateOfSimple ensemble a omega hsimple) henergy
  refine ⟨z, hz0, hz, ?_, henergyConserved⟩
  intro t
  unfold canonicalRandomMassTrajectory
  rw [parametricInitialSample_eq_embedReducedPoint
    ensemble shell.kappa shell.beta shell.g a omega hsimple]
  exact hmatch t

/-- A chosen mass-uniform Poincare constant for the fixed finite lattice. -/
def canonicalUniformPoincareConstant (N : Nat) [NeZero N] : Real :=
  Classical.choose (exists_uniform_massWeighted_poincareConstant (N := N))

theorem canonicalUniformPoincareConstant_pos (N : Nat) [NeZero N] :
    0 < canonicalUniformPoincareConstant N :=
  (Classical.choose_spec
    (exists_uniform_massWeighted_poincareConstant (N := N))).1

theorem canonicalUniformPoincareConstant_spec (N : Nat) [NeZero N] :
    ∀ (m : Lattice.PositiveMassConfig N) (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) →
        ‖q‖ ≤ canonicalUniformPoincareConstant N *
          ‖Lattice.forwardDifference q‖ :=
  (Classical.choose_spec
    (exists_uniform_massWeighted_poincareConstant (N := N))).2

theorem randomMassUpper_pos : 0 < RandomEnsemble.massUpper :=
  RandomEnsemble.massLower_pos.trans_le
    RandomEnsemble.massLower_le_massUpper

/-- Canonical uniform shell for the fixed iid support.  Its only free size
parameter is the common nonlinear initial-energy ceiling `H`. -/
def canonicalIIDUniformEnergyShell
    (N : Nat) [NeZero N] (kappa beta g H : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    UniformRandomMassEnergyShell N where
  C := canonicalUniformPoincareConstant N
  mLower := RandomEnsemble.massLower
  mUpper := RandomEnsemble.massUpper
  uLower := (RandomEnsemble.massUpper)⁻¹
  uUpper := (RandomEnsemble.massLower)⁻¹
  kappa := kappa
  beta := beta
  g := g
  H := H
  hC := (canonicalUniformPoincareConstant_pos N).le
  hPoincare := canonicalUniformPoincareConstant_spec N
  hmLowerPos := RandomEnsemble.massLower_pos
  huLowerNonneg := inv_nonneg.mpr (randomMassUpper_pos.le)
  hbeta := hbeta

/-- Every verified iid ensemble lies pointwise in the canonical mass and
inverse-mass box; this uses the representative-level support field. -/
theorem massAdmissible_canonicalIIDUniformEnergyShell
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa beta g H : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : Omega) :
    (canonicalIIDUniformEnergyShell N kappa beta g H hbeta).MassAdmissible
      (ensemble.restrictPositiveMass (N := N) omega) := by
  intro i
  have hs := ensemble.mass_mem_support i.val omega
  have hmpos := (ensemble.restrictPositiveMass (N := N) omega).mass_pos i
  exact ⟨hs.1, hs.2,
    (inv_le_inv₀ randomMassUpper_pos hmpos).2 hs.2,
    (inv_le_inv₀ hmpos RandomEnsemble.massLower_pos).2 hs.1⟩

/-- Explicit shared flow for the canonical iid mass box. -/
def canonicalIIDRandomMassGlobalFlow
    (N : Nat) [NeZero N] (kappa beta g H : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ParametricPhaseSpace N × Real → ParametricPhaseSpace N :=
  canonicalRandomMassGlobalFlow
    (canonicalIIDUniformEnergyShell N kappa beta g H hbeta)

theorem measurable_canonicalIIDRandomMassGlobalFlow
    (kappa beta g H : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    Measurable (canonicalIIDRandomMassGlobalFlow N kappa beta g H hbeta) :=
  measurable_canonicalRandomMassGlobalFlow _

/-- Random initial samples from any verified iid ensemble, all evolved by the
same canonical flow selected from the fixed support and energy ceiling. -/
def canonicalIIDRandomMassTrajectory
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa beta g H : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) : Omega × Real → ParametricPhaseSpace N :=
  canonicalRandomMassTrajectory
    (canonicalIIDUniformEnergyShell N kappa beta g H hbeta) ensemble a

theorem measurable_canonicalIIDRandomMassTrajectory
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa beta g H : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) :
    Measurable
      (canonicalIIDRandomMassTrajectory (N := N)
        ensemble kappa beta g H hbeta a) :=
  measurable_canonicalRandomMassTrajectory _ ensemble a

@[simp] theorem canonicalIIDRandomMassTrajectory_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa beta g H : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : Omega) :
    canonicalIIDRandomMassTrajectory (N := N)
        ensemble kappa beta g H hbeta a
        (omega, 0) =
      parametricInitialSample ensemble (N := N) kappa beta g a omega := by
  exact canonicalRandomMassTrajectory_zero _ ensemble a omega

/-- For the fixed iid support, the sole remaining samplewise input is the
uniform nonlinear initial-energy estimate. -/
theorem canonicalIIDRandomMassTrajectory_matches_reduced_of_energy_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa beta g H : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : Omega)
    (hsimple : OrderedSingleModeProjector.SimpleOrderedSpectrum
      (MeasurableOrderedModeCoupling.Harmonic.harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)))
    (henergy : reducedHamiltonian
      (ensemble.restrictPositiveMass (N := N) omega) kappa beta g
      (reducedInitialStateOfSimple ensemble a omega hsimple) ≤ H) :
    ∃ z : Real → ReducedPhaseSpace
        (ensemble.restrictPositiveMass (N := N) omega),
      z 0 = reducedInitialStateOfSimple ensemble a omega hsimple ∧
      (∀ t, HasDerivAt z
        (reducedVectorField (ensemble.restrictPositiveMass (N := N) omega)
          kappa beta g (z t)) t) ∧
      (∀ t, canonicalIIDRandomMassTrajectory ensemble
          kappa beta g H hbeta a (omega, t) =
        embedReducedPoint (ensemble.restrictPositiveMass (N := N) omega)
          kappa beta g (z t)) ∧
      ∀ t, reducedHamiltonian
        (ensemble.restrictPositiveMass (N := N) omega) kappa beta g (z t) =
        reducedHamiltonian (ensemble.restrictPositiveMass (N := N) omega)
          kappa beta g
            (reducedInitialStateOfSimple ensemble a omega hsimple) := by
  exact canonicalRandomMassTrajectory_matches_reduced_of_energy_le
    (canonicalIIDUniformEnergyShell N kappa beta g H hbeta)
    ensemble a omega hsimple
    (massAdmissible_canonicalIIDUniformEnergyShell
      ensemble kappa beta g H hbeta omega) henergy

end

end ArchonPhysics.CanonicalRandomMassGlobalFlow

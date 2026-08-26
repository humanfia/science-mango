import ArchonPhysics.GlobalReducedParametricFlowAdapter

/-!
# Canonical measurable global flow on a joint reduced energy shell

This module completes the continuation adapter.  A genuine coercive reduced
trajectory supplies the invariant compact shell; the canonical cutoff flow is
then identified with its embedding by global uniqueness.  Consequently one
jointly measurable ambient flow solves the untruncated Hamilton ODE for every
fixed-mass initial point satisfying the stated common box and energy bounds.
-/

namespace ArchonPhysics.CanonicalReducedParametricGlobalFlow

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianGlobalExistence
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.JointMassEnergyCompactness
open ArchonPhysics.CanonicalGlobalMeasurableFlow
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open Set Metric

noncomputable section

variable {N : Nat} [NeZero N]

/-- The continuous image of a joint mass--inverse-mass energy shell is compact
in the common parameter--phase space. -/
theorem jointMassInverseEnergySublevel_parametric_image_isCompact
    {C mLower mUpper uLower uUpper kappa beta g H : Real}
    (hC : 0 ≤ C)
    (hPoincare : ∀ (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) →
        ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖)
    (hmLower : 0 < mLower) (huLower : 0 ≤ uLower)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    IsCompact
      (jointPointToParametric (N := N) kappa beta g ''
        jointMassInverseEnergySublevel mLower mUpper uLower uUpper
          kappa beta g H) := by
  exact (jointMassInverseEnergySublevel_isCompact hC hPoincare
    hmLower huLower hbeta).image
      (continuous_jointPointToParametric kappa beta g)

/-- One nonnegative cutoff radius contains the whole parameterized image of
the joint compact shell. -/
theorem exists_jointMassInverseEnergySublevel_parametric_norm_bound
    {C mLower mUpper uLower uUpper kappa beta g H : Real}
    (hC : 0 ≤ C)
    (hPoincare : ∀ (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) →
        ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖)
    (hmLower : 0 < mLower) (huLower : 0 ≤ uLower)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ∃ R : Real, 0 ≤ R ∧
      ∀ x ∈ jointMassInverseEnergySublevel (N := N)
          mLower mUpper uLower uUpper kappa beta g H,
        ‖jointPointToParametric kappa beta g x‖ ≤ R := by
  have hcompact :=
    jointMassInverseEnergySublevel_parametric_image_isCompact
      (mUpper := mUpper) (uUpper := uUpper) (g := g) (H := H)
      hC hPoincare hmLower huLower hbeta
  obtain ⟨r, hr⟩ := hcompact.isBounded.subset_closedBall
    (0 : ParametricPhaseSpace N)
  refine ⟨max r 0, le_max_right r 0, fun x hx ↦ ?_⟩
  have himage : jointPointToParametric kappa beta g x ∈
      jointPointToParametric (N := N) kappa beta g ''
        jointMassInverseEnergySublevel mLower mUpper uLower uUpper
          kappa beta g H := ⟨x, hx, rfl⟩
  have hball := hr himage
  have hnorm : ‖jointPointToParametric kappa beta g x‖ ≤ r := by
    simpa only [mem_closedBall, dist_zero_right] using hball
  exact hnorm.trans (le_max_left r 0)

/-- Energy conservation for any genuine two-sided reduced trajectory. -/
theorem reducedHamiltonian_eq_initial_of_global_trajectory
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    {z : Real → ReducedPhaseSpace m} (z0 : ReducedPhaseSpace m)
    (hz0 : z 0 = z0)
    (hz : ∀ t, HasDerivAt z
      (reducedVectorField m kappa beta g (z t)) t) (t : Real) :
    reducedHamiltonian m kappa beta g (z t) =
      reducedHamiltonian m kappa beta g z0 := by
  calc
    reducedHamiltonian m kappa beta g (z t) =
        reducedHamiltonian m kappa beta g (z 0) := by
      exact reducedHamiltonian_eq_of_integralCurveOn m kappa beta g
        convex_univ (fun s _hs ↦ (hz s).hasDerivWithinAt)
        (mem_univ t) (mem_univ 0)
    _ = reducedHamiltonian m kappa beta g z0 := by rw [hz0]

/-- The mass, reciprocal mass, two gauges, and energy bound remain in the
same joint shell for the entire genuine reduced trajectory. -/
theorem reducedTrajectory_jointPoint_mem
    (m : Lattice.PositiveMassConfig N)
    (mLower mUpper uLower uUpper kappa beta g H : Real)
    (hmLower : ∀ i, mLower ≤ m.mass i)
    (hmUpper : ∀ i, m.mass i ≤ mUpper)
    (huLower : ∀ i, uLower ≤ (m.mass i)⁻¹)
    (huUpper : ∀ i, (m.mass i)⁻¹ ≤ uUpper)
    {z : Real → ReducedPhaseSpace m} (z0 : ReducedPhaseSpace m)
    (hz0 : z 0 = z0)
    (hz : ∀ t, HasDerivAt z
      (reducedVectorField m kappa beta g (z t)) t)
    (henergy0 : reducedHamiltonian m kappa beta g z0 ≤ H)
    (t : Real) :
    reducedJointPoint m (z t) ∈
      jointMassInverseEnergySublevel mLower mUpper uLower uUpper
        kappa beta g H := by
  apply reducedJointPoint_mem_jointMassInverseEnergySublevel
    m (z t) mLower mUpper uLower uUpper kappa beta g H
    hmLower hmUpper huLower huUpper
  rw [reducedHamiltonian_eq_initial_of_global_trajectory
    m kappa beta g z0 hz0 hz t]
  exact henergy0

/-- The complete adapter: one canonical measurable cutoff flow is globally
equal, on the selected initial point, to an embedded genuine reduced
trajectory.  Hence it never reaches the cutoff and solves the untruncated
parameterized Hamilton ODE for every time. -/
theorem exists_canonical_measurable_global_flow_matching_reduced
    {C mLower mUpper uLower uUpper kappa beta g H : Real}
    (hC : 0 ≤ C)
    (hPoincare : ∀ (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) →
        ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖)
    (hmLowerPos : 0 < mLower) (huLowerNonneg : 0 ≤ uLower)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (m : Lattice.PositiveMassConfig N)
    (hmLower : ∀ i, mLower ≤ m.mass i)
    (hmUpper : ∀ i, m.mass i ≤ mUpper)
    (huLower : ∀ i, uLower ≤ (m.mass i)⁻¹)
    (huUpper : ∀ i, (m.mass i)⁻¹ ≤ uUpper)
    (z0 : ReducedPhaseSpace m)
    (henergy0 : reducedHamiltonian m kappa beta g z0 ≤ H) :
    ∃ R : Real, 0 ≤ R ∧
      ∃ flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N,
        Measurable flow ∧
        (∀ x, flow (x, 0) = x) ∧
        ∃ z : Real → ReducedPhaseSpace m,
          z 0 = z0 ∧
          (∀ t, HasDerivAt z
            (reducedVectorField m kappa beta g (z t)) t) ∧
          (∀ t, flow (embedReducedPoint m kappa beta g z0, t) =
            embedReducedPoint m kappa beta g (z t)) ∧
          (∀ t, ‖flow (embedReducedPoint m kappa beta g z0, t)‖ ≤ R) ∧
          (∀ t, HasDerivAt
            (fun s ↦ flow (embedReducedPoint m kappa beta g z0, s))
            (parameterizedHamiltonVectorField
              (flow (embedReducedPoint m kappa beta g z0, t))) t) ∧
          (∀ t, reducedHamiltonian m kappa beta g (z t) =
            reducedHamiltonian m kappa beta g z0) ∧
          ∀ t, reducedJointPoint m (z t) ∈
            jointMassInverseEnergySublevel mLower mUpper uLower uUpper
              kappa beta g H := by
  obtain ⟨R, hR, hbound⟩ :=
    exists_jointMassInverseEnergySublevel_parametric_norm_bound
      hC hPoincare hmLowerPos huLowerNonneg hbeta
  obtain ⟨z, hz0, hz⟩ :=
    exists_global_reducedTrajectory m hbeta g z0
  have hjoint : ∀ t, reducedJointPoint m (z t) ∈
      jointMassInverseEnergySublevel mLower mUpper uLower uUpper
        kappa beta g H := fun t ↦
    reducedTrajectory_jointPoint_mem m mLower mUpper uLower uUpper
      kappa beta g H hmLower hmUpper huLower huUpper z0 hz0 hz henergy0 t
  have hembeddedInside : ∀ t,
      ‖embedReducedPoint m kappa beta g (z t)‖ ≤ R := by
    intro t
    rw [← jointPointToParametric_reducedJointPoint]
    exact hbound _ (hjoint t)
  have hembeddedDeriv : ∀ t, HasDerivAt
      (fun s ↦ embedReducedPoint m kappa beta g (z s))
      (parameterizedHamiltonVectorField
        (embedReducedPoint m kappa beta g (z t))) t :=
    fun t ↦ hasDerivAt_embedReducedPoint m kappa beta g (hz t)
  let flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N :=
    canonicalCutoffFlow parameterizedHamiltonVectorField
      parameterizedHamiltonVectorField_contDiff R hR
  have hflowMeasurable : Measurable flow :=
    canonicalCutoffFlow_measurable parameterizedHamiltonVectorField
      parameterizedHamiltonVectorField_contDiff R hR
  have hflowZero : ∀ x, flow (x, 0) = x := fun x ↦
    canonicalCutoffFlow_zero parameterizedHamiltonVectorField
      parameterizedHamiltonVectorField_contDiff R hR x
  have hmatch : (fun t ↦
      flow (embedReducedPoint m kappa beta g z0, t)) =
      fun t ↦ embedReducedPoint m kappa beta g (z t) := by
    apply canonicalCutoffFlow_eq_of_global_solution_inside
      parameterizedHamiltonVectorField
      parameterizedHamiltonVectorField_contDiff R hR
    · simp [hz0]
    · exact hembeddedDeriv
    · exact hembeddedInside
  have hmatchPoint : ∀ t,
      flow (embedReducedPoint m kappa beta g z0, t) =
        embedReducedPoint m kappa beta g (z t) := fun t ↦
    congrFun hmatch t
  refine ⟨R, hR, flow, hflowMeasurable, hflowZero, z, hz0, hz,
    hmatchPoint, ?_, ?_, ?_, hjoint⟩
  · intro t
    rw [hmatchPoint t]
    exact hembeddedInside t
  · intro t
    simpa only [hmatchPoint] using hembeddedDeriv t
  · exact fun t ↦ reducedHamiltonian_eq_initial_of_global_trajectory
      m kappa beta g z0 hz0 hz t

end

end ArchonPhysics.CanonicalReducedParametricGlobalFlow

import ArchonPhysics.MeasurableHamiltonianDynamics
import Mathlib.Analysis.ODE.ExistUnique

/-!
# A jointly continuous local Hamiltonian flow

The inverse masses and the three coupling parameters are adjoined to phase
space as frozen coordinates.  The resulting autonomous vector field is
polynomial on a fixed finite-dimensional Euclidean space.  Picard--Lindelof
therefore produces one local flow which is continuous jointly in the frozen
parameters, the initial state, and time.

This is a local parameter-dependence result.  It neither constructs the
global random flow nor asserts any kinetic or thermalization limit.
-/

namespace ArchonPhysics.ParametricLocalHamiltonianFlow

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients
open Metric Set

noncomputable section

variable {N : Nat} [NeZero N]

/-- Fixed Euclidean parameter space: inverse masses, `kappa`, `beta`, and `g`. -/
abbrev HamiltonParameterSpace (N : Nat) [NeZero N] :=
  HilbertConfiguration N × (Real × (Real × Real))

/-- Parameters together with position and momentum. -/
abbrev ParametricPhaseSpace (N : Nat) [NeZero N] :=
  HamiltonParameterSpace N ×
    (HilbertConfiguration N × HilbertConfiguration N)

/-- Coordinatewise multiplication by the inverse-mass parameter. -/
def inverseMassParameterMomentum
    (u p : HilbertConfiguration N) : HilbertConfiguration N :=
  ∑ i : Lattice.Site N,
    ((EuclideanSpace.proj (𝕜 := Real) i) u *
      (EuclideanSpace.proj (𝕜 := Real) i) p) •
        EuclideanSpace.single i 1

/-- A continuous-linear-coordinate presentation of the joint polynomial
potential gradient. -/
def parameterizedPotentialGradient
    (kappa beta g : Real) (q : HilbertConfiguration N) :
    HilbertConfiguration N :=
  ∑ i : Lattice.Site N,
    potentialDerivative kappa beta g (bondFunctional i q) •
      bondDirection i

@[simp] theorem parameterizedPotentialGradient_eq
    (kappa beta g : Real) (q : HilbertConfiguration N) :
    parameterizedPotentialGradient kappa beta g q =
      potentialGradient kappa beta g q := by
  simp only [parameterizedPotentialGradient, potentialGradient,
    bondFunctional_apply]


/-- The explicit Hamiltonian vector field with inverse masses as free
Euclidean parameters. -/
def parameterizedHamiltonVectorField
    (x : ParametricPhaseSpace N) : ParametricPhaseSpace N :=
  let u := x.1.1
  let kappa := x.1.2.1
  let beta := x.1.2.2.1
  let g := x.1.2.2.2
  let q := x.2.1
  let p := x.2.2
  ((0, (0, (0, 0))),
    (inverseMassParameterMomentum u p,
      -parameterizedPotentialGradient kappa beta g q))

/-- The frozen parameter coordinates really have zero derivative. -/
@[simp] theorem parameterizedHamiltonVectorField_parameters
    (x : ParametricPhaseSpace N) :
    (parameterizedHamiltonVectorField x).1 = 0 := by
  rfl

/-- Supplying reciprocal positive masses recovers the actual Hamiltonian
right-hand side in the phase-space coordinates. -/
theorem parameterizedHamiltonVectorField_phase_eq
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (z : HilbertConfiguration N × HilbertConfiguration N) :
    (parameterizedHamiltonVectorField
      ((WithLp.toLp 2 fun i ↦ (m.mass i)⁻¹, (kappa, (beta, g))), z)).2 =
      MeasurableHamiltonianDynamics.explicitHamiltonVectorField
        m kappa beta g z := by
  apply Prod.ext
  · ext i
    simp [parameterizedHamiltonVectorField, inverseMassParameterMomentum,
      MeasurableHamiltonianDynamics.explicitHamiltonVectorField,
      inverseMassMomentum_apply, Pi.single_apply]
  · simp [parameterizedHamiltonVectorField,
      MeasurableHamiltonianDynamics.explicitHamiltonVectorField]

/-- The adjoined vector field is continuously differentiable jointly in all
parameters and phase-space coordinates. -/
theorem parameterizedHamiltonVectorField_contDiff :
    ContDiff Real 1
      (parameterizedHamiltonVectorField (N := N)) := by
  unfold parameterizedHamiltonVectorField
  unfold inverseMassParameterMomentum parameterizedPotentialGradient
    potentialDerivative
  fun_prop

/-- A `C^1` autonomous vector field has a local flow continuous jointly in
the initial point and time on a nontrivial closed ball and time interval. -/
theorem exists_local_continuous_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E] {f : E → E} {x0 : E}
    (hf : ContDiffAt Real 1 f x0) (t0 : Real) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∃ r : NNReal, 0 < r ∧
        ∃ flow : E × Real → E,
          (∀ x ∈ closedBall x0 (r : Real),
            flow (x, t0) = x ∧
              ∀ t ∈ Icc (t0 - epsilon) (t0 + epsilon),
                HasDerivWithinAt (fun s ↦ flow (x, s))
                  (f (flow (x, t)))
                  (Icc (t0 - epsilon) (t0 + epsilon)) t) ∧
          ContinuousOn flow
            (closedBall x0 (r : Real) ×ˢ
              Icc (t0 - epsilon) (t0 + epsilon)) := by
  obtain ⟨epsilon, hepsilon, a, r, L, K, hr, hpicard⟩ :=
    IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨flow, hflow, hcontinuous⟩ :=
    (hpicard t0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  exact ⟨epsilon, hepsilon, r, hr, flow, hflow, hcontinuous⟩

/-- The concrete parameterized lattice vector field admits such a jointly
continuous local flow around every parameter-state point. -/
theorem exists_parameterized_local_continuous_flow
    (x0 : ParametricPhaseSpace N) (t0 : Real) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∃ r : NNReal, 0 < r ∧
        ∃ flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N,
          (∀ x ∈ closedBall x0 (r : Real),
            flow (x, t0) = x ∧
              ∀ t ∈ Icc (t0 - epsilon) (t0 + epsilon),
                HasDerivWithinAt (fun s ↦ flow (x, s))
                  (parameterizedHamiltonVectorField (flow (x, t)))
                  (Icc (t0 - epsilon) (t0 + epsilon)) t) ∧
          ContinuousOn flow
            (closedBall x0 (r : Real) ×ˢ
              Icc (t0 - epsilon) (t0 + epsilon)) := by
  exact exists_local_continuous_flow
    (parameterizedHamiltonVectorField_contDiff.contDiffAt) t0

end

end ArchonPhysics.ParametricLocalHamiltonianFlow

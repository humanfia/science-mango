import ArchonPhysics.ConcreteHamiltonGradients
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurable explicit Hamilton vector fields

This module proves measurability of the concrete finite-chain Hamiltonian
right-hand side when masses, coupling parameters, and phase-space states vary
measurably.  It is the parameter-side input needed by a future measurable
solution-map theorem; no solution, flow, or thermalization claim is made here.
-/

namespace ArchonPhysics.MeasurableHamiltonianDynamics

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]
variable {N : Nat} [NeZero N]

/-- Fixed-time measurability plus continuous sample paths imply joint
sample-time measurability. This isolates the exact Caratheodory adapter needed
by a future random microscopic flow construction. -/
theorem measurable_joint_trajectory_of_continuous_paths
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (trajectory : Omega → Real → E)
    (hpath : ∀ omega, Continuous (trajectory omega))
    (heval : ∀ t, Measurable fun omega => trajectory omega t) :
    Measurable fun p : Omega × Real => trajectory p.1 p.2 := by
  have htimeFirst : Measurable
      (Function.uncurry fun t omega => trajectory omega t) :=
    MeasureTheory.measurable_uncurry_of_continuous_of_measurable
      (fun omega => hpath omega) heval
  exact htimeFirst.comp measurable_swap

/-- Coordinatewise measurable masses and a measurable momentum give a
measurable inverse-mass Hamiltonian velocity. -/
theorem measurable_inverseMassMomentum_of_coordinate
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (momentum : Omega → HilbertConfiguration N)
    (hmass : ∀ i, Measurable fun omega => (massSample omega).mass i)
    (hmomentum : Measurable momentum) :
    Measurable fun omega =>
      inverseMassMomentum (massSample omega) (momentum omega) := by
  unfold inverseMassMomentum
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  exact (hmass i).inv.mul
    ((measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 _).comp hmomentum))

/-- The stabilized polynomial potential gradient is jointly measurable in
its three scalar parameters and the position. -/
theorem measurable_potentialGradient_of_parameters
    (kappa beta g : Omega → Real)
    (position : Omega → HilbertConfiguration N)
    (hkappa : Measurable kappa) (hbeta : Measurable beta)
    (hg : Measurable g) (hposition : Measurable position) :
    Measurable fun omega =>
      potentialGradient (kappa omega) (beta omega) (g omega)
        (position omega) := by
  unfold potentialGradient
  apply Finset.measurable_sum
  intro i _hi
  have hraw : Measurable fun omega => WithLp.ofLp (position omega) :=
    (WithLp.measurable_ofLp 2 _).comp hposition
  have hforward : Measurable fun omega =>
      Lattice.forwardDifference (asConfiguration (position omega)) i := by
    simp only [Lattice.forwardDifference, asConfiguration]
    exact ((measurable_pi_apply (i + 1)).comp hraw).sub
      ((measurable_pi_apply i).comp hraw)
  have hscalar : Measurable fun omega =>
      potentialDerivative (kappa omega) (beta omega) (g omega)
        (Lattice.forwardDifference (asConfiguration (position omega)) i) := by
    unfold potentialDerivative
    fun_prop
  exact hscalar.smul_const (bondDirection i)

/-- The full explicit Hamiltonian vector field on the fixed Euclidean phase
space, ordered as position then momentum. -/
def explicitHamiltonVectorField
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (z : HilbertConfiguration N × HilbertConfiguration N) :
    HilbertConfiguration N × HilbertConfiguration N :=
  (inverseMassMomentum m z.2, -potentialGradient kappa beta g z.1)

/-- Coordinatewise measurable masses, measurable parameters, and a measurable
state give a measurable evaluation of the actual Hamiltonian right-hand side. -/
theorem measurable_explicitHamiltonVectorField
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Omega → Real)
    (state : Omega → HilbertConfiguration N × HilbertConfiguration N)
    (hmass : ∀ i, Measurable fun omega => (massSample omega).mass i)
    (hkappa : Measurable kappa) (hbeta : Measurable beta)
    (hg : Measurable g) (hstate : Measurable state) :
    Measurable fun omega =>
      explicitHamiltonVectorField (massSample omega)
        (kappa omega) (beta omega) (g omega) (state omega) := by
  have hvelocity : Measurable fun omega =>
      inverseMassMomentum (massSample omega) (state omega).2 := by
    apply measurable_inverseMassMomentum_of_coordinate massSample
      (fun omega => (state omega).2) hmass
    exact measurable_snd.comp hstate
  have hforce : Measurable fun omega =>
      -potentialGradient (kappa omega) (beta omega) (g omega)
        (state omega).1 := by
    apply Measurable.neg
    apply measurable_potentialGradient_of_parameters kappa beta g
      (fun omega => (state omega).1) hkappa hbeta hg
    exact measurable_fst.comp hstate
  exact hvelocity.prodMk hforce

end

end ArchonPhysics.MeasurableHamiltonianDynamics

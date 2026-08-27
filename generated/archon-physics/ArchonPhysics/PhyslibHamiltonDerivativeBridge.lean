import ArchonPhysics.MassWeightedHamiltonianDynamics

/-!
# From Physlib time derivatives to real-parameter Hamilton trajectories

Physlib states Hamilton's equations using its one-dimensional `Time` space and
`Time.deriv`.  The local modal/Duhamel interfaces use Mathlib's
`HasDerivAt` for real-parameter curves.  This module proves the exact change
of parameter through `Time.toRealCLE` and connects a differentiable Physlib
Hamilton trajectory to the verified mass-weighted modal tensor equation.

No existence, uniqueness, limiting, or thermalization assertion is made.
-/

namespace ArchonPhysics.PhyslibHamiltonDerivativeBridge

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ReducedModeTransform
open Time

noncomputable section

/-- The inverse canonical continuous-linear equivalence sends real one to
the positive unit time vector. -/
theorem toRealCLE_symm_one :
    Time.toRealCLE.symm (1 : Real) = (1 : Time) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  change (1 : Real) = (1 : Time).val
  rw [Time.one_val]

/-- A differentiable `Time`-curve, reparametrized by the canonical real
coordinate, has derivative equal to Physlib's `Time.deriv`. -/
theorem hasDerivAt_comp_toRealCLE_symm
    {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
    (w : Time → E) (tau : Real)
    (hw : DifferentiableAt Real w (Time.toRealCLE.symm tau)) :
    HasDerivAt (fun s : Real ↦ w (Time.toRealCLE.symm s))
      (∂ₜ w (Time.toRealCLE.symm tau)) tau := by
  simpa [Function.comp_def, Time.deriv_eq, toRealCLE_symm_one] using
    hw.hasFDerivAt.comp_hasDerivAt_of_eq tau
      ((Time.toRealCLE.symm : Real →L[Real] Time).hasDerivAt) rfl

/-- Canonical real reparametrization of a Physlib time curve. -/
def realReparametrize {E : Type} (w : Time → E) : Real → E :=
  fun tau ↦ w (Time.toRealCLE.symm tau)

/-- A differentiable Physlib Hamilton trajectory supplies the explicit
`HasDerivAt` witnesses required by the mass-weighted dynamics module. -/
theorem hasExplicitHamiltonDerivatives_of_physlib
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q) :
    HasExplicitHamiltonDerivatives m kappa beta g
      (realReparametrize p) (realReparametrize q) := by
  have hExplicit :=
    (satisfiesHamiltonEquations_iff_explicit m kappa beta g p q).mp hHamilton
  intro tau
  let t : Time := Time.toRealCLE.symm tau
  constructor
  · have hqDeriv := hasDerivAt_comp_toRealCLE_symm q tau (hq t)
    rw [hExplicit.1 t] at hqDeriv
    exact hqDeriv
  · have hpDeriv := hasDerivAt_comp_toRealCLE_symm p tau (hp t)
    rw [hExplicit.2 t] at hpDeriv
    exact hpDeriv

/-- A differentiable Physlib Hamilton trajectory obeys the exact
mass-weighted forced harmonic equations after canonical real
reparametrization. -/
theorem massWeightedEquations_of_physlib
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (tau : Real) :
    HasDerivAt
        (massWeightedPosition m (realReparametrize q))
        (massWeightedMomentum m (realReparametrize p) tau) tau ∧
      HasDerivAt
        (massWeightedMomentum m (realReparametrize p))
        (-harmonicOperator m
            (massWeightedPosition m (realReparametrize q) tau) +
          transformedNonlinearForce m kappa beta g
            (realReparametrize q tau)) tau := by
  exact massWeightedEquations_of_explicitHamiltonDerivatives
    m kappa beta g
    (hasExplicitHamiltonDerivatives_of_physlib
      m kappa beta g p q hp hq hHamilton) tau

/-- The same Physlib trajectory projects to the exact scalar mode equation
with the three- and four-leg interaction-tensor forcing. -/
theorem modalScalarTensorEquations_of_physlib
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (tau : Real) :
    HasDerivAt
        (fun s ↦ modalCoordinates m
          (massWeightedPosition m (realReparametrize q) s) k)
        (modalCoordinates m
          (massWeightedMomentum m (realReparametrize p) tau) k) tau ∧
      HasDerivAt
        (fun s ↦ modalCoordinates m
          (massWeightedMomentum m (realReparametrize p) s) k)
        (-(ModalPhaseMismatch.modeFrequency m k) ^ 2 *
            modalCoordinates m
              (massWeightedPosition m (realReparametrize q) tau) k +
          tensorNonlinearForce m kappa beta g
            (modalCoordinates m
              (massWeightedPosition m (realReparametrize q) tau)) k) tau := by
  exact modalScalarTensorEquations_of_explicitHamiltonDerivatives
    m kappa beta g k
    (hasExplicitHamiltonDerivatives_of_physlib
      m kappa beta g p q hp hq hHamilton) tau

end

end ArchonPhysics.PhyslibHamiltonDerivativeBridge

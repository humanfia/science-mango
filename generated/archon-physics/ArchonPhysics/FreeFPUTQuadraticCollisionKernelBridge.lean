import ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
import ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
import ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

/-!
# The free quadratic Picard term as the finite-time collision kernel

The first-Picard character expansion and the microscopic finite-time
collision polynomial were constructed independently.  This module identifies
their termwise kernels.  For one ordered quadratic phase term, the squared
Hamiltonian vertex and its signed frequency mismatch are exactly the data in
`finiteTimeCollisionKernel`.

With energy-normalized radii, the diagonal ordered-pair contribution is the
same kernel multiplied by the two input actions.  The statement keeps an
explicit positive-frequency hypothesis; no coherent cross term, return-tree
feedback, kinetic limit, or nonlinear remainder is removed here.
-/

namespace ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

noncomputable section

/-- One quadratic phase term, read as a signed ordered three-wave tuple, has
exactly the existing microscopic finite-time collision kernel. -/
theorem finiteTimeCollisionKernel_quadratic_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling time : Real)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    finiteTimeCollisionKernel m coupling
        (quadraticCollisionSign term) time
        (quadraticCollisionModes observed term) =
      coupling ^ 2 *
        normalizedInteractionWeight m
          (quadraticCollisionModes observed term) *
        finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed term) time := by
  unfold finiteTimeCollisionKernel hamiltonianInteractionVertex
  rw [mul_pow, normalizedInteractionVertex_sq,
    ← quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch]

/-- For nonnegative modal energies and a positive-frequency three-leg tuple,
the diagonal normalized first-Picard contribution is the finite-time
collision kernel times the two incoming actions. -/
theorem physicalQuadraticDiagonalTerm_eq_finiteTimeCollisionKernel_mul_actions
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (henergy : ∀ r : Fin 2, 0 ≤ energy (term.1 r))
    (hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    Complex.normSq
        (freeQuadraticDuhamelCoefficient
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) term) *
        finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed term) time =
      finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign term) time
          (quadraticCollisionModes observed term) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (term.1 r) := by
  rw [physlibQuadraticCoupling_eq_physicalQuadraticCoupling]
  rw [normSq_physicalQuadraticDuhamelCoefficient_eq
    kappa 1 m observed energy term henergy hpositive]
  rw [finiteTimeCollisionKernel_quadratic_eq]
  ring

/-- Complex ordered-pair form of the preceding identity.  This is the exact
summand used by the coherent same-charge and swap-orbit decompositions. -/
theorem physicalQuadraticSameTermPairValue_eq_collisionKernel_mul_actions
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (henergy : ∀ r : Fin 2, 0 ≤ energy (term.1 r))
    (hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    freeQuadraticSameChargePairValue
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time term term =
      ((finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign term) time
          (quadraticCollisionModes observed term) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (term.1 r) : Real) : Complex) := by
  unfold freeQuadraticSameChargePairValue
  rw [Complex.mul_conj]
  norm_cast
  exact
    physicalQuadraticDiagonalTerm_eq_finiteTimeCollisionKernel_mul_actions
      m kappa time observed energy term henergy hpositive

end

end ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge

import ArchonPhysics.FreeFPUTCollisionMismatchBridge
import ArchonPhysics.ThreeWaveCollisionAlgebra

/-!
# Signed three-wave collision flux

The fixed `1 ↔ 2 + 3` flux is the decay sign sector of a slightly more
general finite algebraic bracket.  A quadratic phase term carries one
interaction sign on each input leg.  Its diagonal first-Picard contribution
supplies the product of the two input actions, while the two connected return
placements supply the two observed-input products with precisely those sign
coefficients.

This file records only that real algebra.  It does not assert that the return
trees have already been reindexed, nor does it discard repeated-mode,
coherent, tadpole, or counterrotating sectors.
-/

namespace ArchonPhysics.SignedThreeWaveCollisionFlux

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ThreeWaveCollisionAlgebra

noncomputable section

/-- Collision bracket with independently supplied signs on the two input
legs. -/
def signedThreeWaveCollisionFlux
    (inputSign : Fin 2 → InteractionSign)
    (nObserved nZero nOne : Real) : Real :=
  nZero * nOne +
    (inputSign 0).coefficient * nObserved * nOne +
    (inputSign 1).coefficient * nObserved * nZero

/-- The all-decay input-sign sector is exactly the standard
`n₀ n₁ - nObserved n₀ - nObserved n₁` collision flux. -/
theorem signedThreeWaveCollisionFlux_minus_minus
    (nObserved nZero nOne : Real) :
    signedThreeWaveCollisionFlux (fun _ ↦ .minus)
        nObserved nZero nOne =
      collisionFlux nObserved nZero nOne := by
  unfold signedThreeWaveCollisionFlux collisionFlux
  simp
  ring

/-- Explicit mixed sector with the zero input carrying the plus sign. -/
theorem signedThreeWaveCollisionFlux_plus_minus
    (nObserved nZero nOne : Real) :
    signedThreeWaveCollisionFlux
        (fun r ↦ if r = 0 then .plus else .minus)
        nObserved nZero nOne =
      nZero * nOne + nObserved * nOne - nObserved * nZero := by
  unfold signedThreeWaveCollisionFlux
  simp
  ring

/-- Explicit mixed sector with the one input carrying the plus sign. -/
theorem signedThreeWaveCollisionFlux_minus_plus
    (nObserved nZero nOne : Real) :
    signedThreeWaveCollisionFlux
        (fun r ↦ if r = 0 then .minus else .plus)
        nObserved nZero nOne =
      nZero * nOne - nObserved * nOne + nObserved * nZero := by
  unfold signedThreeWaveCollisionFlux
  simp
  ring

/-- The all-plus, counterrotating algebraic sector. -/
theorem signedThreeWaveCollisionFlux_plus_plus
    (nObserved nZero nOne : Real) :
    signedThreeWaveCollisionFlux (fun _ ↦ .plus)
        nObserved nZero nOne =
      nZero * nOne + nObserved * nOne + nObserved * nZero := by
  unfold signedThreeWaveCollisionFlux
  simp

/-- The signed bracket attached directly to one quadratic phase term. -/
def quadraticSignedCollisionFlux
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N)
    (action : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  signedThreeWaveCollisionFlux (quadraticInputInteractionSign term)
    (action observed) (action (term.1 0)) (action (term.1 1))

/-- A quadratic term whose two initial characters are ordinary phase
characters lies in the standard decay-flux sector. -/
theorem quadraticSignedCollisionFlux_eq_collisionFlux_of_phase_phase
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N)
    (action : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hzero : binaryPhaseSign term.2.1 = .phase)
    (hone : binaryPhaseSign term.2.2 = .phase) :
    quadraticSignedCollisionFlux term action observed =
      collisionFlux (action observed)
        (action (term.1 0)) (action (term.1 1)) := by
  unfold quadraticSignedCollisionFlux signedThreeWaveCollisionFlux
    quadraticInputInteractionSign
  simp [hzero, hone, phaseSignToInputInteractionSign, collisionFlux]
  ring

end

end ArchonPhysics.SignedThreeWaveCollisionFlux

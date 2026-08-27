import ArchonPhysics.PhyslibHamiltonTwoTimeDuhamel

/-!
# Consumer: exact two-time Physlib Hamiltonian Duhamel formula

This endpoint exposes the restart identity on an arbitrary oriented time
interval.  It is derived from the concrete finite Hamilton equations and
does not assume a kinetic closure.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibHamiltonTwoTimeDuhamel

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonTwoTimeDuhamel

noncomputable section

/-- Consumer endpoint for the exact interaction-picture restart formula. -/
theorem problem_physlibHamiltonian_twoTimeDuhamel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (t0 t1 : Real) :
    phaseRenormalize (modeFrequency m k * t1)
        (physlibModeAmplitude m k p q t1) =
      phaseRenormalize (modeFrequency m k * t0)
          (physlibModeAmplitude m k p q t0) +
        ∫ s in t0..t1, physlibModeRotatedSource m kappa beta g k q s := by
  exact interactionPicture_physlibMode_eq_base_add_integral
    m kappa beta g k p q hp hq hHamilton homega t0 t1

#print axioms problem_physlibHamiltonian_twoTimeDuhamel

end

end ArchonPhysicsConsumers.Thermalization.PhyslibHamiltonTwoTimeDuhamel

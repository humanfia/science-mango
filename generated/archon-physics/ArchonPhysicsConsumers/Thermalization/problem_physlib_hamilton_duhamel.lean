import ArchonPhysics.PhyslibHamiltonDuhamel

/-!
# Consumer: actual Physlib Hamilton trajectory to exact modal Duhamel formula
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibHamiltonDuhamel

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibHamiltonDuhamel

noncomputable section

/-- A five-site contract exercising the complete microscopic-to-Duhamel
adapter for one selected positive-frequency mode. -/
theorem fiveSite_physlib_to_exact_modal_duhamel
    (m : Lattice.PositiveMassConfig 5) (kappa beta g : Real)
    (k : Lattice.Site 5)
    (p q : Time → HilbertConfiguration 5)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (t : Real) :
    phaseRenormalize (modeFrequency m k * t)
        (physlibModeAmplitude m k p q t) =
      physlibModeAmplitude m k p q 0 +
        ∫ s in 0..t, physlibModeRotatedSource m kappa beta g k q s := by
  exact interactionPicture_physlibMode_eq_initial_add_integral_of_differentiable
    m kappa beta g k p q hp hq hHamilton homega t

#print axioms fiveSite_physlib_to_exact_modal_duhamel

end

end ArchonPhysicsConsumers.Thermalization.PhyslibHamiltonDuhamel

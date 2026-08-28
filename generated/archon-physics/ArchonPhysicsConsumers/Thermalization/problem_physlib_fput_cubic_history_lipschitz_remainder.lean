import ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder

/-!
# Consumer: cubic-Lipschitz actual FPUT short-block remainder

The actual-minus-free cubic source is controlled by a telescoping estimate
proportional to the real modal-history defect.  Combining that estimate with
the first-Duhamel defect rate makes the complete post-second-Picard
coefficient an explicit `|g|^3` short-block remainder.

This is an unconditional finite-volume statement for differentiable
Physlib Hamiltonian solutions on the supplied energy window.  It does not
assert uniform control on kinetic time or in the thermodynamic limit.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCubicHistoryLipschitzRemainder

open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Consumer-facing coefficient theorem: after extracting the full second
Picard coefficient, the actual microscopic remainder carries `|g|^3` on a
fixed nonnegative short block. -/
theorem actual_physlib_postSecondPicard_cubicLipschitz_abs_cube_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    ‖physlibFPUTAfterSecondPicardRemainderCoefficient
        m kappa beta g observed q radius phase T‖ ≤
      |g| ^ 3 *
        cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
          m mUpper kappa beta g H radius T observed :=
  norm_afterSecondPicardRemainderCoefficient_le_abs_cube_mul_unit
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius phase
      hinitial homega hT hgauge henergy hzeroHistory

#print axioms distinguishedTensorContraction_three_sub_eq_telescoping
#print axioms abs_distinguishedTensorContraction_three_sub_le
#print axioms norm_cubicHistoryRemainder_le_lipschitz_l1_bounds
#print axioms norm_afterSecondPicardRemainderCoefficient_le_abs_cube_mul_unit
#print axioms abs_integral_actualPhaseModalNormSq_sub_initial_le_abs_cube_correction
#print axioms actual_physlib_postSecondPicard_cubicLipschitz_abs_cube_contract

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCubicHistoryLipschitzRemainder

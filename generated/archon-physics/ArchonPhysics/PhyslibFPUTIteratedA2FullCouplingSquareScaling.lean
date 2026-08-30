import ArchonPhysics.CanonicalIIDCoerciveIteratedA2CouplingSquareScaling

/-!
# Coupling-square scaling through the full iterated-A2 coefficient

The two quadratic Hamiltonian vertices supply an exact `kappa ^ 2` factor
not only in the static tree weight, but also in its nested time integral, the
rotated source, the finite phase sum, and the twist-renormalized physical
coefficient.  The initial radius and harmonic mass configuration are held
fixed while `kappa` varies.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2FullCouplingSquareScaling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2CouplingSquareScaling
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

noncomputable section

/-- The complete nested time coefficient inherits the static coupling
square; both mismatch phases are independent of `kappa`. -/
theorem iteratedQuadraticSecondPicardNestedCoefficient_eq_coupling_sq_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardNestedCoefficient
        m kappa radius observed time term =
      ((kappa : Complex) ^ 2) *
        iteratedQuadraticSecondPicardNestedCoefficient
          m 1 radius observed time term := by
  unfold iteratedQuadraticSecondPicardNestedCoefficient
  rw [
    iteratedQuadraticSecondPicardStaticCoefficient_eq_coupling_sq_mul_unit]
  ring

/-- The unintegrated rotated coefficient of every complete tree scales by
the same exact square. -/
theorem
    iteratedQuadraticSecondPicardRotatedTimeCoefficient_eq_coupling_sq_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (time : Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardRotatedTimeCoefficient
        m kappa radius time observed term =
      ((kappa : Complex) ^ 2) *
        iteratedQuadraticSecondPicardRotatedTimeCoefficient
          m 1 radius time observed term := by
  rw [
    iteratedQuadraticSecondPicardRotatedTimeCoefficient_eq_timeResolved,
    iteratedQuadraticSecondPicardRotatedTimeCoefficient_eq_timeResolved,
    iteratedQuadraticSecondPicardStaticCoefficient_eq_coupling_sq_mul_unit]
  ring

/-- The complete physical quadratic second-Picard rotated source scales by
`kappa ^ 2`, after summing every finite phase character. -/
theorem physlibQuadraticSecondPicardRotatedSource_eq_coupling_sq_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibQuadraticSecondPicardRotatedSource
        m kappa observed radius phase time =
      ((kappa : Complex) ^ 2) *
        physlibQuadraticSecondPicardRotatedSource
          m 1 observed radius phase time := by
  rw [
    physlibQuadraticSecondPicardRotatedSource_eq_characterFamily,
    physlibQuadraticSecondPicardRotatedSource_eq_characterFamily]
  unfold finitePhaseCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term _hterm
  rw [
    iteratedQuadraticSecondPicardRotatedTimeCoefficient_eq_coupling_sq_mul_unit]
  ring

/-- The integrated physical iterated-quadratic P3/A2 coefficient carries the
same exact square. -/
theorem
    physlibIteratedQuadraticSecondPicardCoefficient_eq_coupling_sq_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibIteratedQuadraticSecondPicardCoefficient
        m kappa radius phase time observed =
      ((kappa : Complex) ^ 2) *
        physlibIteratedQuadraticSecondPicardCoefficient
          m 1 radius phase time observed := by
  rw [
    physlibIteratedQuadraticSecondPicardCoefficient_eq_characterFamily,
    physlibIteratedQuadraticSecondPicardCoefficient_eq_characterFamily]
  unfold finitePhaseCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term _hterm
  rw [
    iteratedQuadraticSecondPicardNestedCoefficient_eq_coupling_sq_mul_unit]
  ring

/-- Pointwise scaling of the actual integrated physical A2 tree. -/
theorem physicalIteratedA2Coefficient_eq_coupling_sq_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2Coefficient m kappa radius observed time term =
      ((kappa : Complex) ^ 2) *
        physicalIteratedA2Coefficient m 1 radius observed time term := by
  exact
    iteratedQuadraticSecondPicardNestedCoefficient_eq_coupling_sq_mul_unit
      m kappa radius observed time term

/-- Twist renormalization is linear, so it preserves the exact coupling
square of the full physical coefficient. -/
theorem phaseRenormalizedPhysicalIteratedA2Coefficient_eq_coupling_sq_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    phaseRenormalizedPhysicalIteratedA2Coefficient
        m kappa radius observed time term =
      ((kappa : Complex) ^ 2) *
        phaseRenormalizedPhysicalIteratedA2Coefficient
          m 1 radius observed time term := by
  unfold phaseRenormalizedPhysicalIteratedA2Coefficient
    twistRenormalizedIteratedA2Coefficient
  rw [physicalIteratedA2Coefficient_eq_coupling_sq_mul_unit
    m kappa radius observed time term]
  rw [physicalIteratedA2Coefficient_eq_coupling_sq_mul_unit
    m kappa radius observed time
      (flipIteratedQuadraticInnerBranch term)]
  ring

end

end ArchonPhysics.PhyslibFPUTIteratedA2FullCouplingSquareScaling

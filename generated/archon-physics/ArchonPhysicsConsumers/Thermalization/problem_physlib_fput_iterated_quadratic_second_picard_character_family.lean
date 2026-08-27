import ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

/-!
# Consumer: iterated-quadratic second-Picard character tree

This consumer exposes the exact finite tree obtained by placing the physical
first-Picard coordinate in either ordered input slot of the outer quadratic
tensor.  Each tree retains the sign of the opposite free coordinate and the
positive/conjugate branch of the inner first-Picard family.  The integrated
endpoint uses the corresponding two-layer oscillatory integral.  All claims
are finite-volume algebraic identities.
-/

namespace ArchonPhysicsConsumers.Thermalization

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

noncomputable section

/-- Consumer endpoint for the time-resolved normal form of one complete
`(outer modes, Q1 slot, free sign, inner entry)` tree. -/
theorem problem_iteratedQuadraticSecondPicard_termwiseTimeResolved
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardRotatedTimeCoefficient
        m kappa radius time observed term =
      iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term *
        Complex.exp
          ((Complex.I *
            (iteratedQuadraticOuterMismatch m observed term : Real)) * time) *
        oscillatoryIntegral
          (iteratedQuadraticInnerMismatch m term) time :=
  iteratedQuadraticSecondPicardRotatedTimeCoefficient_eq_timeResolved
    m kappa radius time observed term

/-- Consumer endpoint for the exact pointwise finite-character expansion of
the iterated-quadratic P3 source. -/
theorem problem_physlibQuadraticSecondPicardRotatedSource_exactCharacterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibQuadraticSecondPicardRotatedSource
        m kappa observed radius phase time =
      finitePhaseCorrection
        (iteratedQuadraticSecondPicardRotatedTimeCoefficient
          m kappa radius time observed)
        iteratedQuadraticSecondPicardCharge phase :=
  physlibQuadraticSecondPicardRotatedSource_eq_characterFamily
    m kappa radius phase time observed

/-- An inner zero-frequency mode kills the corresponding tree coefficient
through the physical interaction tensor. -/
theorem problem_iteratedQuadraticSecondPicard_innerZeroDecoupling
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hzero : modeFrequency m (iteratedQuadraticFirstPicardMode term) = 0) :
    iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term = 0 :=
  iteratedQuadraticSecondPicardStaticCoefficient_eq_zero_of_innerFrequency_eq_zero
    m kappa radius observed term hzero

/-- Consumer endpoint for the integrated nested character family of the
iterated-quadratic P3 `A2` component. -/
theorem problem_physlibIteratedQuadraticSecondPicard_exactNestedFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibIteratedQuadraticSecondPicardCoefficient
        m kappa radius phase time observed =
      finitePhaseCorrection
        (iteratedQuadraticSecondPicardNestedCoefficient
          m kappa radius observed time)
        iteratedQuadraticSecondPicardCharge phase :=
  physlibIteratedQuadraticSecondPicardCoefficient_eq_characterFamily
    m kappa radius phase time observed

/-- At a zero-frequency observed mode the integrated family vanishes by the
physical second-Picard decoupling theorem. -/
theorem problem_physlibIteratedQuadraticSecondPicard_observedZeroDecoupling
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N)
    (hzero : modeFrequency m observed = 0) :
    physlibIteratedQuadraticSecondPicardCoefficient
        m kappa radius phase time observed = 0 :=
  physlibIteratedQuadraticSecondPicardCoefficient_eq_zero_of_modeFrequency_eq_zero
    m kappa radius phase time observed hzero

#print axioms
  problem_iteratedQuadraticSecondPicard_termwiseTimeResolved
#print axioms
  problem_physlibQuadraticSecondPicardRotatedSource_exactCharacterFamily
#print axioms
  problem_iteratedQuadraticSecondPicard_innerZeroDecoupling
#print axioms
  problem_physlibIteratedQuadraticSecondPicard_exactNestedFamily
#print axioms
  problem_physlibIteratedQuadraticSecondPicard_observedZeroDecoupling

end

end ArchonPhysicsConsumers.Thermalization

import ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily

/-!
# Consumer: exact character family of the Physlib first-Picard coordinate

This consumer exposes the finite `J1` oscillatory family and its exact real
modal-coordinate reconstruction.  The latter retains both the positive and
conjugate branches and all repeated-charge terms.  No terms are grouped or
discarded, and no collision or kinetic interpretation is asserted.
-/

namespace ArchonPhysicsConsumers.Thermalization

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open scoped ComplexConjugate

noncomputable section

/-- Consumer endpoint for the physical `J1` coefficient as the existing
finite oscillatory `QuadraticPhaseTerm` family. -/
theorem problem_physlibQuadraticFirstPicardCoefficient_exactCharacterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (observed : Lattice.Site N) :
    physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time observed =
      finiteHaarOscillatorySum
        (freeQuadraticDuhamelCoefficient
          (physlibQuadraticCoupling m kappa 1 observed)
          m observed radius)
        quadraticPhaseCharge
        (quadraticPhaseMismatch (modeFrequency m) observed)
        time phase :=
  physlibQuadraticFirstPicardCoefficient_eq_finiteHaarOscillatorySum
    m kappa radius phase time observed

/-- The positive branch has the exact `1/2`, coordinate scale, rotated
coefficient, and original charge. -/
theorem problem_physlibQuadraticFirstPicardCoordinate_positiveBranch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (hpositive : 0 < modeFrequency m observed) :
    physlibQuadraticFirstPicardCoordinateCharacterCoefficient
        m kappa radius time observed (term, 0) =
      (((((Real.sqrt (2 * modeFrequency m observed) /
          modeFrequency m observed) / 2 : Real)) : Complex) *
        physlibQuadraticFirstPicardRotatedTermCoefficient
          m kappa radius time observed term) ∧
    physlibQuadraticFirstPicardCoordinateCharacterCharge (term, 0) =
      quadraticPhaseCharge term := by
  constructor
  · simpa [physlibQuadraticFirstPicardCoordinateScale] using
      physlibQuadraticFirstPicardCoordinateCharacterCoefficient_zero
        m kappa radius time observed term hpositive
  · exact physlibQuadraticFirstPicardCoordinateCharacterCharge_zero term

/-- The conjugate branch has the same exact scale, the conjugate rotated
coefficient, and negated charge. -/
theorem problem_physlibQuadraticFirstPicardCoordinate_conjugateBranch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (hpositive : 0 < modeFrequency m observed) :
    physlibQuadraticFirstPicardCoordinateCharacterCoefficient
        m kappa radius time observed (term, 1) =
      (((((Real.sqrt (2 * modeFrequency m observed) /
          modeFrequency m observed) / 2 : Real)) : Complex) *
        starRingEnd Complex
          (physlibQuadraticFirstPicardRotatedTermCoefficient
            m kappa radius time observed term)) ∧
    physlibQuadraticFirstPicardCoordinateCharacterCharge (term, 1) =
      -quadraticPhaseCharge term := by
  constructor
  · simpa [physlibQuadraticFirstPicardCoordinateScale] using
      physlibQuadraticFirstPicardCoordinateCharacterCoefficient_one
        m kappa radius time observed term hpositive
  · exact physlibQuadraticFirstPicardCoordinateCharacterCharge_one term

/-- Consumer endpoint for the global real modal-coordinate family.  It also
covers a zero-frequency observed mode through the tensor-decoupled P3
endpoint, rather than through a division argument. -/
theorem problem_physlibQuadraticFirstPicardModalHistory_exactCharacterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (observed : Lattice.Site N) :
    ((physlibQuadraticFirstPicardModalHistory
        m kappa radius phase time observed : Real) : Complex) =
      physlibQuadraticFirstPicardCoordinateCharacterFamily
        m kappa radius time observed phase :=
  coe_physlibQuadraticFirstPicardModalHistory_eq_characterFamily
    m kappa radius phase time observed

/-- Explicit zero-frequency consumer endpoint for the character family. -/
theorem problem_physlibQuadraticFirstPicardCoordinateCharacterFamily_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (observed : Lattice.Site N)
    (hzero : modeFrequency m observed = 0) :
    physlibQuadraticFirstPicardCoordinateCharacterFamily
      m kappa radius time observed phase = 0 :=
  physlibQuadraticFirstPicardCoordinateCharacterFamily_eq_zero_of_modeFrequency_eq_zero
    m kappa radius phase time observed hzero

#print axioms
  ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily.coe_scaled_re_finitePhaseCorrection_eq_twoBranch
#print axioms
  ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily.physlibQuadraticFirstPicardCoefficient_eq_finiteHaarOscillatorySum
#print axioms
  ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily.coe_physlibQuadraticFirstPicardModalHistory_eq_characterFamily
#print axioms problem_physlibQuadraticFirstPicardCoefficient_exactCharacterFamily
#print axioms problem_physlibQuadraticFirstPicardCoordinate_positiveBranch
#print axioms problem_physlibQuadraticFirstPicardCoordinate_conjugateBranch
#print axioms problem_physlibQuadraticFirstPicardModalHistory_exactCharacterFamily
#print axioms problem_physlibQuadraticFirstPicardCoordinateCharacterFamily_zero

end

end ArchonPhysicsConsumers.Thermalization

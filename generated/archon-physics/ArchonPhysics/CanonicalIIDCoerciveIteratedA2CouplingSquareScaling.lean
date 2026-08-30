import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay

/-!
# Exact coupling-square scaling of an actual iterated-A2 channel

The quadratic FPUT interaction enters both vertices of an iterated
second-Picard tree.  This module records the resulting exact square in the
physical static coefficient and carries it through the iid expectation.

The radius profile is held fixed as the coupling varies.  No dynamical claim
about a coupling-dependent initial ensemble or nonlinear trajectory is made.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2CouplingSquareScaling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open MeasureTheory

noncomputable section

/-- A real force amplitude can be pulled out of the complex mode source. -/
theorem forcedModeSource_neg_coupling_eq_mul_unit
    (omega coupling : Real) :
    forcedModeSource omega (-coupling) =
      (coupling : Complex) * forcedModeSource omega (-1) := by
  unfold forcedModeSource
  push_cast
  ring

/-- The physical quadratic coupling is linear in `kappa` when its auxiliary
coupling argument is fixed to one. -/
theorem physlibQuadraticCoupling_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (observed : Lattice.Site N) :
    physlibQuadraticCoupling m kappa 1 observed =
      (kappa : Complex) * physlibQuadraticCoupling m 1 1 observed := by
  unfold physlibQuadraticCoupling
  simp only [mul_one]
  exact forcedModeSource_neg_coupling_eq_mul_unit
    (modeFrequency m observed) kappa

/-- Every inner first-Picard coordinate branch is linear in `kappa`. -/
theorem firstPicardCoordinateBranchStaticCoefficient_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved entry =
      (kappa : Complex) *
        firstPicardCoordinateBranchStaticCoefficient
          m 1 radius innerObserved entry := by
  unfold firstPicardCoordinateBranchStaticCoefficient
  by_cases hpositive : 0 < modeFrequency m innerObserved
  · rw [if_pos hpositive, if_pos hpositive]
    by_cases hbranch : entry.2 = 0
    · rw [if_pos hbranch, if_pos hbranch]
      rw [physlibQuadraticCoupling_eq_coupling_mul_unit]
      unfold freeQuadraticDuhamelCoefficient
      ring
    · rw [if_neg hbranch, if_neg hbranch]
      rw [physlibQuadraticCoupling_eq_coupling_mul_unit]
      unfold freeQuadraticDuhamelCoefficient
      simp only [map_mul, Complex.conj_ofReal]
      ring
  · rw [if_neg hpositive, if_neg hpositive]
    ring

/-- The two quadratic vertices give an exact `kappa ^ 2` factor. -/
theorem iteratedQuadraticSecondPicardStaticCoefficient_eq_coupling_sq_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term =
      ((kappa : Complex) ^ 2) *
        iteratedQuadraticSecondPicardStaticCoefficient
          m 1 radius observed term := by
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  by_cases hpositive : 0 < modeFrequency m observed
  · rw [if_pos hpositive, if_pos hpositive]
    unfold physlibIteratedQuadraticOuterCoupling
    rw [forcedModeSource_neg_coupling_eq_mul_unit]
    rw [firstPicardCoordinateBranchStaticCoefficient_eq_coupling_mul_unit]
    ring
  · rw [if_neg hpositive, if_neg hpositive]
    ring

/-- Pointwise iid static weights inherit the exact coupling square. -/
theorem actualIteratedA2StaticWeightSample_eq_coupling_sq_mul_unit
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (sample : Omega) :
    actualIteratedA2StaticWeightSample ensemble kappa radius observed term
        sample =
      ((kappa : Complex) ^ 2) *
        actualIteratedA2StaticWeightSample ensemble 1 radius observed term
          sample := by
  exact iteratedQuadraticSecondPicardStaticCoefficient_eq_coupling_sq_mul_unit
    (ensemble.restrictPositiveMass (N := N) sample) kappa
      (radius sample) observed term

/-- The exact coupling square passes through the weighted mismatch
expectation. -/
theorem actualIteratedA2StaticWeightedChannelExpectation_eq_coupling_sq_mul_unit
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (time : Real) :
    actualIteratedA2StaticWeightedChannelExpectation ensemble channel kappa
        radius observed term time =
      ((kappa : Complex) ^ 2) *
        actualIteratedA2StaticWeightedChannelExpectation ensemble channel 1
          radius observed term time := by
  unfold actualIteratedA2StaticWeightedChannelExpectation
    actualIteratedA2WeightedChannelExpectation weightedMismatchExpectation
  rw [show (fun sample =>
      Complex.exp
          (Complex.I *
            ((time * actualIteratedA2MismatchSample ensemble channel observed
              term sample : Real) : Complex)) *
        actualIteratedA2StaticWeightSample ensemble kappa radius observed term
          sample) =
      (fun sample => ((kappa : Complex) ^ 2) *
        (Complex.exp
            (Complex.I *
              ((time * actualIteratedA2MismatchSample ensemble channel observed
                term sample : Real) : Complex)) *
          actualIteratedA2StaticWeightSample ensemble 1 radius observed term
            sample)) by
    funext sample
    rw [actualIteratedA2StaticWeightSample_eq_coupling_sq_mul_unit]
    ring]
  rw [integral_const_mul]

end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2CouplingSquareScaling

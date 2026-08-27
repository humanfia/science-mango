import ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

/-!
# Consumer: exact second-Picard extraction from a true Physlib trajectory

The endpoints below retain the actual-history cross remainder, the quadratic
defect square, the actual-minus-free cubic remainder, and all higher terms of
the finite squared-amplitude polynomial.  They make no RPA or kinetic
assumption and do not identify the finite polynomial with a collision
operator.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTSecondPicardHistoryBridge

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open scoped ComplexConjugate

noncomputable section

/-- Consumer endpoint for the positive-frequency inverse from an
interaction-picture correction to its real modal coordinate. -/
theorem problem_positiveFrequencyInteractionPictureCoordinate_exact
    {omega Q P time : Real} (homega : 0 < omega) :
    interactionPictureCorrectionCoordinate omega time
        (phaseRenormalize (omega * time)
          (complexModeAmplitude omega Q P)) = Q := by
  exact
    interactionPictureCorrectionCoordinate_phaseRenormalize_complexModeAmplitude
      homega

/-- Consumer endpoint: at a zero-frequency observed mode, `A1`, reconstructed
`Q1`, and the complete extracted `A2` all decouple. -/
theorem problem_zeroFrequencyPicardCoefficients_exact
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (hzero : modeFrequency m observed = 0) :
    physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time observed = 0 ∧
      physlibQuadraticFirstPicardModalHistory
          m kappa radius phase time observed = 0 ∧
      physlibFPUTSecondPicardCoefficient
          m kappa beta observed radius phase time = 0 := by
  exact ⟨
    physlibQuadraticFirstPicardCoefficient_eq_zero_of_modeFrequency_eq_zero
      m kappa radius phase time observed hzero,
    physlibQuadraticFirstPicardModalHistory_eq_zero_of_modeFrequency_eq_zero
      m kappa radius phase time observed hzero,
    physlibFPUTSecondPicardCoefficient_eq_zero_of_modeFrequency_eq_zero
      m kappa beta observed radius phase time hzero⟩

/-- Consumer endpoint: complete true history source equals `g^2 A2` plus
all three explicit source remainders. -/
theorem problem_trueHistorySource_exact_secondPicard_split
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibQuadraticHistoryDifference
          m kappa g observed q radius phase time +
        physlibCubicRotatedSource m beta g observed q time =
      ((g ^ 2 : Real) : Complex) *
          physlibFPUTSecondPicardRotatedSource
            m kappa beta observed radius phase time +
        physlibFPUTAfterSecondPicardRemainderRotatedSource
          m kappa beta g observed q radius phase time := by
  exact physlibFPUTTrueHistorySource_eq_secondPicard_add_remainder
    m kappa beta g observed q radius phase time

/-- Consumer endpoint: the second-order squared-amplitude coefficient contains
both the first-correction square and the initial/second-correction
interference. -/
theorem problem_secondPicardSecondMomentCoefficient_exact
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (A0 : Complex) :
    twoStepSecondCoefficient A0
        (physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time observed)
        (physlibFPUTSecondPicardCoefficient
          m kappa beta observed radius phase time) =
      Complex.normSq
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed) +
        2 * (A0 * conj (physlibFPUTSecondPicardCoefficient
          m kappa beta observed radius phase time)).re := by
  exact physlibFPUT_secondMomentSecondCoefficient_eq_normSq_add_interference
    m kappa beta observed radius phase time A0

/-- Consumer endpoint for the genuine harmonic modal-energy coefficient. -/
theorem problem_secondPicardModalEnergyCoefficient_exact
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (A0 : Complex) :
    modeFrequency m observed *
        twoStepSecondCoefficient A0
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time) =
      modeFrequency m observed *
        (Complex.normSq
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed) +
          2 * (A0 * conj (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time)).re) := by
  exact
    physlibFPUT_modalEnergySecondCoefficient_eq_frequency_mul_normSq_add_interference
      m kappa beta observed radius phase time A0

/-- Consumer endpoint for a true Hamilton trajectory: the exact amplitude is
the two-step Picard amplitude plus the integrated equality remainder. -/
theorem problem_trueInteractionPicture_exact_twoStep_with_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m observed)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    phaseRenormalize (modeFrequency m observed * time)
        (physlibModeAmplitude m observed p q time) =
      twoStepPerturbedAmplitude g
          (physlibModeAmplitude m observed p q 0)
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time) +
        physlibFPUTAfterSecondPicardRemainderCoefficient
          m kappa beta g observed q radius phase time := by
  exact interactionPicture_physlibMode_eq_twoStep_add_remainder
    m kappa beta g observed p q hp hq hHamilton homega radius phase time

/-- Consumer endpoint: exact true squared amplitude with every two-step term,
the truncation--remainder interference, and the remainder square retained. -/
theorem problem_trueInteractionPictureSecondMoment_exact_with_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m observed)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    Complex.normSq
        (phaseRenormalize (modeFrequency m observed * time)
          (physlibModeAmplitude m observed p q time)) =
      secondMomentZeroth (physlibModeAmplitude m observed p q 0) +
        g * secondMomentFirst (physlibModeAmplitude m observed p q 0)
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed) +
        g ^ 2 * twoStepSecondCoefficient
          (physlibModeAmplitude m observed p q 0)
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time) +
        g ^ 3 * twoStepThirdCoefficient
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time) +
        g ^ 4 * twoStepFourthCoefficient
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time) +
        secondMomentFirst
          (twoStepPerturbedAmplitude g
            (physlibModeAmplitude m observed p q 0)
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed)
            (physlibFPUTSecondPicardCoefficient
              m kappa beta observed radius phase time))
          (physlibFPUTAfterSecondPicardRemainderCoefficient
            m kappa beta g observed q radius phase time) +
        secondMomentSecond
          (physlibFPUTAfterSecondPicardRemainderCoefficient
            m kappa beta g observed q radius phase time) := by
  exact
    normSq_interactionPicture_physlibMode_eq_twoStepPolynomial_add_remainder
      m kappa beta g observed p q hp hq hHamilton homega radius phase time

/-- Consumer endpoint: the same exact identity for the physical harmonic
modal energy `omega * normSq`. -/
theorem problem_truePhysicalModalEnergy_exact_with_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m observed)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    modalEnergy (modeFrequencySq m observed)
        (physlibModePosition m observed q time)
        (physlibModeMomentum m observed p time) =
      modeFrequency m observed *
        (secondMomentZeroth (physlibModeAmplitude m observed p q 0) +
          g * secondMomentFirst (physlibModeAmplitude m observed p q 0)
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed) +
          g ^ 2 * twoStepSecondCoefficient
            (physlibModeAmplitude m observed p q 0)
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed)
            (physlibFPUTSecondPicardCoefficient
              m kappa beta observed radius phase time) +
          g ^ 3 * twoStepThirdCoefficient
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed)
            (physlibFPUTSecondPicardCoefficient
              m kappa beta observed radius phase time) +
          g ^ 4 * twoStepFourthCoefficient
            (physlibFPUTSecondPicardCoefficient
              m kappa beta observed radius phase time) +
          secondMomentFirst
            (twoStepPerturbedAmplitude g
              (physlibModeAmplitude m observed p q 0)
              (physlibQuadraticFirstPicardCoefficient
                m kappa radius phase time observed)
              (physlibFPUTSecondPicardCoefficient
                m kappa beta observed radius phase time))
            (physlibFPUTAfterSecondPicardRemainderCoefficient
              m kappa beta g observed q radius phase time) +
          secondMomentSecond
            (physlibFPUTAfterSecondPicardRemainderCoefficient
              m kappa beta g observed q radius phase time)) := by
  exact modalEnergy_physlibMode_eq_frequency_mul_twoStepPolynomial_add_remainder
    m kappa beta g observed p q hp hq hHamilton homega radius phase time

#print axioms problem_trueHistorySource_exact_secondPicard_split
#print axioms problem_positiveFrequencyInteractionPictureCoordinate_exact
#print axioms problem_zeroFrequencyPicardCoefficients_exact
#print axioms problem_secondPicardSecondMomentCoefficient_exact
#print axioms problem_secondPicardModalEnergyCoefficient_exact
#print axioms problem_trueInteractionPicture_exact_twoStep_with_remainder
#print axioms problem_trueInteractionPictureSecondMoment_exact_with_remainder
#print axioms problem_truePhysicalModalEnergy_exact_with_remainder

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTSecondPicardHistoryBridge

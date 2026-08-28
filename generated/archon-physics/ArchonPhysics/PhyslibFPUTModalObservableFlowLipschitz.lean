import ArchonPhysics.ComplexModeAmplitude
import ArchonPhysics.PhyslibFPUTEnergyShellFlowLipschitz
import ArchonPhysics.ReducedModeTransform

/-!
# Lipschitz physical modal amplitudes along the canonical FPUT flow

For a fixed positive mass realization and a selected normal mode, the
physical complex amplitude is a continuous real-linear observable of the
full parameter--phase state.  Consequently its composition with the
canonical energy-shell Hamiltonian flow is Lipschitz at every fixed time.

The mass used by the observable is fixed.  Thus this result does not make a
continuity claim for a realization-dependent eigenbasis as the mass varies;
it is precisely the fixed-realization statement used inside one coupled
FPUT block.
-/

namespace ArchonPhysics.PhyslibFPUTModalObservableFlowLipschitz

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhyslibFPUTEnergyShellFlowLipschitz
open ArchonPhysics.ReducedModeTransform

noncomputable section

variable {N : Nat} [NeZero N]

/-- Position projection from the common parameter--phase space. -/
def parametricPhasePositionCLM :
    ParametricPhaseSpace N →L[Real] HilbertConfiguration N :=
  (ContinuousLinearMap.fst Real
      (HilbertConfiguration N) (HilbertConfiguration N)).comp
    (ContinuousLinearMap.snd Real
      (HamiltonParameterSpace N)
      (HilbertConfiguration N × HilbertConfiguration N))

/-- Momentum projection from the common parameter--phase space. -/
def parametricPhaseMomentumCLM :
    ParametricPhaseSpace N →L[Real] HilbertConfiguration N :=
  (ContinuousLinearMap.snd Real
      (HilbertConfiguration N) (HilbertConfiguration N)).comp
    (ContinuousLinearMap.snd Real
      (HamiltonParameterSpace N)
      (HilbertConfiguration N × HilbertConfiguration N))

/-- Fixed-mass, selected-mode mass-weighted position coordinate. -/
def fixedMassModalPositionCoordinateCLM
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N) :
    ParametricPhaseSpace N →L[Real] Real :=
  (EuclideanSpace.proj observed).comp
    ((modalCoordinates m).toContinuousLinearMap.comp
      ((sqrtMassTransform m).comp parametricPhasePositionCLM))

/-- Fixed-mass, selected-mode mass-weighted momentum coordinate. -/
def fixedMassModalMomentumCoordinateCLM
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N) :
    ParametricPhaseSpace N →L[Real] Real :=
  (EuclideanSpace.proj observed).comp
    ((modalCoordinates m).toContinuousLinearMap.comp
      ((inverseSqrtMassTransform m).comp parametricPhaseMomentumCLM))

/-- The genuine positive-frequency complex modal amplitude, bundled as a
continuous real-linear observable on the full parameter--phase state. -/
def fixedMassSelectedModeAmplitudeCLM
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N) :
    ParametricPhaseSpace N →L[Real] Complex :=
  (Real.sqrt (2 * modeFrequency m observed))⁻¹ •
    ((fixedMassModalPositionCoordinateCLM m observed).smulRight
        (modeFrequency m observed : Complex) +
      (fixedMassModalMomentumCoordinateCLM m observed).smulRight Complex.I)

/-- Function-valued name for the selected physical amplitude. -/
def fixedMassSelectedModeAmplitude
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N) :
    ParametricPhaseSpace N → Complex :=
  fixedMassSelectedModeAmplitudeCLM m observed

/-- Lipschitz constant used for this fixed-mass initial observable in a
full-state endpoint certificate. -/
def fixedMassSelectedModeAmplitudeAmplification
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N) : NNReal :=
  ‖fixedMassSelectedModeAmplitudeCLM m observed‖₊

/-- The observable has exactly the standard physical complex-amplitude
formula in mass-weighted normal coordinates. -/
theorem fixedMassSelectedModeAmplitude_eq
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (x : ParametricPhaseSpace N) :
    fixedMassSelectedModeAmplitude m observed x =
      complexModeAmplitude (modeFrequency m observed)
        (modalCoordinates m (sqrtMassTransform m x.2.1) observed)
        (modalCoordinates m (inverseSqrtMassTransform m x.2.2) observed) := by
  unfold fixedMassSelectedModeAmplitude fixedMassSelectedModeAmplitudeCLM
    fixedMassModalPositionCoordinateCLM
    fixedMassModalMomentumCoordinateCLM
    parametricPhasePositionCLM parametricPhaseMomentumCLM
    complexModeAmplitude
  change (Real.sqrt (2 * modeFrequency m observed))⁻¹ •
      ((modalCoordinates m (sqrtMassTransform m x.2.1) observed) •
          (modeFrequency m observed : Complex) +
        (modalCoordinates m (inverseSqrtMassTransform m x.2.2) observed) •
          Complex.I) = _
  simp only [RCLike.real_smul_eq_coe_mul]
  push_cast
  rw [div_eq_mul_inv]
  simp only [mul_comm]
  exact mul_comm _ _

/-- The selected physical modal amplitude is globally Lipschitz, with its
honest continuous-linear operator norm as the constant. -/
theorem fixedMassSelectedModeAmplitude_lipschitz
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N) :
    LipschitzWith (fixedMassSelectedModeAmplitudeAmplification m observed)
      (fixedMassSelectedModeAmplitude m observed) := by
  exact (fixedMassSelectedModeAmplitudeCLM m observed).lipschitz

/-- At positive frequency, the observable carries exactly the physical
harmonic energy of the selected mode. -/
theorem fixedMassSelectedModeAmplitude_energy
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed)
    (x : ParametricPhaseSpace N) :
    modeFrequency m observed *
        Complex.normSq (fixedMassSelectedModeAmplitude m observed x) =
      HarmonicModes.modalEnergy (modeFrequencySq m observed)
        (modalCoordinates m (sqrtMassTransform m x.2.1) observed)
        (modalCoordinates m (inverseSqrtMassTransform m x.2.2) observed) := by
  rw [fixedMassSelectedModeAmplitude_eq]
  exact latticeModeAmplitude_energy m observed _ _ homega

/-- Physical observed amplitude after one canonical Hamiltonian block. -/
def canonicalFixedMassSelectedModeAmplitudeAfter
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) : ParametricPhaseSpace N → Complex :=
  fun x ↦ fixedMassSelectedModeAmplitude m observed
    (canonicalRandomMassGlobalFlow shell (x, t))

/-- Lipschitz constant used for the actual one-block observable in a
full-state endpoint certificate. -/
def canonicalFixedMassSelectedModeAmplitudeAfterAmplification
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) : NNReal :=
  fixedMassSelectedModeAmplitudeAmplification m observed *
    energyShellFlowAmplification shell t

@[simp] theorem canonicalFixedMassSelectedModeAmplitudeAfter_apply
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) (x : ParametricPhaseSpace N) :
    canonicalFixedMassSelectedModeAmplitudeAfter shell m observed t x =
      complexModeAmplitude (modeFrequency m observed)
        (modalCoordinates m
          (sqrtMassTransform m
            (canonicalRandomMassGlobalFlow shell (x, t)).2.1) observed)
        (modalCoordinates m
          (inverseSqrtMassTransform m
            (canonicalRandomMassGlobalFlow shell (x, t)).2.2) observed) := by
  exact fixedMassSelectedModeAmplitude_eq m observed _

/-- The actual one-block modal observable is Lipschitz.  Its constant is the
product of the observable operator norm and the true energy-shell flow's
two-sided Grönwall amplification. -/
theorem canonicalFixedMassSelectedModeAmplitudeAfter_lipschitz
    (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) :
    LipschitzWith
      (canonicalFixedMassSelectedModeAmplitudeAfterAmplification
        shell m observed t)
      (canonicalFixedMassSelectedModeAmplitudeAfter shell m observed t) := by
  exact (fixedMassSelectedModeAmplitude_lipschitz m observed).comp
    (canonicalRandomMassGlobalFlow_lipschitz_fixedTime shell t)

end

end ArchonPhysics.PhyslibFPUTModalObservableFlowLipschitz

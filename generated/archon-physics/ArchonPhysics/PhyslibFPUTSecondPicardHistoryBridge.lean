import ArchonPhysics.QuadraticTensorHistoryExpansion
import ArchonPhysics.DuhamelTwoStepMomentAlgebra
import ArchonPhysics.FiniteSecondOrderPhaseExpansion
import ArchonPhysics.FrozenCollisionMassPositivity

/-!
# Exact second-Picard extraction from the Physlib FPUT history defect

For the cubic-leading FPUT scaling, the quadratic force is proportional to
`g` and the cubic force to `g^2`.  This module defines the coefficient `A1`
by evaluating the unit-`g` quadratic force on the free orbit.  Its associated
real modal-coordinate correction is inserted once into the polarized
quadratic tensor source, producing the quadratic part of `A2`; the free cubic
source supplies the other part of `A2`.

For a true Physlib Hamiltonian trajectory the actual modal-history defect is
split *identically* as `g • Q1 + remainder`.  Consequently its linear cross
source is `g^2` times the quadratic `A2` source plus an explicit remainder.
The defect-square term and the difference between the actual and free cubic
sources are retained as well.  No RPA, decorrelation, smallness, or limiting
assumption is used.
-/

namespace ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FrozenCollisionMassPositivity
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.ReducedModeTransform
open scoped ComplexConjugate

noncomputable section

/-! ## Bilinearity of the polarized order-two contraction -/

/-- The cross contraction is additive in its defect argument. -/
theorem quadraticTensorCrossContraction_add_right
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (base left right : WeightedConfiguration N) :
    quadraticTensorCrossContraction m observed base (left + right) =
      quadraticTensorCrossContraction m observed base left +
        quadraticTensorCrossContraction m observed base right := by
  classical
  unfold quadraticTensorCrossContraction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro modes hmodes
  simp only [WithLp.ofLp_add, Pi.add_apply]
  ring

/-- A real scalar in the defect pulls out of the cross contraction. -/
theorem quadraticTensorCrossContraction_smul_right
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (base defect : WeightedConfiguration N) (scale : Real) :
    quadraticTensorCrossContraction m observed base (scale • defect) =
      scale * quadraticTensorCrossContraction m observed base defect := by
  classical
  unfold quadraticTensorCrossContraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro modes hmodes
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- A tensor with a zero-frequency observed leg vanishes before any modal
amplitudes are inserted. -/
theorem interactionTensor_cons_eq_zero_of_observedFrequency_eq_zero
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (modes : Fin n → Lattice.Site N)
    (hzero : modeFrequency m observed = 0) :
    interactionTensor m (n + 1) (Fin.cons observed modes) = 0 := by
  exact interactionTensor_eq_zero_of_modeFrequency_eq_zero
    m (Fin.cons observed modes) 0 hzero

/-- A tensor with any zero-frequency input leg vanishes. -/
theorem interactionTensor_cons_eq_zero_of_inputFrequency_eq_zero
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (modes : Fin n → Lattice.Site N) (input : Fin n)
    (hzero : modeFrequency m (modes input) = 0) :
    interactionTensor m (n + 1) (Fin.cons observed modes) = 0 := by
  exact interactionTensor_eq_zero_of_modeFrequency_eq_zero
    m (Fin.cons observed modes) input.succ (by simpa)

/-- Therefore every individual quadratic or cubic Picard summand carrying a
zero-frequency input leg is zero, independently of its amplitude factor. -/
theorem interactionTensor_cons_mul_eq_zero_of_inputFrequency_eq_zero
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (modes : Fin n → Lattice.Site N) (input : Fin n)
    (hzero : modeFrequency m (modes input) = 0) (amplitudeFactor : Real) :
    interactionTensor m (n + 1) (Fin.cons observed modes) *
        amplitudeFactor = 0 := by
  rw [interactionTensor_cons_eq_zero_of_inputFrequency_eq_zero
    m observed modes input hzero, zero_mul]

/-- Every distinguished tensor contraction vanishes when its observed leg
has zero harmonic frequency.  The conclusion is obtained termwise from the
physical interaction tensor, independently of the modal amplitudes. -/
theorem distinguishedTensorContraction_eq_zero_of_observedFrequency_eq_zero
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (history : WeightedConfiguration N)
    (hzero : modeFrequency m observed = 0) :
    distinguishedTensorContraction m history observed n = 0 := by
  classical
  unfold distinguishedTensorContraction
  apply Finset.sum_eq_zero
  intro modes hmodes
  rw [interactionTensor_cons_eq_zero_of_observedFrequency_eq_zero
    m observed modes hzero, zero_mul]

/-- In particular, the entire polarized quadratic contraction vanishes at a
zero-frequency observed mode. -/
theorem quadraticTensorCrossContraction_eq_zero_of_observedFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (base defect : WeightedConfiguration N)
    (hzero : modeFrequency m observed = 0) :
    quadraticTensorCrossContraction m observed base defect = 0 := by
  classical
  unfold quadraticTensorCrossContraction
  apply Finset.sum_eq_zero
  intro modes hmodes
  rw [interactionTensor_cons_eq_zero_of_observedFrequency_eq_zero
    m observed modes hzero, zero_mul]

/-- The polarized cross contraction is continuous along two continuous modal
histories. -/
theorem continuous_quadraticTensorCrossContraction_comp
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (base defect : Real → WeightedConfiguration N)
    (hbase : Continuous base) (hdefect : Continuous defect) :
    Continuous (fun time ↦
      quadraticTensorCrossContraction m observed
        (base time) (defect time)) := by
  classical
  unfold quadraticTensorCrossContraction
  apply continuous_finsetSum Finset.univ
  intro modes hmodes
  have hbase0 := (PiLp.continuous_apply 2 _ (modes 0)).comp hbase
  have hbase1 := (PiLp.continuous_apply 2 _ (modes 1)).comp hbase
  have hdefect0 := (PiLp.continuous_apply 2 _ (modes 0)).comp hdefect
  have hdefect1 := (PiLp.continuous_apply 2 _ (modes 1)).comp hdefect
  exact continuous_const.mul
    ((hbase0.mul hdefect1).add (hdefect0.mul hbase1))

/-! ## The first Picard coefficient and its real modal history -/

/-- Recover the real coordinate carried by an interaction-picture complex
correction.  Division is totalized at zero frequency; positive-frequency
applications use the usual inverse complex-amplitude formula. -/
def interactionPictureCorrectionCoordinate
    (omega time : Real) (correction : Complex) : Real :=
  Real.sqrt (2 * omega) *
    (phaseRenormalize (-(omega * time)) correction).re / omega

/-- At positive frequency, undoing the interaction-picture phase and applying
`interactionPictureCorrectionCoordinate` exactly recovers the real modal
coordinate represented by `complexModeAmplitude`. -/
theorem interactionPictureCorrectionCoordinate_phaseRenormalize_complexModeAmplitude
    {omega Q P time : Real} (homega : 0 < omega) :
    interactionPictureCorrectionCoordinate omega time
        (phaseRenormalize (omega * time)
          (complexModeAmplitude omega Q P)) = Q := by
  unfold interactionPictureCorrectionCoordinate
  rw [ArchonPhysics.InteractionPictureDuhamel.phaseRenormalize_neg_phaseRenormalize,
    sqrt_two_mul_frequency_mul_re_eq_frequency_mul_coordinate homega]
  exact mul_div_cancel_left₀ Q homega.ne'

/-- The totalized coordinate reconstruction assigns zero to the zero mode. -/
@[simp] theorem interactionPictureCorrectionCoordinate_zero
    (time : Real) (correction : Complex) :
    interactionPictureCorrectionCoordinate 0 time correction = 0 := by
  simp [interactionPictureCorrectionCoordinate]

/-- `A1` as a coefficient of `g`: the unit-`g` quadratic first Picard
correction of one mode. -/
def physlibQuadraticFirstPicardCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (mode : Lattice.Site N) : Complex :=
  freeQuadraticInteractionPictureCorrection
    (physlibQuadraticCoupling m kappa 1 mode)
    m mode radius (modeFrequency m) time phase

/-- The first Picard coefficient of a zero-frequency observed mode vanishes. -/
theorem physlibQuadraticFirstPicardCoefficient_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (mode : Lattice.Site N)
    (hzero : modeFrequency m mode = 0) :
    physlibQuadraticFirstPicardCoefficient
      m kappa radius phase time mode = 0 := by
  have hsource (sourceTime : Real) :
      freeQuadraticTensorSource
        m mode radius (modeFrequency m) sourceTime phase = 0 := by
    classical
    unfold freeQuadraticTensorSource
    apply Finset.sum_eq_zero
    intro modes hmodes
    rw [interactionTensor_cons_eq_zero_of_observedFrequency_eq_zero
      m mode modes hzero, Complex.ofReal_zero, zero_mul]
  unfold physlibQuadraticFirstPicardCoefficient
  unfold freeQuadraticInteractionPictureCorrection
    freeQuadraticPicardIntegrand
  simp_rw [hsource]
  simp

/-- The real modal-coordinate history `Q1` reconstructed from the first
interaction-picture Picard coefficient, mode by mode. -/
def physlibQuadraticFirstPicardModalHistory
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    WeightedConfiguration N :=
  WithLp.toLp 2 (fun mode ↦
    interactionPictureCorrectionCoordinate
      (modeFrequency m mode) time
      (physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time mode))

@[simp] theorem physlibQuadraticFirstPicardModalHistory_apply
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (mode : Lattice.Site N) :
    physlibQuadraticFirstPicardModalHistory
        m kappa radius phase time mode =
      interactionPictureCorrectionCoordinate
        (modeFrequency m mode) time
        (physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time mode) := rfl

/-- The reconstructed first-Picard real modal correction has no zero-mode
component. -/
theorem physlibQuadraticFirstPicardModalHistory_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (mode : Lattice.Site N)
    (hzero : modeFrequency m mode = 0) :
    physlibQuadraticFirstPicardModalHistory
      m kappa radius phase time mode = 0 := by
  rw [physlibQuadraticFirstPicardModalHistory_apply, hzero]
  exact interactionPictureCorrectionCoordinate_zero time _

/-- The first interaction-picture Picard coefficient is continuous in its
upper time endpoint. -/
theorem continuous_physlibQuadraticFirstPicardCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (mode : Lattice.Site N) :
    Continuous (fun time : Real ↦
      physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time mode) := by
  change Continuous (fun time : Real ↦
    ∫ s in (0 : Real)..time,
      physlibFreeQuadraticRotatedSource
        m kappa 1 mode radius phase s)
  apply intervalIntegral.continuous_primitive
  intro a b
  exact (continuous_physlibFreeQuadraticRotatedSource
    m kappa 1 mode radius phase).intervalIntegrable
      (μ := MeasureTheory.volume) a b

/-- The real modal history reconstructed from all first Picard coefficients
is continuous, including the totalized zero-frequency coordinate. -/
theorem continuous_physlibQuadraticFirstPicardModalHistory
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    Continuous (physlibQuadraticFirstPicardModalHistory
      m kappa radius phase) := by
  unfold physlibQuadraticFirstPicardModalHistory
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro mode
  unfold interactionPictureCorrectionCoordinate
  have hA := continuous_physlibQuadraticFirstPicardCoefficient
    m kappa radius phase mode
  have hphase : Continuous (fun time : Real ↦
      phaseFactor (-(modeFrequency m mode * time))) :=
    continuous_phaseFactor_real.comp (by fun_prop)
  unfold phaseRenormalize
  exact (continuous_const.mul
    (Complex.continuous_re.comp (hphase.mul hA))).div_const _

/-- The freely rotating real modal configuration is continuous in time. -/
theorem continuous_freeWeightedConfiguration
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    Continuous (fun time : Real ↦
      freeWeightedConfiguration radius (modeFrequency m) time phase) := by
  unfold freeWeightedConfiguration
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro mode
  unfold freeRealModeCoordinate realPhaseModeCoordinate
    physicalFreePhaseEvolution
    ArchonPhysics.FiniteHarmonicHaarPhasePropagation.freeHarmonicPhaseEvolution
    ArchonPhysics.PhaseEnergyModeCoordinates.unitPhase
  have hadvance : Continuous (fun time : Real ↦
      ArchonPhysics.FiniteHarmonicHaarPhasePropagation.harmonicPhaseAdvance
        (fun mode ↦ -modeFrequency m mode) time mode) := by
    unfold ArchonPhysics.FiniteHarmonicHaarPhasePropagation.harmonicPhaseAdvance
    exact continuous_quotient_mk'.comp (by fun_prop)
  have hcircle : Continuous (fun time : Real ↦
      ArchonPhysics.FiniteHarmonicHaarPhasePropagation.harmonicPhaseAdvance
          (fun mode ↦ -modeFrequency m mode) time mode + phase mode) :=
    hadvance.add continuous_const
  exact continuous_const.mul
    (Complex.continuous_re.comp ((fourier 1).continuous.comp hcircle))

/-- The physical first layer at coupling `g` is exactly `g * A1`; this is a
coefficient identity, not an asymptotic statement. -/
theorem freeQuadraticCorrection_eq_g_mul_firstPicardCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    freeQuadraticInteractionPictureCorrection
        (physlibQuadraticCoupling m kappa g observed)
        m observed radius (modeFrequency m) time phase =
      (g : Complex) * physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time observed := by
  unfold physlibQuadraticFirstPicardCoefficient
  rw [freeQuadraticInteractionPictureCorrection_eq_finiteHaarOscillatorySum,
    freeQuadraticInteractionPictureCorrection_eq_finiteHaarOscillatorySum]
  unfold FiniteHaarOscillatorySecondMoment.finiteHaarOscillatorySum
    FiniteHaarOscillatorySecondMoment.oscillatoryCoefficient
    FreeFPUTDuhamelResonanceBridge.freeQuadraticDuhamelCoefficient
    physlibQuadraticCoupling
    forcedModeSource FiniteDuhamelPhaseAverage.finitePhaseCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term hterm
  push_cast
  ring

/-! ## Exact extraction of the second Picard source -/

/-- Quadratic part of the unit coefficient `A2`: insert `Q1` in exactly one
of the two input legs of the polarized quadratic source. -/
def physlibQuadraticSecondPicardRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  phaseFactor (modeFrequency m observed * time) *
    forcedModeSource (modeFrequency m observed)
      (-(kappa * quadraticTensorCrossContraction m observed
        (freeWeightedConfiguration radius (modeFrequency m) time phase)
        (physlibQuadraticFirstPicardModalHistory
          m kappa radius phase time)))

/-- Cubic-force part of the unit coefficient `A2`, evaluated on the free
modal history. -/
def physlibFreeCubicSecondPicardRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  phaseFactor (modeFrequency m observed * time) *
    forcedModeSource (modeFrequency m observed)
      (-(beta * distinguishedTensorContraction m
        (freeWeightedConfiguration radius (modeFrequency m) time phase)
        observed 3))

/-- Complete second Picard source coefficient, including both the iterated
quadratic force and the free cubic force. -/
def physlibFPUTSecondPicardRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  physlibQuadraticSecondPicardRotatedSource
      m kappa observed radius phase time +
    physlibFreeCubicSecondPicardRotatedSource
      m beta observed radius phase time

/-- `A2`, obtained by integrating the complete unit second-Picard source. -/
def physlibFPUTSecondPicardCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  ∫ s in (0 : Real)..time,
    physlibFPUTSecondPicardRotatedSource
      m kappa beta observed radius phase s

/-- The quadratic second-Picard source has no zero-frequency observed-mode
component. -/
theorem physlibQuadraticSecondPicardRotatedSource_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (hzero : modeFrequency m observed = 0) :
    physlibQuadraticSecondPicardRotatedSource
      m kappa observed radius phase time = 0 := by
  have hcross :
      quadraticTensorCrossContraction m observed
          (freeWeightedConfiguration radius (modeFrequency m) time phase)
          (physlibQuadraticFirstPicardModalHistory
            m kappa radius phase time) = 0 :=
    quadraticTensorCrossContraction_eq_zero_of_observedFrequency_eq_zero
      m observed
        (freeWeightedConfiguration radius (modeFrequency m) time phase)
        (physlibQuadraticFirstPicardModalHistory
          m kappa radius phase time) hzero
  unfold physlibQuadraticSecondPicardRotatedSource
  rw [hcross]
  simp [forcedModeSource]

/-- The free cubic second-Picard source likewise has no zero-frequency
observed-mode component. -/
theorem physlibFreeCubicSecondPicardRotatedSource_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (hzero : modeFrequency m observed = 0) :
    physlibFreeCubicSecondPicardRotatedSource
      m beta observed radius phase time = 0 := by
  have hcubic :
      distinguishedTensorContraction m
          (freeWeightedConfiguration radius (modeFrequency m) time phase)
          observed 3 = 0 :=
    distinguishedTensorContraction_eq_zero_of_observedFrequency_eq_zero
      m observed
        (freeWeightedConfiguration radius (modeFrequency m) time phase) hzero
  unfold physlibFreeCubicSecondPicardRotatedSource
  rw [hcubic]
  simp [forcedModeSource]

/-- Hence the complete extracted second-Picard source vanishes for a
zero-frequency observed mode. -/
theorem physlibFPUTSecondPicardRotatedSource_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (hzero : modeFrequency m observed = 0) :
    physlibFPUTSecondPicardRotatedSource
      m kappa beta observed radius phase time = 0 := by
  unfold physlibFPUTSecondPicardRotatedSource
  rw [physlibQuadraticSecondPicardRotatedSource_eq_zero_of_modeFrequency_eq_zero
      m kappa observed radius phase time hzero,
    physlibFreeCubicSecondPicardRotatedSource_eq_zero_of_modeFrequency_eq_zero
      m beta observed radius phase time hzero,
    zero_add]

/-- The integrated second-Picard coefficient also vanishes at zero observed
frequency. -/
theorem physlibFPUTSecondPicardCoefficient_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (hzero : modeFrequency m observed = 0) :
    physlibFPUTSecondPicardCoefficient
      m kappa beta observed radius phase time = 0 := by
  unfold physlibFPUTSecondPicardCoefficient
  have hsource :
      physlibFPUTSecondPicardRotatedSource
          m kappa beta observed radius phase = 0 := by
    funext s
    exact physlibFPUTSecondPicardRotatedSource_eq_zero_of_modeFrequency_eq_zero
      m kappa beta observed radius phase s hzero
  rw [hsource]
  simp

/-- The complete second-Picard source is continuous.  Hence finite-interval
integrability is a theorem, not an additional dynamical hypothesis. -/
theorem continuous_physlibFPUTSecondPicardRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    Continuous (physlibFPUTSecondPicardRotatedSource
      m kappa beta observed radius phase) := by
  have hfree := continuous_freeWeightedConfiguration m radius phase
  have hfirst := continuous_physlibQuadraticFirstPicardModalHistory
    m kappa radius phase
  have hcross := continuous_quadraticTensorCrossContraction_comp
    m observed _ _ hfree hfirst
  have hcubicContraction := continuous_distinguishedTensorContraction_comp
    m _ hfree observed (n := 3)
  have hphase : Continuous (fun time : Real ↦
      phaseFactor (modeFrequency m observed * time)) :=
    continuous_phaseFactor_real.comp (by fun_prop)
  have hquadraticForce : Continuous (fun time : Real ↦
      forcedModeSource (modeFrequency m observed)
        (-(kappa * quadraticTensorCrossContraction m observed
          (freeWeightedConfiguration radius (modeFrequency m) time phase)
          (physlibQuadraticFirstPicardModalHistory
            m kappa radius phase time)))) := by
    unfold forcedModeSource
    exact (continuous_const.mul
      (Complex.continuous_ofReal.comp
        (continuous_const.mul hcross).neg)).div_const _
  have hcubicForce : Continuous (fun time : Real ↦
      forcedModeSource (modeFrequency m observed)
        (-(beta * distinguishedTensorContraction m
          (freeWeightedConfiguration radius (modeFrequency m) time phase)
          observed 3))) := by
    unfold forcedModeSource
    exact (continuous_const.mul
      (Complex.continuous_ofReal.comp
        (continuous_const.mul hcubicContraction).neg)).div_const _
  unfold physlibFPUTSecondPicardRotatedSource
    physlibQuadraticSecondPicardRotatedSource
    physlibFreeCubicSecondPicardRotatedSource
  exact (hphase.mul hquadraticForce).add (hphase.mul hcubicForce)

/-- The second-Picard source is integrable on every finite oriented interval. -/
theorem intervalIntegrable_physlibFPUTSecondPicardRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (a b : Real) :
    IntervalIntegrable
      (physlibFPUTSecondPicardRotatedSource
        m kappa beta observed radius phase)
      MeasureTheory.volume a b :=
  (continuous_physlibFPUTSecondPicardRotatedSource
    m kappa beta observed radius phase).intervalIntegrable
      (μ := MeasureTheory.volume) a b

/-! ## Exact actual-history remainder -/

/-- What remains after subtracting `g • Q1` from the true modal-history
defect.  No estimate on this remainder is built into the definition. -/
def physlibModalHistoryAfterFirstPicardRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    WeightedConfiguration N :=
  physlibModalHistoryDefect m q radius phase time -
    g • physlibQuadraticFirstPicardModalHistory
      m kappa radius phase time

/-- The actual history defect is identically `g • Q1` plus its remainder. -/
theorem physlibModalHistoryDefect_eq_g_smul_firstPicard_add_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibModalHistoryDefect m q radius phase time =
      g • physlibQuadraticFirstPicardModalHistory
          m kappa radius phase time +
        physlibModalHistoryAfterFirstPicardRemainder
          m kappa g q radius phase time := by
  unfold physlibModalHistoryAfterFirstPicardRemainder
  abel

/-- The part of the physical linear history source left after extracting
`g^2` times the quadratic second-Picard source. -/
def physlibQuadraticLinearHistoryRemainderRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  phaseFactor (modeFrequency m observed * time) *
    forcedModeSource (modeFrequency m observed)
      (-(kappa * g * quadraticTensorCrossContraction m observed
        (freeWeightedConfiguration radius (modeFrequency m) time phase)
        (physlibModalHistoryAfterFirstPicardRemainder
          m kappa g q radius phase time)))

/-- The actual cross term, before adding the defect-square contribution. -/
def physlibQuadraticLinearHistoryRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  phaseFactor (modeFrequency m observed * time) *
    forcedModeSource (modeFrequency m observed)
      (-(kappa * g * quadraticTensorCrossContraction m observed
        (freeWeightedConfiguration radius (modeFrequency m) time phase)
        (physlibModalHistoryDefect m q radius phase time)))

/-- Exact identification of the linear actual-history cross source with
`g^2 A2_quadratic` plus its unestimated history remainder. -/
theorem physlibQuadraticLinearHistoryRotatedSource_eq_secondPicard_add_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibQuadraticLinearHistoryRotatedSource
        m kappa g observed q radius phase time =
      ((g ^ 2 : Real) : Complex) *
          physlibQuadraticSecondPicardRotatedSource
            m kappa observed radius phase time +
        physlibQuadraticLinearHistoryRemainderRotatedSource
          m kappa g observed q radius phase time := by
  rw [physlibQuadraticLinearHistoryRotatedSource]
  rw [physlibModalHistoryDefect_eq_g_smul_firstPicard_add_remainder
      m kappa g q radius phase time,
    quadraticTensorCrossContraction_add_right,
    quadraticTensorCrossContraction_smul_right]
  unfold physlibQuadraticSecondPicardRotatedSource
    physlibQuadraticLinearHistoryRemainderRotatedSource forcedModeSource
  push_cast
  ring

/-- The exact defect-square contribution left by polarization of the
quadratic tensor source. -/
def physlibQuadraticDefectSquareRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  phaseFactor (modeFrequency m observed * time) *
    forcedModeSource (modeFrequency m observed)
      (-(kappa * g * distinguishedTensorContraction m
        (physlibModalHistoryDefect m q radius phase time) observed 2))

/-- The full physical quadratic-history source is its linear cross source
plus the exact defect-square source. -/
theorem physlibQuadraticHistoryDifference_eq_linear_add_defectSquare
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibQuadraticHistoryDifference
        m kappa g observed q radius phase time =
      physlibQuadraticLinearHistoryRotatedSource
          m kappa g observed q radius phase time +
        physlibQuadraticDefectSquareRotatedSource
          m kappa g observed q radius phase time := by
  exact physlibQuadraticHistoryDifference_eq_cross_add_defect
    m kappa g observed q radius phase time

/-- Actual cubic source minus `g^2` times the cubic source evaluated on the
free modal history.  This retains the complete actual-minus-free cubic
history, with no Taylor truncation. -/
def physlibCubicHistoryRemainderRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  physlibCubicRotatedSource m beta g observed q time -
    ((g ^ 2 : Real) : Complex) *
      physlibFreeCubicSecondPicardRotatedSource
        m beta observed radius phase time

/-- Exact cubic source split into its free second-Picard coefficient and the
complete actual-minus-free cubic remainder. -/
theorem physlibCubicRotatedSource_eq_secondPicard_add_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibCubicRotatedSource m beta g observed q time =
      ((g ^ 2 : Real) : Complex) *
          physlibFreeCubicSecondPicardRotatedSource
            m beta observed radius phase time +
        physlibCubicHistoryRemainderRotatedSource
          m beta g observed q radius phase time := by
  unfold physlibCubicHistoryRemainderRotatedSource
  ring

/-- Complete source remainder after extracting `g^2 A2`: the cross-history
remainder, the quadratic defect square, and the actual-minus-free cubic
remainder. -/
def physlibFPUTAfterSecondPicardRemainderRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  physlibQuadraticLinearHistoryRemainderRotatedSource
      m kappa g observed q radius phase time +
    physlibQuadraticDefectSquareRotatedSource
      m kappa g observed q radius phase time +
    physlibCubicHistoryRemainderRotatedSource
      m beta g observed q radius phase time

/-- Exact complete true-history source identity.  Every source omitted from
`A2` occurs explicitly on the right-hand side. -/
theorem physlibFPUTTrueHistorySource_eq_secondPicard_add_remainder
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
  rw [physlibQuadraticHistoryDifference_eq_linear_add_defectSquare,
    physlibQuadraticLinearHistoryRotatedSource_eq_secondPicard_add_remainder,
    physlibCubicRotatedSource_eq_secondPicard_add_remainder]
  all_goals
    unfold physlibFPUTSecondPicardRotatedSource
      physlibFPUTAfterSecondPicardRemainderRotatedSource
    ring

/-- Time-integrated explicit remainder after the second Picard coefficient. -/
def physlibFPUTAfterSecondPicardRemainderCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  ∫ s in (0 : Real)..time,
    physlibFPUTAfterSecondPicardRemainderRotatedSource
      m kappa beta g observed q radius phase s

/-- The two original history integrals split exactly into `g^2 A2` and the
integrated explicit remainder.  All required finite-interval integrability is
derived from continuity and differentiability. -/
theorem intervalIntegrals_trueHistory_eq_secondPicard_add_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N) (hq : Differentiable Real q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    (∫ s in (0 : Real)..time,
        physlibQuadraticHistoryDifference
          m kappa g observed q radius phase s) +
      (∫ s in (0 : Real)..time,
        physlibCubicRotatedSource m beta g observed q s) =
      ((g ^ 2 : Real) : Complex) *
          physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time +
        physlibFPUTAfterSecondPicardRemainderCoefficient
          m kappa beta g observed q radius phase time := by
  obtain ⟨_hfree, hhistory, hcubic⟩ :=
    intervalIntegrable_physlibPicardPieces
      m kappa beta g observed q hq radius phase 0 time
  have hsecond := intervalIntegrable_physlibFPUTSecondPicardRotatedSource
    m kappa beta observed radius phase 0 time
  have hleft : IntervalIntegrable (fun s ↦
      physlibQuadraticHistoryDifference
          m kappa g observed q radius phase s +
        physlibCubicRotatedSource m beta g observed q s)
      MeasureTheory.volume 0 time := hhistory.add hcubic
  have hscaled : IntervalIntegrable (fun s ↦
      ((g ^ 2 : Real) : Complex) *
        physlibFPUTSecondPicardRotatedSource
          m kappa beta observed radius phase s)
      MeasureTheory.volume 0 time := hsecond.const_mul _
  have hremainder : IntervalIntegrable
      (physlibFPUTAfterSecondPicardRemainderRotatedSource
        m kappa beta g observed q radius phase)
      MeasureTheory.volume 0 time := by
    apply (hleft.sub hscaled).congr
    intro s hs
    change
      (physlibQuadraticHistoryDifference
            m kappa g observed q radius phase s +
          physlibCubicRotatedSource m beta g observed q s) -
        ((g ^ 2 : Real) : Complex) *
          physlibFPUTSecondPicardRotatedSource
            m kappa beta observed radius phase s = _
    rw [physlibFPUTTrueHistorySource_eq_secondPicard_add_remainder]
    ring
  calc
    (∫ s in (0 : Real)..time,
        physlibQuadraticHistoryDifference
          m kappa g observed q radius phase s) +
      (∫ s in (0 : Real)..time,
        physlibCubicRotatedSource m beta g observed q s) =
        ∫ s in (0 : Real)..time,
          (physlibQuadraticHistoryDifference
              m kappa g observed q radius phase s +
            physlibCubicRotatedSource m beta g observed q s) := by
      rw [intervalIntegral.integral_add hhistory hcubic]
    _ = ∫ s in (0 : Real)..time,
        (((g ^ 2 : Real) : Complex) *
            physlibFPUTSecondPicardRotatedSource
              m kappa beta observed radius phase s +
          physlibFPUTAfterSecondPicardRemainderRotatedSource
            m kappa beta g observed q radius phase s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact physlibFPUTTrueHistorySource_eq_secondPicard_add_remainder
        m kappa beta g observed q radius phase s
    _ = _ := by
      rw [intervalIntegral.integral_add hscaled hremainder,
        intervalIntegral.integral_const_mul]
      rfl

/-- Exact true-trajectory amplitude through the second Picard extraction.
The final summand is an equality remainder, not an asymptotic `o(g^2)` term. -/
theorem interactionPicture_physlibMode_eq_twoStep_add_remainder
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
  rw [interactionPicture_physlibMode_eq_initial_add_firstPicard_add_remainders
    m kappa beta g observed p q hp hq hHamilton homega radius phase time,
    freeQuadraticCorrection_eq_g_mul_firstPicardCoefficient]
  have hsplit := intervalIntegrals_trueHistory_eq_secondPicard_add_remainder
    m kappa beta g observed q hq radius phase time
  unfold twoStepPerturbedAmplitude
  push_cast
  push_cast at hsplit
  linear_combination hsplit

/-- Exact squared-amplitude formula for the true trajectory.  It displays
the complete two-step polynomial and also retains the interference with and
the square of the equality remainder. -/
theorem normSq_interactionPicture_physlibMode_eq_twoStepPolynomial_add_remainder
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
  rw [interactionPicture_physlibMode_eq_twoStep_add_remainder
    m kappa beta g observed p q hp hq hHamilton homega radius phase time,
    Complex.normSq_add,
    normSq_twoStepPerturbedAmplitude]
  unfold secondMomentFirst secondMomentSecond
  ring

/-! ## Second-order moment coefficient -/

/-- For the microscopic `A1` and `A2` defined above, the order-`g^2`
coefficient is necessarily `|A1|^2 + 2 Re (A0 * conj A2)`. -/
theorem physlibFPUT_secondMomentSecondCoefficient_eq_normSq_add_interference
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
  exact twoStepSecondCoefficient_eq _ _ _

/-- The genuine harmonic modal-energy coefficient at order `g^2` is the
mode frequency times the complete second-moment coefficient. -/
theorem physlibFPUT_modalEnergySecondCoefficient_eq_frequency_mul_normSq_add_interference
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
  rw [physlibFPUT_secondMomentSecondCoefficient_eq_normSq_add_interference]

/-- Exact fourth-degree moment polynomial for the two Picard coefficients.
The cubic and quartic terms are retained; nothing is dropped by order
notation. -/
theorem normSq_physlibFPUT_twoStepPerturbedAmplitude
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (A0 : Complex) :
    Complex.normSq (twoStepPerturbedAmplitude g A0
        (physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time observed)
        (physlibFPUTSecondPicardCoefficient
          m kappa beta observed radius phase time)) =
      secondMomentZeroth A0 +
        g * secondMomentFirst A0
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed) +
        g ^ 2 * twoStepSecondCoefficient A0
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
            m kappa beta observed radius phase time) := by
  exact normSq_twoStepPerturbedAmplitude _ _ _ g

/-! ## Physical modal energy of the true trajectory -/

/-- The interaction-picture squared amplitude, multiplied by the positive
mode frequency, is exactly the real harmonic modal energy of the true
Physlib position and momentum. -/
theorem frequency_mul_normSq_interactionPicture_physlibMode_eq_modalEnergy
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N) (time : Real)
    (homega : 0 < modeFrequency m observed) :
    modeFrequency m observed *
        Complex.normSq
          (phaseRenormalize (modeFrequency m observed * time)
            (physlibModeAmplitude m observed p q time)) =
      modalEnergy (modeFrequencySq m observed)
        (physlibModePosition m observed q time)
        (physlibModeMomentum m observed p time) := by
  rw [normSq_phaseRenormalize]
  unfold physlibModeAmplitude
  rw [frequency_mul_normSq_eq_modalEnergy homega,
    modeFrequency_sq]

/-- Complete exact physical modal-energy identity for the true Hamiltonian
trajectory.  The `g^3` and `g^4` two-step terms, the interference with the
equality remainder, and the remainder square all remain explicit. -/
theorem modalEnergy_physlibMode_eq_frequency_mul_twoStepPolynomial_add_remainder
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
  rw [← frequency_mul_normSq_interactionPicture_physlibMode_eq_modalEnergy
    m observed p q time homega,
    normSq_interactionPicture_physlibMode_eq_twoStepPolynomial_add_remainder
      m kappa beta g observed p q hp hq hHamilton homega radius phase time]

end

end ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

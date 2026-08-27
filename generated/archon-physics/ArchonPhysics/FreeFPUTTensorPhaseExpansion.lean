import ArchonPhysics.PhaseEnergyModeCoordinates
import ArchonPhysics.ModalNonlinearForce
import ArchonPhysics.FiniteHarmonicHaarPhasePropagation
import ArchonPhysics.FiniteDuhamelPhaseAverage

/-!
# Free FPUT tensor sources as finite phase-character polynomials

This module supplies the first algebraic micro-to-kinetic bridge for the
quadratic (three-wave) FPUT tensor source. A real free modal coordinate is
split into its positive- and negative-phase characters. Consequently the
finite quadratic interaction-tensor contraction, and any deterministic scalar
multiple used as a first-Picard integrand, are exact finite Fourier-character
polynomials of the initial phases.

The physical free orbit uses the negative phase advance: the complex mode
amplitude obeys `a' = -i * omega * a`, whereas the generic Haar-translation API
is parameterized by an arbitrary signed frequency. Haar charge balance then
gives the exact mean selector and annihilates a correction when every term is
charge-unbalanced.

Everything here is finite-volume algebra for the free-orbit Picard main term.
It does not prove nonlinear random-phase propagation, a kinetic limit, or
control of a Duhamel remainder.
-/

namespace ArchonPhysics.FreeFPUTTensorPhaseExpansion

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModeCoupling

noncomputable section

/-- The two sectors in the real-part decomposition: positive character and
negative/conjugate character. -/
def binaryPhaseSign (sign : Fin 2) : PhaseSign :=
  if sign = 0 then .phase else .conjugate

@[simp] theorem binaryPhaseSign_zero :
    binaryPhaseSign (0 : Fin 2) = .phase := by
  simp [binaryPhaseSign]

@[simp] theorem binaryPhaseSign_one :
    binaryPhaseSign (1 : Fin 2) = .conjugate := by
  simp [binaryPhaseSign]

/-- A mode carrying one of the two real-part character signs. -/
def binarySignedMode {d : Type*} (mode : d) (sign : Fin 2) : SignedMode d :=
  ⟨mode, binaryPhaseSign sign⟩

/-- The corresponding single-mode character. -/
def binarySignedCharacter {d : Type*} [Fintype d] [DecidableEq d]
    (mode : d) (sign : Fin 2) (phase : UnitAddTorus d) : Complex :=
  (binarySignedMode mode sign).phaseFactor phase

/-- A real modal coordinate with deterministic radial amplitude and phase. -/
def realPhaseModeCoordinate {d : Type*}
    (radius : d → Real) (phase : UnitAddTorus d) (mode : d) : Real :=
  radius mode * (unitPhase (phase mode)).re

/-- Exact two-character decomposition of one real modal coordinate. -/
theorem coe_realPhaseModeCoordinate_eq_binarySignedSum
    {d : Type*} [Fintype d] [DecidableEq d]
    (radius : d → Real) (phase : UnitAddTorus d) (mode : d) :
    (realPhaseModeCoordinate radius phase mode : Complex) =
      ∑ sign : Fin 2, ((radius mode / 2 : Real) : Complex) *
        binarySignedCharacter mode sign phase := by
  rw [Fin.sum_univ_two]
  unfold realPhaseModeCoordinate binarySignedCharacter binarySignedMode
  simp only [binaryPhaseSign_zero, binaryPhaseSign_one,
    SignedMode.phaseFactor, unitPhase]
  apply Complex.ext
  · simp
    ring
  · simp

/-- Physical free phase evolution. The minus sign matches
`ComplexModeAmplitude.hasDerivAt_complexModeAmplitude_harmonic`. -/
def physicalFreePhaseEvolution {d : Type*}
    (frequency : d → Real) (time : Real) : UnitAddTorus d → UnitAddTorus d :=
  freeHarmonicPhaseEvolution (fun mode => -frequency mode) time

/-- Real modal coordinate evaluated on the physical free orbit. -/
def freeRealModeCoordinate {d : Type*}
    (radius frequency : d → Real) (time : Real)
    (phase : UnitAddTorus d) (mode : d) : Real :=
  realPhaseModeCoordinate radius
    (physicalFreePhaseEvolution frequency time phase) mode

/-- The prescribed-energy radius used by `phaseCoordinate`. -/
def phaseEnergyRadius {d : Type*}
    (energy frequency : d → Real) (mode : d) : Real :=
  Real.sqrt (2 * energy mode) / frequency mode

/-- The radial presentation agrees exactly with the existing prescribed-energy
phase coordinate, including its totalized value at zero frequency. -/
theorem freeRealModeCoordinate_phaseEnergyRadius
    {d : Type*} (energy frequency : d → Real) (time : Real)
    (phase : UnitAddTorus d) (mode : d) :
    freeRealModeCoordinate (phaseEnergyRadius energy frequency) frequency
        time phase mode =
      phaseCoordinate (energy mode) (frequency mode)
        (physicalFreePhaseEvolution frequency time phase mode) := by
  unfold freeRealModeCoordinate realPhaseModeCoordinate phaseEnergyRadius
    phaseCoordinate
  ring

/-- Free evolution retains the normalized finite product Haar law. -/
theorem measurePreserving_physicalFreePhaseEvolution
    {d : Type*} [Fintype d] (frequency : d → Real) (time : Real) :
    MeasurePreserving (physicalFreePhaseEvolution frequency time)
      (RandomPhaseMoments.finitePhaseHaarLaw d)
      (RandomPhaseMoments.finitePhaseHaarLaw d) := by
  simpa [physicalFreePhaseEvolution] using
    (measurePreserving_freeHarmonicPhaseEvolution
      (fun mode => -frequency mode) time)

/-- Coercion of one freely evolved real coordinate into its exact signed
character sum. -/
theorem coe_freeRealModeCoordinate_eq_binarySignedSum
    {d : Type*} [Fintype d] [DecidableEq d]
    (radius frequency : d → Real) (time : Real)
    (phase : UnitAddTorus d) (mode : d) :
    (freeRealModeCoordinate radius frequency time phase mode : Complex) =
      ∑ sign : Fin 2, ((radius mode / 2 : Real) : Complex) *
        binarySignedCharacter mode sign
          (physicalFreePhaseEvolution frequency time phase) := by
  exact coe_realPhaseModeCoordinate_eq_binarySignedSum radius
    (physicalFreePhaseEvolution frequency time phase) mode

/-- One quadratic tensor term is indexed by two internal modes and two signed
phase sectors. -/
abbrev QuadraticPhaseTerm (N : Nat) :=
  (Fin 2 → Lattice.Site N) × (Fin 2 × Fin 2)

/-- Total Haar charge of one signed quadratic tensor term. -/
def quadraticPhaseCharge {N : Nat} [NeZero N]
    (term : QuadraticPhaseTerm N) : Lattice.Site N → Int :=
  (binarySignedMode (term.1 0) term.2.1).charge +
    (binarySignedMode (term.1 1) term.2.2).charge

/-- Deterministic coefficient of one quadratic tensor character. -/
def quadraticPhaseCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (term : QuadraticPhaseTerm N) : Complex :=
  (interactionTensor m 3 (Fin.cons observed term.1) : Complex) *
    ((radius (term.1 0) / 2 : Real) : Complex) *
    ((radius (term.1 1) / 2 : Real) : Complex)

/-- Finite character polynomial representing the quadratic tensor source. -/
def quadraticTensorPhasePolynomial {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  finitePhaseCorrection
    (quadraticPhaseCoefficient m observed radius) quadraticPhaseCharge phase

/-- Complexification of the quadratic tensor contraction evaluated on the
physical free real-mode orbit. -/
def freeQuadraticTensorSource {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  ∑ modes : Fin 2 → Lattice.Site N,
    (interactionTensor m 3 (Fin.cons observed modes) : Complex) *
      ∏ r, (freeRealModeCoordinate radius frequency time phase (modes r) : Complex)

/-- The freely evolved site function packaged in the existing finite Euclidean
modal-coordinate space. -/
def freeWeightedConfiguration {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    ReducedModeTransform.WeightedConfiguration N :=
  WithLp.toLp 2 (freeRealModeCoordinate radius frequency time phase)

@[simp] theorem freeWeightedConfiguration_apply
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) (mode : Lattice.Site N) :
    freeWeightedConfiguration radius frequency time phase mode =
      freeRealModeCoordinate radius frequency time phase mode := rfl

/-- The explicit complex sum is exactly the complexification of the existing
real `distinguishedTensorContraction` at order two. -/
theorem freeQuadraticTensorSource_eq_complex_tensorContraction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticTensorSource m observed radius frequency time phase =
      (distinguishedTensorContraction m
        (freeWeightedConfiguration radius frequency time phase) observed 2 : Real) := by
  unfold freeQuadraticTensorSource distinguishedTensorContraction
  push_cast
  rfl

/-- Product of two signed single-mode factors is the multivariate character
of their summed charge. -/
theorem binarySignedCharacter_mul_eq_mFourier
    {d : Type*} [Fintype d] [DecidableEq d]
    (leftMode rightMode : d) (leftSign rightSign : Fin 2)
    (phase : UnitAddTorus d) :
    binarySignedCharacter leftMode leftSign phase *
        binarySignedCharacter rightMode rightSign phase =
      mFourier
        ((binarySignedMode leftMode leftSign).charge +
          (binarySignedMode rightMode rightSign).charge) phase := by
  unfold binarySignedCharacter
  rw [SignedMode.phaseFactor_eq_mFourier,
    SignedMode.phaseFactor_eq_mFourier, ← mFourier_add]

/-- Exact finite-character expansion of the free quadratic (three-wave) tensor
source. No approximation is used. -/
theorem freeQuadraticTensorSource_eq_phasePolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticTensorSource m observed radius frequency time phase =
      quadraticTensorPhasePolynomial m observed radius
        (physicalFreePhaseEvolution frequency time phase) := by
  classical
  unfold freeQuadraticTensorSource quadraticTensorPhasePolynomial
    finitePhaseCorrection
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro modes hmodes
  rw [Fin.prod_univ_two,
    coe_freeRealModeCoordinate_eq_binarySignedSum,
    coe_freeRealModeCoordinate_eq_binarySignedSum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro leftSign hleftSign
  apply Finset.sum_congr rfl
  intro rightSign hrightSign
  simp only [quadraticPhaseCoefficient, quadraticPhaseCharge]
  rw [← binarySignedCharacter_mul_eq_mFourier]
  ring

/-- A deterministic scalar multiple of the source. At a fixed time this scalar
can contain the FPUT coupling and the output interaction-picture phase, so this
is the algebraic first-Picard integrand. -/
def freeQuadraticPicardIntegrand {N : Nat} [NeZero N]
    (timeCoefficient : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  timeCoefficient *
    freeQuadraticTensorSource m observed radius frequency time phase

/-- Character coefficient after inserting the deterministic Picard factor. -/
def quadraticPicardCoefficient {N : Nat} [NeZero N]
    (timeCoefficient : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (term : QuadraticPhaseTerm N) : Complex :=
  timeCoefficient * quadraticPhaseCoefficient m observed radius term

/-- Exact finite-character form of the quadratic first-Picard integrand. -/
theorem freeQuadraticPicardIntegrand_eq_finitePhaseCorrection
    {N : Nat} [NeZero N]
    (timeCoefficient : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticPicardIntegrand timeCoefficient m observed radius frequency
        time phase =
      finitePhaseCorrection
        (quadraticPicardCoefficient timeCoefficient m observed radius)
        quadraticPhaseCharge
        (physicalFreePhaseEvolution frequency time phase) := by
  unfold freeQuadraticPicardIntegrand quadraticPicardCoefficient
  rw [freeQuadraticTensorSource_eq_phasePolynomial]
  unfold quadraticTensorPhasePolynomial finitePhaseCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term hterm
  ring

/-- Exact Haar mean of the free quadratic first-Picard integrand: only
charge-balanced terms survive. -/
theorem integral_freeQuadraticPicardIntegrand_eq_zeroChargeSum
    {N : Nat} [NeZero N]
    (timeCoefficient : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      freeQuadraticPicardIntegrand timeCoefficient m observed radius frequency
        time phase
      ∂(RandomPhaseMoments.finitePhaseHaarLaw (Lattice.Site N))) =
      ∑ term : QuadraticPhaseTerm N,
        if quadraticPhaseCharge term = 0 then
          quadraticPicardCoefficient timeCoefficient m observed radius term
        else 0 := by
  have hpreserve :=
    measurePreserving_physicalFreePhaseEvolution frequency time
  have hembed : MeasurableEmbedding
      (physicalFreePhaseEvolution frequency time) := by
    unfold physicalFreePhaseEvolution freeHarmonicPhaseEvolution
    exact measurableEmbedding_addLeft _
  calc
    (∫ phase : UnitAddTorus (Lattice.Site N),
      freeQuadraticPicardIntegrand timeCoefficient m observed radius frequency
        time phase
      ∂(RandomPhaseMoments.finitePhaseHaarLaw (Lattice.Site N))) =
        ∫ phase : UnitAddTorus (Lattice.Site N),
          finitePhaseCorrection
            (quadraticPicardCoefficient timeCoefficient m observed radius)
            quadraticPhaseCharge
            (physicalFreePhaseEvolution frequency time phase)
          ∂(RandomPhaseMoments.finitePhaseHaarLaw (Lattice.Site N)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase =>
        freeQuadraticPicardIntegrand_eq_finitePhaseCorrection
          timeCoefficient m observed radius frequency time phase
    _ = ∫ phase : UnitAddTorus (Lattice.Site N),
          finitePhaseCorrection
            (quadraticPicardCoefficient timeCoefficient m observed radius)
            quadraticPhaseCharge phase
          ∂(RandomPhaseMoments.finitePhaseHaarLaw (Lattice.Site N)) := by
      exact hpreserve.integral_comp hembed _
    _ = ∑ term : QuadraticPhaseTerm N,
        if quadraticPhaseCharge term = 0 then
          quadraticPicardCoefficient timeCoefficient m observed radius term
        else 0 :=
      integral_finitePhaseCorrection_eq_zeroChargeSum
        (quadraticPicardCoefficient timeCoefficient m observed radius)
        quadraticPhaseCharge

/-- If every signed quadratic term is charge-unbalanced, the Haar mean of the
first-Picard integrand vanishes exactly. -/
theorem integral_freeQuadraticPicardIntegrand_eq_zero
    {N : Nat} [NeZero N]
    (timeCoefficient : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (hunbalanced : ∀ term : QuadraticPhaseTerm N,
      quadraticPhaseCharge term ≠ 0) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      freeQuadraticPicardIntegrand timeCoefficient m observed radius frequency
        time phase
      ∂(RandomPhaseMoments.finitePhaseHaarLaw (Lattice.Site N))) = 0 := by
  rw [integral_freeQuadraticPicardIntegrand_eq_zeroChargeSum]
  simp [hunbalanced]

end

end ArchonPhysics.FreeFPUTTensorPhaseExpansion

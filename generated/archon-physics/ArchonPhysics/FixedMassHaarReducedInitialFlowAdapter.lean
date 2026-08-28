import ArchonPhysics.CanonicalRandomMassGlobalFlow
import ArchonPhysics.FreeFPUTA0DirectCubicBridge
import ArchonPhysics.GlobalRandomMassModalObservable
import ArchonPhysics.PhyslibInitialModalReference
import ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
import ArchonPhysics.TranslationZeroModeEnergy

/-!
# Fixed-mass Haar initial data and the canonical ambient flow

This module constructs the radial/Haar initial state used by the finite
Picard character expansion directly in the translation-reduced physical
phase space.  The only necessary zero-mode input is that the radial position
coefficient vanishes at every zero frequency.  The modal momentum vanishes
there automatically because it contains the frequency factor.

The reduced initial map is continuous in the complete finite Haar phase
torus.  Embedding it into the common parametric phase space and applying the
canonical cutoff flow therefore gives jointly measurable ambient position
and momentum paths.  On a common energy shell, the existing global matching
theorem supplies a genuine reduced trajectory at each phase; projection of
the matching identity transfers differentiability and the exact Physlib
Hamilton equations to the already measurable ambient paths.

No random-phase approximation, kinetic equation, or solution certificate is
introduced.
-/

namespace ArchonPhysics.FixedMassHaarReducedInitialFlowAdapter

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalForcedDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhyslibInitialModalReference
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
open ArchonPhysics.ReducedHarmonicSpectrum
open ArchonPhysics.ReducedModeTransform
open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

/-! ## Zero-frequency reconstruction and the two physical gauges -/

/-- The translation vector bundled in the mass-weighted Euclidean space. -/
def weightedTranslationMode {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : WeightedConfiguration N :=
  WithLp.toLp 2 (translationMode m)

theorem harmonicOperator_weightedTranslationMode_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    harmonicOperator m (weightedTranslationMode m) = 0 := by
  rw [harmonicOperator_apply]
  unfold weightedTranslationMode
  rw [translationMode_is_zero]
  rfl

/-- A positive-frequency normal coordinate of the translation vector is
zero.  This follows from diagonalizing the harmonic operator, not from a
simple-spectrum assumption. -/
theorem modalCoordinates_weightedTranslationMode_eq_zero_of_frequency_ne_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : Lattice.Site N) (hfrequency : modeFrequency m k ≠ 0) :
    modalCoordinates m (weightedTranslationMode m) k = 0 := by
  have hdiag := modalCoordinates_harmonicOperator
    m (weightedTranslationMode m) k
  rw [harmonicOperator_weightedTranslationMode_eq_zero] at hdiag
  simp only [map_zero, PiLp.zero_apply] at hdiag
  have hsquared : modeFrequencySq m k ≠ 0 := by
    intro hsquaredZero
    apply hfrequency
    have hsq : modeFrequency m k ^ 2 = 0 := by
      rw [modeFrequency_sq, hsquaredZero]
    exact sq_eq_zero_iff.mp hsq
  exact (mul_eq_zero.mp hdiag.symm).resolve_left hsquared

/-- If all zero-frequency modal coefficients of `a` vanish, reconstructing
`a` produces a vector orthogonal to the complete translation kernel.  No
choice of a distinguished zero-mode index is needed. -/
theorem inner_weightedTranslationMode_reconstruct_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (a : WeightedConfiguration N)
    (hzero : ∀ k, modeFrequency m k = 0 → a k = 0) :
    ⟪weightedTranslationMode m, reconstruct m a⟫_ℝ = 0 := by
  have hisometry := (modalCoordinates m).inner_map_map
    (weightedTranslationMode m) (reconstruct m a)
  rw [modalCoordinates_reconstruct] at hisometry
  rw [← hisometry]
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hfrequency : modeFrequency m k = 0
  · rw [hzero k hfrequency]
    simp
  · rw [modalCoordinates_weightedTranslationMode_eq_zero_of_frequency_ne_zero
      m k hfrequency]
    simp

/-- Physical position obtained by undoing the square-root mass transform. -/
def physicalPositionOfWeighted
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (X : WeightedConfiguration N) : HilbertConfiguration N :=
  inverseSqrtMassTransform m X

/-- Physical canonical momentum obtained by applying the square-root mass
transform to the mass-weighted modal momentum. -/
def physicalMomentumOfWeighted
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (Y : WeightedConfiguration N) : HilbertConfiguration N :=
  sqrtMassTransform m Y

@[simp] theorem sqrtMassTransform_physicalPositionOfWeighted
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (X : WeightedConfiguration N) :
    sqrtMassTransform m (physicalPositionOfWeighted m X) = X := by
  ext i
  unfold physicalPositionOfWeighted
  rw [sqrtMassTransform_apply, inverseSqrtMassTransform_apply]
  rw [← mul_assoc,
    mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (m.mass_pos i)), one_mul]

@[simp] theorem inverseSqrtMassTransform_physicalMomentumOfWeighted
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (Y : WeightedConfiguration N) :
    inverseSqrtMassTransform m (physicalMomentumOfWeighted m Y) = Y := by
  ext i
  unfold physicalMomentumOfWeighted
  rw [inverseSqrtMassTransform_apply, sqrtMassTransform_apply]
  rw [← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (m.mass_pos i)), one_mul]

/-- Orthogonality to the weighted translation vector is exactly the physical
mass-weighted position gauge after undoing the mass transform. -/
theorem physicalPositionOfWeighted_mem_reducedPositionSpace
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (X : WeightedConfiguration N)
    (horthogonal : ⟪weightedTranslationMode m, X⟫_ℝ = 0) :
    physicalPositionOfWeighted m X ∈ ReducedPositionSpace m := by
  rw [mem_reducedPositionSpace_iff]
  unfold physicalPositionOfWeighted
  simp only [inverseSqrtMassTransform_apply]
  change ∑ i, m.mass i *
    ((Real.sqrt (m.mass i))⁻¹ * X i) = 0
  have hsum :
      (∑ i, m.mass i * ((Real.sqrt (m.mass i))⁻¹ * X i)) =
        ∑ i, X i * Real.sqrt (m.mass i) := by
    apply Finset.sum_congr rfl
    intro i _hi
    have hsqrt : Real.sqrt (m.mass i) ≠ 0 :=
      Real.sqrt_ne_zero'.2 (m.mass_pos i)
    have hmass : Real.sqrt (m.mass i) * Real.sqrt (m.mass i) =
        m.mass i := by
      simpa [pow_two] using Real.sq_sqrt (m.mass_pos i).le
    calc
      m.mass i * ((Real.sqrt (m.mass i))⁻¹ * X i) =
          (Real.sqrt (m.mass i) * Real.sqrt (m.mass i)) *
            ((Real.sqrt (m.mass i))⁻¹ * X i) :=
        congrArg (fun c : Real ↦
          c * ((Real.sqrt (m.mass i))⁻¹ * X i)) hmass.symm
      _ = X i * Real.sqrt (m.mass i) := by
        field_simp [hsqrt]
  rw [hsum]
  rw [PiLp.inner_apply] at horthogonal
  simpa [weightedTranslationMode, translationMode, mul_comm] using horthogonal

/-- The same orthogonality is exactly zero total canonical momentum after
applying the square-root mass transform. -/
theorem physicalMomentumOfWeighted_mem_reducedMomentumSpace
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (Y : WeightedConfiguration N)
    (horthogonal : ⟪weightedTranslationMode m, Y⟫_ℝ = 0) :
    physicalMomentumOfWeighted m Y ∈ ReducedMomentumSpace N := by
  rw [mem_reducedMomentumSpace_iff]
  rw [PiLp.inner_apply] at horthogonal
  simpa [weightedTranslationMode, physicalMomentumOfWeighted,
    sqrtMassTransform_apply, translationMode, mul_comm] using horthogonal

/-! ## Explicit radial/Haar reduced initial state -/

/-- Real modal position at time zero for fixed radii and Haar phases. -/
def fixedMassHaarModalPosition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : WeightedConfiguration N :=
  freeWeightedConfiguration radius (modeFrequency m) 0 phase

/-- Real modal momentum at time zero for the same radial/Haar data. -/
def fixedMassHaarModalMomentum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : WeightedConfiguration N :=
  WithLp.toLp 2 fun k ↦
    freeReferenceInitialModalMomentum radius (modeFrequency m) phase k

theorem fixedMassHaarModalPosition_eq_radius_mul_re
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (k : Lattice.Site N) :
    fixedMassHaarModalPosition m radius phase k =
      radius k * (unitPhase (phase k)).re := by
  exact freeWeightedConfiguration_zero_apply
    radius (modeFrequency m) phase k

@[simp] theorem fixedMassHaarModalMomentum_apply
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (k : Lattice.Site N) :
    fixedMassHaarModalMomentum m radius phase k =
      modeFrequency m k * radius k * (unitPhase (phase k)).im := rfl

theorem fixedMassHaarModalPosition_zero_of_frequency_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) (k : Lattice.Site N)
    (hfrequency : modeFrequency m k = 0) :
    fixedMassHaarModalPosition m radius phase k = 0 := by
  rw [fixedMassHaarModalPosition_eq_radius_mul_re,
    hzero k hfrequency, zero_mul]

theorem fixedMassHaarModalMomentum_zero_of_frequency_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (k : Lattice.Site N)
    (hfrequency : modeFrequency m k = 0) :
    fixedMassHaarModalMomentum m radius phase k = 0 := by
  simp [hfrequency]

/-- Reconstructed mass-weighted position. -/
def fixedMassHaarWeightedPosition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : WeightedConfiguration N :=
  reconstruct m (fixedMassHaarModalPosition m radius phase)

/-- Reconstructed mass-weighted momentum. -/
def fixedMassHaarWeightedMomentum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : WeightedConfiguration N :=
  reconstruct m (fixedMassHaarModalMomentum m radius phase)

/-- Physical position of the fixed-mass Haar initializer. -/
def fixedMassHaarPhysicalPosition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : HilbertConfiguration N :=
  physicalPositionOfWeighted m
    (fixedMassHaarWeightedPosition m radius phase)

/-- Physical canonical momentum of the fixed-mass Haar initializer. -/
def fixedMassHaarPhysicalMomentum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : HilbertConfiguration N :=
  physicalMomentumOfWeighted m
    (fixedMassHaarWeightedMomentum m radius phase)

theorem fixedMassHaarPhysicalPosition_mem_reduced
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) :
    fixedMassHaarPhysicalPosition m radius phase ∈ ReducedPositionSpace m := by
  apply physicalPositionOfWeighted_mem_reducedPositionSpace
  apply inner_weightedTranslationMode_reconstruct_eq_zero
  exact fixedMassHaarModalPosition_zero_of_frequency_eq_zero
    m radius hzero phase

theorem fixedMassHaarPhysicalMomentum_mem_reduced
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    fixedMassHaarPhysicalMomentum m radius phase ∈ ReducedMomentumSpace N := by
  apply physicalMomentumOfWeighted_mem_reducedMomentumSpace
  apply inner_weightedTranslationMode_reconstruct_eq_zero
  exact fixedMassHaarModalMomentum_zero_of_frequency_eq_zero m radius phase

/-- Genuine translation-reduced radial/Haar initial state. -/
def fixedMassHaarReducedInitialState
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) : ReducedPhaseSpace m :=
  (⟨fixedMassHaarPhysicalPosition m radius phase,
      fixedMassHaarPhysicalPosition_mem_reduced m radius hzero phase⟩,
    ⟨fixedMassHaarPhysicalMomentum m radius phase,
      fixedMassHaarPhysicalMomentum_mem_reduced m radius phase⟩)

/-! ## Continuity and measurability of the initializer -/

theorem continuous_fixedMassHaarModalPosition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real) :
    Continuous (fixedMassHaarModalPosition m radius) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  have hphase : Continuous
      (fun phase : UnitAddTorus (Lattice.Site N) ↦ unitPhase (phase k)) :=
    continuous_unitPhase.comp (continuous_apply k)
  change Continuous (fun phase : UnitAddTorus (Lattice.Site N) ↦
    fixedMassHaarModalPosition m radius phase k)
  have heq :
      (fun phase : UnitAddTorus (Lattice.Site N) ↦
          fixedMassHaarModalPosition m radius phase k) =
        fun phase ↦ radius k * (unitPhase (phase k)).re := by
    funext phase
    exact fixedMassHaarModalPosition_eq_radius_mul_re m radius phase k
  rw [heq]
  exact continuous_const.mul (Complex.continuous_re.comp hphase)

theorem continuous_fixedMassHaarModalMomentum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real) :
    Continuous (fixedMassHaarModalMomentum m radius) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  have hphase : Continuous
      (fun phase : UnitAddTorus (Lattice.Site N) ↦ unitPhase (phase k)) :=
    continuous_unitPhase.comp (continuous_apply k)
  exact continuous_const.mul (Complex.continuous_im.comp hphase)

theorem continuous_fixedMassHaarPhysicalPosition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real) :
    Continuous (fixedMassHaarPhysicalPosition m radius) := by
  unfold fixedMassHaarPhysicalPosition physicalPositionOfWeighted
    fixedMassHaarWeightedPosition
  exact (inverseSqrtMassTransform m).continuous.comp
    ((reconstruct m).continuous.comp
      (continuous_fixedMassHaarModalPosition m radius))

theorem continuous_fixedMassHaarPhysicalMomentum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real) :
    Continuous (fixedMassHaarPhysicalMomentum m radius) := by
  unfold fixedMassHaarPhysicalMomentum physicalMomentumOfWeighted
    fixedMassHaarWeightedMomentum
  exact (sqrtMassTransform m).continuous.comp
    ((reconstruct m).continuous.comp
      (continuous_fixedMassHaarModalMomentum m radius))

theorem continuous_fixedMassHaarReducedInitialState
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0) :
    Continuous (fixedMassHaarReducedInitialState m radius hzero) := by
  exact (Continuous.subtype_mk
      (continuous_fixedMassHaarPhysicalPosition m radius) _).prodMk
    (Continuous.subtype_mk
      (continuous_fixedMassHaarPhysicalMomentum m radius) _)

theorem measurable_fixedMassHaarReducedInitialState
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0) :
    Measurable (fixedMassHaarReducedInitialState m radius hzero) :=
  (continuous_fixedMassHaarReducedInitialState m radius hzero).measurable

/-! ## Exact modal reconstruction and A0 alignment -/

@[simp] theorem modalCoordinates_sqrtMassTransform_fixedMassHaarPosition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    modalCoordinates m
        (sqrtMassTransform m (fixedMassHaarPhysicalPosition m radius phase)) =
      fixedMassHaarModalPosition m radius phase := by
  unfold fixedMassHaarPhysicalPosition fixedMassHaarWeightedPosition
  rw [sqrtMassTransform_physicalPositionOfWeighted]
  exact modalCoordinates_reconstruct m _

@[simp] theorem modalCoordinates_inverseSqrtMassTransform_fixedMassHaarMomentum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    modalCoordinates m
        (inverseSqrtMassTransform m
          (fixedMassHaarPhysicalMomentum m radius phase)) =
      fixedMassHaarModalMomentum m radius phase := by
  unfold fixedMassHaarPhysicalMomentum fixedMassHaarWeightedMomentum
  rw [inverseSqrtMassTransform_physicalMomentumOfWeighted]
  exact modalCoordinates_reconstruct m _

/-- The explicit reduced initializer discharges the initial-amplitude
alignment used by the actual Haar post-second-Picard decomposition. -/
theorem complexModeAmplitude_fixedMassHaarInitial_eq_canonicalFree
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (observed : Lattice.Site N) :
    complexModeAmplitude (modeFrequency m observed)
      (modalCoordinates m
        (sqrtMassTransform m
          (fixedMassHaarPhysicalPosition m radius phase)) observed)
      (modalCoordinates m
        (inverseSqrtMassTransform m
          (fixedMassHaarPhysicalMomentum m radius phase)) observed) =
      canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) phase observed := by
  rw [modalCoordinates_sqrtMassTransform_fixedMassHaarPosition,
    modalCoordinates_inverseSqrtMassTransform_fixedMassHaarMomentum]
  unfold fixedMassHaarModalPosition fixedMassHaarModalMomentum
    canonicalFreeComplexInitialAmplitude
  rfl

/-! ## Measurable ambient flow and pointwise genuine-solution transfer -/

/-- Common parametric initial point generated by the fixed-mass Haar state. -/
def fixedMassHaarParametricInitial
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) : ParametricPhaseSpace N :=
  embedReducedPoint m shell.kappa shell.beta shell.g
    (fixedMassHaarReducedInitialState m radius hzero phase)

theorem measurable_fixedMassHaarParametricInitial
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0) :
    Measurable (fixedMassHaarParametricInitial shell m radius hzero) := by
  unfold fixedMassHaarParametricInitial embedReducedPoint
  have hz := measurable_fixedMassHaarReducedInitialState m radius hzero
  exact measurable_const.prodMk
    (((measurable_subtype_coe.comp hz.fst).prodMk
      (measurable_subtype_coe.comp hz.snd)))

/-- Jointly measurable ambient canonical-flow position. -/
def fixedMassHaarCanonicalFlowPosition
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0) :
    UnitAddTorus (Lattice.Site N) × Real → HilbertConfiguration N :=
  sampledFlowPosition (fixedMassHaarParametricInitial shell m radius hzero)
    (canonicalRandomMassGlobalFlow shell)

/-- Jointly measurable ambient canonical-flow momentum. -/
def fixedMassHaarCanonicalFlowMomentum
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0) :
    UnitAddTorus (Lattice.Site N) × Real → HilbertConfiguration N :=
  sampledFlowMomentum (fixedMassHaarParametricInitial shell m radius hzero)
    (canonicalRandomMassGlobalFlow shell)

theorem measurable_fixedMassHaarCanonicalFlowPosition
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0) :
    Measurable (fixedMassHaarCanonicalFlowPosition shell m radius hzero) :=
  measurable_sampledFlowPosition _ _
    (measurable_fixedMassHaarParametricInitial shell m radius hzero)
    (measurable_canonicalRandomMassGlobalFlow shell)

theorem measurable_fixedMassHaarCanonicalFlowMomentum
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0) :
    Measurable (fixedMassHaarCanonicalFlowMomentum shell m radius hzero) :=
  measurable_sampledFlowMomentum _ _
    (measurable_fixedMassHaarParametricInitial shell m radius hzero)
    (measurable_canonicalRandomMassGlobalFlow shell)

/-- Ambient position rewritten as a Physlib `Time` path. -/
def fixedMassHaarCanonicalPhyslibPosition
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) :
    Time → HilbertConfiguration N :=
  fun t ↦ fixedMassHaarCanonicalFlowPosition shell m radius hzero
    (phase, Time.toRealCLE t)

/-- Ambient momentum rewritten as a Physlib `Time` path. -/
def fixedMassHaarCanonicalPhyslibMomentum
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) :
    Time → HilbertConfiguration N :=
  fun t ↦ fixedMassHaarCanonicalFlowMomentum shell m radius hzero
    (phase, Time.toRealCLE t)

/-- The ambient position and momentum remain jointly measurable after the
canonical `Time → Real` reparametrization. -/
theorem measurable_fixedMassHaarCanonicalPhyslibPaths
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0) :
    Measurable (fun pt : UnitAddTorus (Lattice.Site N) × Time ↦
      (fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero pt.1 pt.2,
        fixedMassHaarCanonicalPhyslibPosition shell m radius hzero pt.1 pt.2)) := by
  let reparametrize : UnitAddTorus (Lattice.Site N) × Time →
      UnitAddTorus (Lattice.Site N) × Real :=
    fun pt ↦ (pt.1, Time.toRealCLE pt.2)
  have hreparametrize : Measurable reparametrize :=
    measurable_fst.prodMk (Time.toRealCLE.continuous.measurable.comp measurable_snd)
  exact ((measurable_fixedMassHaarCanonicalFlowMomentum
      shell m radius hzero).comp hreparametrize).prodMk
    ((measurable_fixedMassHaarCanonicalFlowPosition
      shell m radius hzero).comp hreparametrize)

/-- A fixed Physlib-time section of the ambient position path is measurable
in the Haar phase. -/
theorem measurable_fixedMassHaarCanonicalPhyslibPosition_at
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (t : Time) :
    Measurable (fun phase : UnitAddTorus (Lattice.Site N) ↦
      fixedMassHaarCanonicalPhyslibPosition shell m radius hzero phase t) := by
  have hpaths := measurable_fixedMassHaarCanonicalPhyslibPaths
    shell m radius hzero
  exact ((hpaths.comp (measurable_id.prodMk measurable_const)).snd)

/-- A fixed Physlib-time section of the ambient momentum path is measurable
in the Haar phase. -/
theorem measurable_fixedMassHaarCanonicalPhyslibMomentum_at
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (t : Time) :
    Measurable (fun phase : UnitAddTorus (Lattice.Site N) ↦
      fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero phase t) := by
  have hpaths := measurable_fixedMassHaarCanonicalPhyslibPaths
    shell m radius hzero
  exact ((hpaths.comp (measurable_id.prodMk measurable_const)).fst)

@[simp] theorem realReparametrize_fixedMassHaarCanonicalPhyslibPosition
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    realReparametrize
        (fixedMassHaarCanonicalPhyslibPosition shell m radius hzero phase) time =
      fixedMassHaarCanonicalFlowPosition shell m radius hzero (phase, time) := by
  unfold realReparametrize fixedMassHaarCanonicalPhyslibPosition
  rw [ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem realReparametrize_fixedMassHaarCanonicalPhyslibMomentum
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    realReparametrize
        (fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero phase) time =
      fixedMassHaarCanonicalFlowMomentum shell m radius hzero (phase, time) := by
  unfold realReparametrize fixedMassHaarCanonicalPhyslibMomentum
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The actual complex amplitude of any fixed mode and time is measurable in
the Haar phase for the canonical ambient flow. -/
theorem measurable_fixedMassHaarPhyslibModeAmplitude_at
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (observed : Lattice.Site N) (time : Real) :
    Measurable (fun phase : UnitAddTorus (Lattice.Site N) ↦
      physlibModeAmplitude m observed
        (fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero phase)
        (fixedMassHaarCanonicalPhyslibPosition shell m radius hzero phase)
        time) := by
  have hp : Measurable (fun phase : UnitAddTorus (Lattice.Site N) ↦
      fixedMassHaarCanonicalFlowMomentum shell m radius hzero
        (phase, time)) :=
    (measurable_fixedMassHaarCanonicalFlowMomentum
      shell m radius hzero).comp (measurable_id.prodMk measurable_const)
  have hq : Measurable (fun phase : UnitAddTorus (Lattice.Site N) ↦
      fixedMassHaarCanonicalFlowPosition shell m radius hzero
        (phase, time)) :=
    (measurable_fixedMassHaarCanonicalFlowPosition
      shell m radius hzero).comp (measurable_id.prodMk measurable_const)
  have hP : Measurable (fun phase : UnitAddTorus (Lattice.Site N) ↦
      modalCoordinates m
        (inverseSqrtMassTransform m
          (fixedMassHaarCanonicalFlowMomentum shell m radius hzero
            (phase, time))) observed) :=
    (PiLp.continuous_apply 2
      (fun _ : Lattice.Site N ↦ Real) observed).measurable.comp
      ((modalCoordinates m).continuous.measurable.comp
        ((inverseSqrtMassTransform m).continuous.measurable.comp hp))
  have hQ : Measurable (fun phase : UnitAddTorus (Lattice.Site N) ↦
      modalCoordinates m
        (sqrtMassTransform m
          (fixedMassHaarCanonicalFlowPosition shell m radius hzero
            (phase, time))) observed) :=
    (PiLp.continuous_apply 2
      (fun _ : Lattice.Site N ↦ Real) observed).measurable.comp
      ((modalCoordinates m).continuous.measurable.comp
        ((sqrtMassTransform m).continuous.measurable.comp hq))
  have hcomplex : Continuous (fun qp : Real × Real ↦
      complexModeAmplitude (modeFrequency m observed) qp.1 qp.2) := by
    unfold complexModeAmplitude
    fun_prop
  unfold physlibModeAmplitude physlibModePosition physlibModeMomentum
    massWeightedPosition massWeightedMomentum
  simp only [realReparametrize_fixedMassHaarCanonicalPhyslibPosition,
    realReparametrize_fixedMassHaarCanonicalPhyslibMomentum]
  exact hcomplex.measurable.comp (hQ.prodMk hP)

@[simp] theorem fixedMassHaarCanonicalPhyslibPosition_zero
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) :
    fixedMassHaarCanonicalPhyslibPosition shell m radius hzero phase 0 =
      fixedMassHaarPhysicalPosition m radius phase := by
  unfold fixedMassHaarCanonicalPhyslibPosition
    fixedMassHaarCanonicalFlowPosition sampledFlowPosition
  rw [show Time.toRealCLE (0 : Time) = 0 by
      exact map_zero Time.toRealCLE,
    canonicalRandomMassGlobalFlow_zero]
  rfl

@[simp] theorem fixedMassHaarCanonicalPhyslibMomentum_zero
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N)) :
    fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero phase 0 =
      fixedMassHaarPhysicalMomentum m radius phase := by
  unfold fixedMassHaarCanonicalPhyslibMomentum
    fixedMassHaarCanonicalFlowMomentum sampledFlowMomentum
  rw [show Time.toRealCLE (0 : Time) = 0 by
      exact map_zero Time.toRealCLE,
    canonicalRandomMassGlobalFlow_zero]
  rfl

/-- Every phase whose explicit initial state lies below the common energy
ceiling has a reduced trajectory witnessing that the measurable ambient paths
are differentiable and solve the exact Physlib Hamilton equations. -/
theorem exists_reducedTrajectory_matching_fixedMassHaarCanonicalPhyslibPaths
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (hmass : shell.MassAdmissible m)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (phase : UnitAddTorus (Lattice.Site N))
    (henergy : reducedHamiltonian m shell.kappa shell.beta shell.g
      (fixedMassHaarReducedInitialState m radius hzero phase) ≤ shell.H) :
    ∃ z : Real → ReducedPhaseSpace m,
      z 0 = fixedMassHaarReducedInitialState m radius hzero phase ∧
      (∀ time, HasDerivAt z
        (reducedVectorField m shell.kappa shell.beta shell.g (z time)) time) ∧
      (∀ time, canonicalRandomMassGlobalFlow shell
        (fixedMassHaarParametricInitial shell m radius hzero phase, time) =
          embedReducedPoint m shell.kappa shell.beta shell.g (z time)) ∧
      fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero phase =
        physlibMomentumPathOfReducedTrajectory z ∧
      fixedMassHaarCanonicalPhyslibPosition shell m radius hzero phase =
        physlibPositionPathOfReducedTrajectory z ∧
      Differentiable Real
        (fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero phase) ∧
      Differentiable Real
        (fixedMassHaarCanonicalPhyslibPosition shell m radius hzero phase) ∧
      SatisfiesHamiltonEquations m shell.kappa shell.beta shell.g
        (fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero phase)
        (fixedMassHaarCanonicalPhyslibPosition shell m radius hzero phase) ∧
      ∀ time, reducedHamiltonian m shell.kappa shell.beta shell.g (z time) =
        reducedHamiltonian m shell.kappa shell.beta shell.g
          (fixedMassHaarReducedInitialState m radius hzero phase) := by
  obtain ⟨z, hz0, hz, hmatch, _hbound, _hderiv, henergyConserved, _hjoint⟩ :=
    canonicalRandomMassGlobalFlow_matches_reduced shell m hmass
      (fixedMassHaarReducedInitialState m radius hzero phase) henergy
  have hpPath : fixedMassHaarCanonicalPhyslibMomentum
      shell m radius hzero phase = physlibMomentumPathOfReducedTrajectory z := by
    funext t
    have h := congrArg (fun x : ParametricPhaseSpace N ↦ x.2.2)
      (hmatch (Time.toRealCLE t))
    simpa [fixedMassHaarCanonicalPhyslibMomentum,
      fixedMassHaarCanonicalFlowMomentum, sampledFlowMomentum,
      fixedMassHaarParametricInitial, embedReducedPoint,
      physlibMomentumPathOfReducedTrajectory] using h
  have hqPath : fixedMassHaarCanonicalPhyslibPosition
      shell m radius hzero phase = physlibPositionPathOfReducedTrajectory z := by
    funext t
    have h := congrArg (fun x : ParametricPhaseSpace N ↦ x.2.1)
      (hmatch (Time.toRealCLE t))
    simpa [fixedMassHaarCanonicalPhyslibPosition,
      fixedMassHaarCanonicalFlowPosition, sampledFlowPosition,
      fixedMassHaarParametricInitial, embedReducedPoint,
      physlibPositionPathOfReducedTrajectory] using h
  have hp := differentiable_physlibMomentumPathOfReducedTrajectory
    m shell.kappa shell.beta shell.g z hz
  have hq := differentiable_physlibPositionPathOfReducedTrajectory
    m shell.kappa shell.beta shell.g z hz
  have hHamilton := satisfiesHamiltonEquations_physlibPathsOfReducedTrajectory
    m shell.kappa shell.beta shell.g z hz
  refine ⟨z, hz0, hz, hmatch, hpPath, hqPath, ?_, ?_, ?_, henergyConserved⟩
  · rw [hpPath]
    exact hp
  · rw [hqPath]
    exact hq
  · rw [hpPath, hqPath]
    exact hHamilton

end

end ArchonPhysics.FixedMassHaarReducedInitialFlowAdapter

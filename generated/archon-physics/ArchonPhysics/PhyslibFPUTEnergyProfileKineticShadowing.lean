import ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual

/-!
# Finite-dimensional FPUT energy-profile kinetic shadowing

The scalar kinetic interface loses information: the finite-time collision in
one observed mode depends on the complete modal-energy profile.  This module
keeps all positive-frequency modes at once.  Its collision map is the
canonical Haar broadening itself, converted from action to energy, so no
separate collision-compatibility field is needed.
-/

namespace ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

open Filter
open Topology
open ArchonPhysics
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation
open ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion

noncomputable section

/-- The finite set of genuine oscillatory modes.  The translation zero mode
is excluded from the complex-amplitude kinetic state. -/
abbrev PositiveFrequencyMode {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :=
  {mode : Lattice.Site N // 0 < modeFrequency m mode}

/-- A finite modal-energy profile on the positive-frequency modes.  Its Pi
norm is the finite-dimensional sup norm supplied by Mathlib. -/
abbrev PositiveEnergyProfile {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :=
  PositiveFrequencyMode m → Real

/-- Extend a positive-frequency profile to all modes, assigning zero energy
to the translation sector. -/
def extendPositiveEnergyProfile
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m) : Lattice.Site N → Real :=
  fun mode ↦ if h : 0 < modeFrequency m mode then energy ⟨mode, h⟩ else 0

@[simp] theorem extendPositiveEnergyProfile_apply
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m)
    (mode : PositiveFrequencyMode m) :
    extendPositiveEnergyProfile m energy mode = energy mode := by
  simp [extendPositiveEnergyProfile, mode.property]

/-- The canonical finite-time Haar collision field on the complete positive
modal-energy profile.  This is a definition, not a supplied kinetic closure. -/
def canonicalHaarEnergyCollision
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real) :
    PositiveEnergyProfile m → PositiveEnergyProfile m :=
  fun energy mode ↦
    modeFrequency m mode *
      normalizedSecondOrderHaarBroadening m kappa beta
        (extendPositiveEnergyProfile m energy) mode T

@[simp] theorem canonicalHaarEnergyCollision_apply
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real)
    (energy : PositiveEnergyProfile m)
    (mode : PositiveFrequencyMode m) :
    canonicalHaarEnergyCollision m kappa beta T energy mode =
      modeFrequency m mode *
        normalizedSecondOrderHaarBroadening m kappa beta
          (extendPositiveEnergyProfile m energy) mode T := by
  rfl

/-- The initial Haar action moment is exactly prescribed energy divided by
frequency. -/
theorem canonicalHaarInitialMoment_eq_modeAction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N)
    (henergy : 0 ≤ energy observed)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceInitialHaarMoment m
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      modeAction energy (modeFrequency m) observed := by
  rw [physlibReferenceInitialHaarMoment_eq_sameChargeFamilySquare
    m (phaseEnergyRadius energy (modeFrequency m)) observed homega]
  classical
  unfold sameChargeFamilySquare equalChargeCrossPairSum
    freeInitialPhaseCoefficient phaseEnergyRadius modeAction
  simp only [Fin.sum_univ_one, if_pos, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.conj_ofReal]
  have hsqrtOmega : Real.sqrt (2 * modeFrequency m observed) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two homega)
  field_simp [homega.ne', hsqrtOmega]
  rw [Real.sq_sqrt (mul_nonneg zero_le_two henergy)]
  have hsquareOmega :
      Real.sqrt (modeFrequency m observed * 2) ^ 2 =
        modeFrequency m observed * 2 :=
    Real.sq_sqrt (mul_nonneg homega.le zero_le_two)
  rw [hsquareOmega]
  ring

/-! ## Sup-norm kinetic Euler interface -/

/-- One finite-dimensional energy-profile Euler residual, measured in the
Pi sup norm. -/
def EnergyProfileKineticEulerResidual
    {mode : Type*} [Fintype mode]
    (initial final : mode → Real) (step : Real)
    (collision : mode → Real) (defect : Real) : Prop :=
  ‖final - initial - step • collision‖ ≤ defect

/-- Discrete kinetic Euler evolution of the complete modal-energy profile. -/
def IsEnergyProfileKineticEulerTrajectory
    {mode : Type*} [Fintype mode]
    (V : Nat → mode → Real) (step : Real)
    (Q : (mode → Real) → mode → Real) : Prop :=
  ∀ j, V (j + 1) = V j + step • Q (V j)

/-- Endpoint transfer for a vector collision field.  It is the exact
sup-norm analogue of the scalar restart lemma. -/
theorem energyProfileResidual_of_reference_endpoint_control
    {mode : Type*} [Fintype mode]
    (actualInitial actualFinal referenceInitial referenceFinal : mode → Real)
    (Q : (mode → Real) → mode → Real)
    {step L referenceDefect initialEndpointDefect finalEndpointDefect : Real}
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (hreference : EnergyProfileKineticEulerResidual
      referenceInitial referenceFinal step (Q referenceInitial)
        referenceDefect)
    (hinitial : ‖actualInitial - referenceInitial‖ ≤ initialEndpointDefect)
    (hfinal : ‖actualFinal - referenceFinal‖ ≤ finalEndpointDefect)
    (hQ : ∀ x y, ‖Q x - Q y‖ ≤ L * ‖x - y‖) :
    EnergyProfileKineticEulerResidual actualInitial actualFinal step
      (Q actualInitial)
      (referenceDefect + finalEndpointDefect +
        (1 + step * L) * initialEndpointDefect) := by
  have hQinitial :
      ‖Q referenceInitial - Q actualInitial‖ ≤
        L * initialEndpointDefect := by
    calc
      ‖Q referenceInitial - Q actualInitial‖ ≤
          L * ‖referenceInitial - actualInitial‖ :=
        hQ referenceInitial actualInitial
      _ = L * ‖actualInitial - referenceInitial‖ := by
        rw [norm_sub_rev]
      _ ≤ L * initialEndpointDefect :=
        mul_le_mul_of_nonneg_left hinitial hL
  have hcollision :
      ‖step • (Q referenceInitial - Q actualInitial)‖ ≤
        step * (L * initialEndpointDefect) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hstep]
    exact mul_le_mul_of_nonneg_left hQinitial hstep
  have hidentity :
      actualFinal - actualInitial - step • Q actualInitial =
        (referenceFinal - referenceInitial - step • Q referenceInitial) +
          ((actualFinal - referenceFinal) +
            ((referenceInitial - actualInitial) +
              step • (Q referenceInitial - Q actualInitial))) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold EnergyProfileKineticEulerResidual at hreference ⊢
  rw [hidentity]
  calc
    ‖(referenceFinal - referenceInitial - step • Q referenceInitial) +
        ((actualFinal - referenceFinal) +
          ((referenceInitial - actualInitial) +
            step • (Q referenceInitial - Q actualInitial)))‖ ≤
        ‖referenceFinal - referenceInitial - step • Q referenceInitial‖ +
          ‖(actualFinal - referenceFinal) +
            ((referenceInitial - actualInitial) +
              step • (Q referenceInitial - Q actualInitial))‖ :=
      norm_add_le _ _
    _ ≤ ‖referenceFinal - referenceInitial - step • Q referenceInitial‖ +
          (‖actualFinal - referenceFinal‖ +
            ‖(referenceInitial - actualInitial) +
              step • (Q referenceInitial - Q actualInitial)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖referenceFinal - referenceInitial - step • Q referenceInitial‖ +
          (‖actualFinal - referenceFinal‖ +
            (‖referenceInitial - actualInitial‖ +
              ‖step • (Q referenceInitial - Q actualInitial)‖)) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ referenceDefect +
          (finalEndpointDefect +
            (initialEndpointDefect + step * (L * initialEndpointDefect))) := by
      exact add_le_add hreference
        (add_le_add hfinal
          (add_le_add (by simpa only [norm_sub_rev] using hinitial)
            hcollision))
    _ = referenceDefect + finalEndpointDefect +
          (1 + step * L) * initialEndpointDefect := by ring

/-- A microscopic profile residual and a sup-norm Lipschitz collision field
give the usual affine error recurrence. -/
theorem norm_energyProfile_sub_kinetic_next_le
    {mode : Type*} [Fintype mode]
    (E V : Nat → mode → Real)
    (Q : (mode → Real) → mode → Real)
    (step L : Real) (defect : Nat → Real)
    (hstep : 0 ≤ step)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V step Q)
    (hresidual : ∀ j, EnergyProfileKineticEulerResidual
      (E j) (E (j + 1)) step (Q (E j)) (defect j))
    (hQ : ∀ x y, ‖Q x - Q y‖ ≤ L * ‖x - y‖)
    (j : Nat) :
    ‖E (j + 1) - V (j + 1)‖ ≤
      (1 + L * step) * ‖E j - V j‖ + defect j := by
  have hdecomposition :
      E (j + 1) - V (j + 1) =
        (E (j + 1) - E j - step • Q (E j)) +
          ((E j - V j) + step • (Q (E j) - Q (V j))) := by
    rw [hkinetic j]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdecomposition]
  calc
    ‖(E (j + 1) - E j - step • Q (E j)) +
        ((E j - V j) + step • (Q (E j) - Q (V j)))‖ ≤
        ‖E (j + 1) - E j - step • Q (E j)‖ +
          ‖(E j - V j) + step • (Q (E j) - Q (V j))‖ :=
      norm_add_le _ _
    _ ≤ defect j +
          (‖E j - V j‖ + ‖step • (Q (E j) - Q (V j))‖) := by
      gcongr
      · exact hresidual j
      · exact norm_add_le _ _
    _ ≤ defect j +
          (‖E j - V j‖ + step * (L * ‖E j - V j‖)) := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hstep]
      exact mul_le_mul_of_nonneg_left (hQ (E j) (V j)) hstep
    _ = (1 + L * step) * ‖E j - V j‖ + defect j := by ring

/-- Finite-block sup-norm shadowing with a uniform profile residual. -/
theorem energyProfile_kineticEuler_shadowing_uniform_bound
    {mode : Type*} [Fintype mode]
    (E V : Nat → mode → Real)
    (Q : (mode → Real) → mode → Real)
    (step L defectMax : Real) (defect : Nat → Real)
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (hdefect : ∀ j, 0 ≤ defect j)
    (hdefectMax : ∀ j, defect j ≤ defectMax)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V step Q)
    (hresidual : ∀ j, EnergyProfileKineticEulerResidual
      (E j) (E (j + 1)) step (Q (E j)) (defect j))
    (hQ : ∀ x y, ‖Q x - Q y‖ ≤ L * ‖x - y‖)
    (K : Nat) :
    ‖E K - V K‖ ≤
      (‖E 0 - V 0‖ + (K : Real) * defectMax) *
        Real.exp (L * step * (K : Real)) := by
  apply discrete_affine_error_uniform_defect_bound
      (e := fun j ↦ ‖E j - V j‖) (defect := defect)
      (L := L) (h := step) (defectMax := defectMax)
  · exact norm_nonneg _
  · exact hL
  · exact hstep
  · exact hdefect
  · exact hdefectMax
  · exact fun j ↦ norm_energyProfile_sub_kinetic_next_le
      E V Q step L defect hstep hkinetic hresidual hQ j

/-! ## Canonical Haar reference blocks in energy variables -/

/-- Initial modal energy of one canonical Haar block. -/
def canonicalHaarEnergyBlockInitial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m) : PositiveEnergyProfile m :=
  fun mode ↦ modeFrequency m mode *
    physlibReferenceInitialHaarMoment m
      (phaseEnergyRadius (extendPositiveEnergyProfile m energy)
        (modeFrequency m)) mode

/-- Final modal energy of the canonical two-step Picard Haar block. -/
def canonicalHaarEnergyBlockFinal
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (energy : PositiveEnergyProfile m) (T : Real) :
    PositiveEnergyProfile m :=
  fun mode ↦ modeFrequency m mode *
    physlibReferenceTwoStepHaarMoment m kappa beta g
      (phaseEnergyRadius (extendPositiveEnergyProfile m energy)
        (modeFrequency m)) T mode

/-- On nonnegative profiles the canonical initial Haar energy is the supplied
profile itself.  Thus its collision field has no inverse-profile or scalar
compatibility assumption. -/
theorem canonicalHaarEnergyBlockInitial_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    canonicalHaarEnergyBlockInitial m energy = energy := by
  funext mode
  unfold canonicalHaarEnergyBlockInitial
  rw [canonicalHaarInitialMoment_eq_modeAction m
    (extendPositiveEnergyProfile m energy) mode
    (by simpa using henergy mode) mode.property]
  unfold modeAction
  rw [extendPositiveEnergyProfile_apply]
  field_simp [mode.property.ne']

/-- The complete reference block has a derived profile residual against the
definition-level canonical collision.  `Cref` is only a uniform finite-mode
coefficient envelope, not a kinetic closure assumption. -/
theorem canonicalHaarEnergyBlock_is_profileKineticEulerResidual
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g T Cref : Real)
    (energy : PositiveEnergyProfile m)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (hT : 0 < T) (hg : |g| ≤ 1) (hCrefNonneg : 0 ≤ Cref)
    (hCref : ∀ mode : PositiveFrequencyMode m,
      modeFrequency m mode *
        (physlibHaarEnergyDriftC3 m kappa beta
            (phaseEnergyRadius (extendPositiveEnergyProfile m energy)
              (modeFrequency m)) T mode +
          physlibHaarEnergyDriftC4 m kappa beta
            (phaseEnergyRadius (extendPositiveEnergyProfile m energy)
              (modeFrequency m)) T mode) ≤ Cref) :
    EnergyProfileKineticEulerResidual
      (canonicalHaarEnergyBlockInitial m energy)
      (canonicalHaarEnergyBlockFinal m kappa beta g energy T)
      (g ^ 2 * T)
      (canonicalHaarEnergyCollision m kappa beta T
        (canonicalHaarEnergyBlockInitial m energy))
      (Cref * |g| ^ 3) := by
  have hinitial := canonicalHaarEnergyBlockInitial_eq m energy henergy
  rw [hinitial]
  unfold EnergyProfileKineticEulerResidual
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg hCrefNonneg (pow_nonneg (abs_nonneg _) _))).2 ?_
  intro mode
  simp only [Pi.sub_apply, Pi.smul_apply, Real.norm_eq_abs, smul_eq_mul]
  let radius := phaseEnergyRadius (extendPositiveEnergyProfile m energy)
    (modeFrequency m)
  let A0 := physlibReferenceInitialHaarMoment m radius mode
  let A1 := physlibReferenceTwoStepHaarMoment m kappa beta g radius T mode
  let broadening := normalizedSecondOrderHaarBroadening m kappa beta
    (extendPositiveEnergyProfile m energy) mode T
  have href :
      |A1 - A0 - (g ^ 2 * T) * broadening| ≤
        physlibReferenceBlockKineticDefect m kappa beta radius T mode g := by
    exact physlibReferenceBlock_is_momentKineticEulerResidual
      m kappa beta g (extendPositiveEnergyProfile m energy) mode hT
        mode.property
  have hfixed :
      physlibReferenceBlockKineticDefect m kappa beta radius T mode g ≤
        |g| ^ 3 *
          (physlibHaarEnergyDriftC3 m kappa beta radius T mode +
            physlibHaarEnergyDriftC4 m kappa beta radius T mode) :=
    physlibReferenceBlockKineticDefect_le_abs_cube_mul_fixedEnvelope
      m kappa beta radius T mode hg
  have hinitMode : modeFrequency m mode * A0 = energy mode := by
    simpa only [canonicalHaarEnergyBlockInitial, radius, A0] using
      congrFun hinitial mode
  change
    |modeFrequency m mode * A1 - energy mode -
        (g ^ 2 * T) * (modeFrequency m mode * broadening)| ≤
      Cref * |g| ^ 3
  rw [← hinitMode]
  have hrewrite :
      modeFrequency m mode * A1 - modeFrequency m mode * A0 -
          (g ^ 2 * T) * (modeFrequency m mode * broadening) =
        modeFrequency m mode *
          (A1 - A0 - (g ^ 2 * T) * broadening) := by ring
  rw [hrewrite, abs_mul, abs_of_pos mode.property]
  calc
    modeFrequency m mode *
        |A1 - A0 - (g ^ 2 * T) * broadening| ≤
      modeFrequency m mode *
        (|g| ^ 3 *
          (physlibHaarEnergyDriftC3 m kappa beta radius T mode +
            physlibHaarEnergyDriftC4 m kappa beta radius T mode)) :=
      mul_le_mul_of_nonneg_left (href.trans hfixed) mode.property.le
    _ = |g| ^ 3 *
        (modeFrequency m mode *
          (physlibHaarEnergyDriftC3 m kappa beta radius T mode +
            physlibHaarEnergyDriftC4 m kappa beta radius T mode)) := by ring
    _ ≤ |g| ^ 3 * Cref := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [radius] using hCref mode
      · positivity
    _ = Cref * |g| ^ 3 := by ring

/-! ## Compatibility-free blockwise certificate -/

/-- A coherent actual energy-profile chain coupled blockwise to fresh
canonical Haar profiles.  The collision map is not a field: it is fixed to
`canonicalHaarEnergyCollision`.  Consequently there is no analogue of the
scalar `collision_compatibility` hypothesis. -/
structure FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real)
    (g : Nat → Real)
    (E : Nat → Nat → PositiveEnergyProfile m)
    (Cref Ccoupling : Real) where
  referenceEnergy : Nat → Nat → PositiveEnergyProfile m
  Cref_nonneg : 0 ≤ Cref
  Ccoupling_nonneg : 0 ≤ Ccoupling
  referenceEnergy_nonneg : ∀ n j mode,
    0 ≤ referenceEnergy n j mode
  couplingWindow : ∀ n, |g n| ≤ 1
  initial_endpoint_control : ∀ n j,
    ‖E n j - canonicalHaarEnergyBlockInitial m (referenceEnergy n j)‖ ≤
      Ccoupling * |g n| ^ 3
  final_endpoint_control : ∀ n j,
    ‖E n (j + 1) -
        canonicalHaarEnergyBlockFinal m kappa beta (g n)
          (referenceEnergy n j) T‖ ≤
      Ccoupling * |g n| ^ 3
  finiteCharacterEnergyEnvelope : ∀ n j (mode : PositiveFrequencyMode m),
    modeFrequency m mode *
        (physlibHaarEnergyDriftC3 m kappa beta
            (phaseEnergyRadius
              (extendPositiveEnergyProfile m (referenceEnergy n j))
              (modeFrequency m)) T mode +
          physlibHaarEnergyDriftC4 m kappa beta
            (phaseEnergyRadius
              (extendPositiveEnergyProfile m (referenceEnergy n j))
              (modeFrequency m)) T mode) ≤
      Cref

namespace FPUTCanonicalHaarEnergyProfileBlockwiseCertificate

variable {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {g : Nat → Real}
  {E : Nat → Nat → PositiveEnergyProfile m}
  {Cref Ccoupling : Real}

/-- Uniform actual profile-residual envelope after transferring both Haar
endpoints. -/
def actualResidualDefect
    (_certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (L : Real) (n : Nat) : Real :=
  Cref * |g n| ^ 3 + Ccoupling * |g n| ^ 3 +
    (1 + (g n ^ 2 * T) * L) * (Ccoupling * |g n| ^ 3)

/-- A coupling-independent cubic coefficient on the unit coupling window. -/
def kineticCubicConstant
    (_certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (L : Real) : Real :=
  Cref + (2 + T * L) * Ccoupling

theorem kineticCubicConstant_nonneg
    (certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (hT : 0 ≤ T) {L : Real} (hL : 0 ≤ L) :
    0 ≤ certificate.kineticCubicConstant L := by
  unfold kineticCubicConstant
  exact add_nonneg certificate.Cref_nonneg
    (mul_nonneg
      (add_nonneg (by norm_num) (mul_nonneg hT hL))
      certificate.Ccoupling_nonneg)

/-- On `|g|≤1`, the transferred actual residual is uniformly cubic with
coefficient `Cref + (2 + T L) Ccoupling`. -/
theorem actualResidualDefect_le_kineticCubicConstant_mul_abs_cube
    (certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (hT : 0 ≤ T) {L : Real} (hL : 0 ≤ L) (n : Nat) :
    certificate.actualResidualDefect L n ≤
      certificate.kineticCubicConstant L * |g n| ^ 3 := by
  have hg2 : g n ^ 2 ≤ 1 := by
    calc
      g n ^ 2 = |g n| * |g n| := by rw [← sq_abs]; ring
      _ ≤ 1 * 1 := mul_le_mul (certificate.couplingWindow n)
        (certificate.couplingWindow n) (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have hstepFactor : (g n ^ 2 * T) * L ≤ T * L := by
    exact mul_le_mul_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_right hg2 hT) hL
  have hcouplingCube : 0 ≤ Ccoupling * |g n| ^ 3 :=
    mul_nonneg certificate.Ccoupling_nonneg (by positivity)
  unfold actualResidualDefect kineticCubicConstant
  calc
    Cref * |g n| ^ 3 + Ccoupling * |g n| ^ 3 +
        (1 + (g n ^ 2 * T) * L) * (Ccoupling * |g n| ^ 3) ≤
      Cref * |g n| ^ 3 + Ccoupling * |g n| ^ 3 +
        (1 + T * L) * (Ccoupling * |g n| ^ 3) := by
      gcongr
    _ = (Cref + (2 + T * L) * Ccoupling) * |g n| ^ 3 := by
      ring

/-- The reference profile residual is derived simultaneously in every
positive mode. -/
theorem reference_is_profileKineticEulerResidual
    (certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (hT : 0 < T) (n j : Nat) :
    EnergyProfileKineticEulerResidual
      (canonicalHaarEnergyBlockInitial m (certificate.referenceEnergy n j))
      (canonicalHaarEnergyBlockFinal m kappa beta (g n)
        (certificate.referenceEnergy n j) T)
      (g n ^ 2 * T)
      (canonicalHaarEnergyCollision m kappa beta T
        (canonicalHaarEnergyBlockInitial m
          (certificate.referenceEnergy n j)))
      (Cref * |g n| ^ 3) := by
  exact canonicalHaarEnergyBlock_is_profileKineticEulerResidual
    m kappa beta (g n) T Cref (certificate.referenceEnergy n j)
      (certificate.referenceEnergy_nonneg n j) hT
      (certificate.couplingWindow n) certificate.Cref_nonneg
      (certificate.finiteCharacterEnergyEnvelope n j)

/-- The actual all-mode residual follows from profile endpoint coupling and
sup-norm Lipschitzness. -/
theorem actual_is_profileKineticEulerResidual
    (certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (hT : 0 < T) {L : Real} (hL : 0 ≤ L)
    (hQ : ∀ x y,
      ‖canonicalHaarEnergyCollision m kappa beta T x -
          canonicalHaarEnergyCollision m kappa beta T y‖ ≤
        L * ‖x - y‖)
    (n j : Nat) :
    EnergyProfileKineticEulerResidual
      (E n j) (E n (j + 1)) (g n ^ 2 * T)
      (canonicalHaarEnergyCollision m kappa beta T (E n j))
      (certificate.actualResidualDefect L n) := by
  exact energyProfileResidual_of_reference_endpoint_control
    (E n j) (E n (j + 1))
    (canonicalHaarEnergyBlockInitial m (certificate.referenceEnergy n j))
    (canonicalHaarEnergyBlockFinal m kappa beta (g n)
      (certificate.referenceEnergy n j) T)
    (canonicalHaarEnergyCollision m kappa beta T)
    (mul_nonneg (sq_nonneg _) hT.le) hL
    (certificate.reference_is_profileKineticEulerResidual hT n j)
    (certificate.initial_endpoint_control n j)
    (certificate.final_endpoint_control n j) hQ

/-- The displayed actual residual is nonnegative. -/
theorem actualResidualDefect_nonneg
    (certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (hT : 0 ≤ T) {L : Real} (hL : 0 ≤ L) (n : Nat) :
    0 ≤ certificate.actualResidualDefect L n := by
  unfold actualResidualDefect
  have href : 0 ≤ Cref * |g n| ^ 3 :=
    mul_nonneg certificate.Cref_nonneg (pow_nonneg (abs_nonneg _) _)
  have hcoupling : 0 ≤ Ccoupling * |g n| ^ 3 :=
    mul_nonneg certificate.Ccoupling_nonneg
      (pow_nonneg (abs_nonneg _) _)
  have hfactor : 0 ≤ 1 + (g n ^ 2 * T) * L :=
    add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (sq_nonneg _) hT) hL)
  exact add_nonneg (add_nonneg href hcoupling)
    (mul_nonneg hfactor hcoupling)

/-- Finite-block shadowing of the full positive-mode energy profile.  The
collision is fixed by `m,kappa,beta,T`; the only collision hypothesis is its
ordinary global sup-norm Lipschitz estimate.  For a genuinely quadratic
collision field, applications should replace it by the corresponding local
Lipschitz estimate on a proved invariant bounded-energy region. -/
theorem actual_energyProfile_kineticEuler_shadowing_uniform_bound
    (certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (hT : 0 < T) (L : Real) (hL : 0 ≤ L)
    (hQ : ∀ x y,
      ‖canonicalHaarEnergyCollision m kappa beta T x -
          canonicalHaarEnergyCollision m kappa beta T y‖ ≤
        L * ‖x - y‖)
    (n : Nat) (V : Nat → PositiveEnergyProfile m)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V
      (g n ^ 2 * T) (canonicalHaarEnergyCollision m kappa beta T))
    (K : Nat) :
    ‖E n K - V K‖ ≤
      (‖E n 0 - V 0‖ +
          (K : Real) * certificate.actualResidualDefect L n) *
        Real.exp (L * (g n ^ 2 * T) * (K : Real)) := by
  exact energyProfile_kineticEuler_shadowing_uniform_bound
    (E n) V (canonicalHaarEnergyCollision m kappa beta T)
      (g n ^ 2 * T) L (certificate.actualResidualDefect L n)
      (fun _ ↦ certificate.actualResidualDefect L n)
      (mul_nonneg (sq_nonneg _) hT.le) hL
      (fun _ ↦ certificate.actualResidualDefect_nonneg hT.le hL n)
      (fun _ ↦ le_rfl) hkinetic
      (fun j ↦ certificate.actual_is_profileKineticEulerResidual
        hT hL hQ n j)
      hQ K

/-- Explicit kinetic-time profile shadowing.  If
`(g² T) K ≤ tau`, the accumulated cubic block error is bounded by
`(tau / T) * (Cref + (2 + T L) Ccoupling) * |g|`, while the Lipschitz
amplification is at most `exp (L tau)`. -/
theorem actual_energyProfile_kineticTime_shadowing_bound
    (certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (hT : 0 < T) (L : Real) (hL : 0 ≤ L)
    (hQ : ∀ x y,
      ‖canonicalHaarEnergyCollision m kappa beta T x -
          canonicalHaarEnergyCollision m kappa beta T y‖ ≤
        L * ‖x - y‖)
    (n : Nat) (V : Nat → PositiveEnergyProfile m)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V
      (g n ^ 2 * T) (canonicalHaarEnergyCollision m kappa beta T))
    (K : Nat) (tau : Real)
    (hkineticBudget : (g n ^ 2 * T) * (K : Real) ≤ tau) :
    ‖E n K - V K‖ ≤
      (‖E n 0 - V 0‖ +
          (tau / T) * certificate.kineticCubicConstant L * |g n|) *
        Real.exp (L * tau) := by
  have hbase := certificate.actual_energyProfile_kineticEuler_shadowing_uniform_bound
    hT L hL hQ n V hkinetic K
  have hCtotal : 0 ≤ certificate.kineticCubicConstant L :=
    certificate.kineticCubicConstant_nonneg hT.le hL
  have hdefect :=
    certificate.actualResidualDefect_le_kineticCubicConstant_mul_abs_cube
      hT.le hL n
  have htau : 0 ≤ tau :=
    (mul_nonneg (mul_nonneg (sq_nonneg _) hT.le)
      (Nat.cast_nonneg _)).trans hkineticBudget
  have hcumulative :
      (K : Real) * certificate.actualResidualDefect L n ≤
        (tau / T) * certificate.kineticCubicConstant L * |g n| := by
    by_cases hgzero : g n = 0
    · simp [actualResidualDefect, hgzero]
    · have hratio :
          0 ≤ certificate.kineticCubicConstant L * |g n| / T :=
        div_nonneg (mul_nonneg hCtotal (abs_nonneg _)) hT.le
      calc
        (K : Real) * certificate.actualResidualDefect L n ≤
            (K : Real) *
              (certificate.kineticCubicConstant L * |g n| ^ 3) :=
          mul_le_mul_of_nonneg_left hdefect (Nat.cast_nonneg _)
        _ = ((g n ^ 2 * T) * (K : Real)) *
              (certificate.kineticCubicConstant L * |g n| / T) := by
          field_simp [hT.ne', hgzero]
          rw [sq_abs]
        _ ≤ tau *
              (certificate.kineticCubicConstant L * |g n| / T) :=
          mul_le_mul_of_nonneg_right hkineticBudget hratio
        _ = (tau / T) * certificate.kineticCubicConstant L * |g n| := by
          ring
  have hexponent :
      L * (g n ^ 2 * T) * (K : Real) ≤ L * tau := by
    calc
      L * (g n ^ 2 * T) * (K : Real) =
          L * ((g n ^ 2 * T) * (K : Real)) := by ring
      _ ≤ L * tau := mul_le_mul_of_nonneg_left hkineticBudget hL
  have hprefixNonneg :
      0 ≤ ‖E n 0 - V 0‖ +
        (tau / T) * certificate.kineticCubicConstant L * |g n| := by
    exact add_nonneg (norm_nonneg _)
      (mul_nonneg
        (mul_nonneg (div_nonneg htau hT.le) hCtotal)
        (abs_nonneg _))
  calc
    ‖E n K - V K‖ ≤
        (‖E n 0 - V 0‖ +
            (K : Real) * certificate.actualResidualDefect L n) *
          Real.exp (L * (g n ^ 2 * T) * (K : Real)) := hbase
    _ ≤ (‖E n 0 - V 0‖ +
            (tau / T) * certificate.kineticCubicConstant L * |g n|) *
          Real.exp (L * (g n ^ 2 * T) * (K : Real)) :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hcumulative)
        (Real.exp_pos _).le
    _ ≤ (‖E n 0 - V 0‖ +
            (tau / T) * certificate.kineticCubicConstant L * |g n|) *
          Real.exp (L * tau) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
        hprefixNonneg

end FPUTCanonicalHaarEnergyProfileBlockwiseCertificate

end

end ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

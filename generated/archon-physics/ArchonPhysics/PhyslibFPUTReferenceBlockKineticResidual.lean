import ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

/-!
# Reference FPUT block supplies its kinetic residual

The canonical Haar two-step Picard amplitude is the natural reference block
used in the coupling/restart argument.  This module proves, rather than
assumes, its scalar kinetic Euler residual.

The finite-character Haar algebra removes the order-one interference and
identifies the complete signed order-two coefficient with the finite-time
collision field.  The only terms left after subtracting the kinetic step are
the order-three `A1`--`A2` interference and the order-four `A2` square.  Their
existing coefficient-mass bounds give the explicit nonnegative defect

`|g|^3 * (C3 + |g| * C4)`.

At fixed finite volume and fixed positive block length this is
`o(g^2 T)`.  No nonlinear flow, restart/RPA certificate, kinetic equation, or
additional reference-residual hypothesis occurs in the result.
-/

namespace ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual

open Filter
open MeasureTheory
open Set
open Topology
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTActualOneBlockKineticConsistency
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-! ## Canonical reference moments -/

/-- Haar second moment of the canonical physical two-step Picard amplitude. -/
def physlibReferenceTwoStepHaarMoment
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) : Real :=
  ∫ phase : UnitAddTorus (Lattice.Site N),
    Complex.normSq
      (twoStepPerturbedAmplitude g
        (canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
        (physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time observed)
        (physlibFPUTSecondPicardCoefficient
          m kappa beta observed radius phase time))
    ∂finitePhaseHaarLaw (Lattice.Site N)

/-- Haar second moment of the free canonical initial amplitude. -/
def physlibReferenceInitialHaarMoment
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (observed : Lattice.Site N) : Real :=
  ∫ phase : UnitAddTorus (Lattice.Site N),
    Complex.normSq
      (canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) phase observed)
    ∂finitePhaseHaarLaw (Lattice.Site N)

/-- The literal Haar integral of the physical two-step reference amplitude
is exactly the previously constructed finite matched-charge polynomial. -/
theorem physlibReferenceTwoStepHaarMoment_eq_matchedCharge
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceTwoStepHaarMoment
        m kappa beta g radius time observed =
      physlibMatchedChargeTwoStepMoment
        m kappa beta g radius time observed := by
  unfold physlibReferenceTwoStepHaarMoment
  calc
    _ = ∫ phase : UnitAddTorus (Lattice.Site N),
        Complex.normSq
          (finiteCharacterFamilyTwoStepAmplitude g
            (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
            (freeInitialPhaseCharge observed)
            (physlibQuadraticFirstPicardCharacterCoefficient
              m kappa radius time observed)
            quadraticPhaseCharge
            (completeSecondPicardCoefficient
              m kappa beta radius observed time)
            completeSecondPicardCharge phase)
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        dsimp only
        rw [physlibTwoStepAmplitude_eq_finiteCharacterFamily
          m kappa beta g radius phase time observed homega]
    _ = _ := integral_normSq_finiteCharacterFamilyTwoStepAmplitude
      g
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
      (freeInitialPhaseCharge observed)
      (physlibQuadraticFirstPicardCharacterCoefficient
        m kappa radius time observed)
      quadraticPhaseCharge
      (completeSecondPicardCoefficient
        m kappa beta radius observed time)
      completeSecondPicardCharge

/-- The reference initial Haar moment is the complete same-charge `A0`
square. -/
theorem physlibReferenceInitialHaarMoment_eq_sameChargeFamilySquare
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceInitialHaarMoment m radius observed =
      sameChargeFamilySquare
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed) := by
  exact integral_canonicalFreeInitial_normSq_eq_sameChargeFamilySquare
    m radius observed homega

/-! ## Exact residual and its finite coefficient envelope -/

/-- The explicit nonnegative residual envelope for one reference block. -/
def physlibReferenceBlockKineticDefect
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (g : Real) : Real :=
  g ^ 2 *
    (|g| * physlibHaarEnergyDriftC3
        m kappa beta radius time observed +
      g ^ 2 * physlibHaarEnergyDriftC4
        m kappa beta radius time observed)

/-- Unit cubic envelope; its only `g` dependence is the harmless quartic
correction `|g| * C4`. -/
def physlibReferenceBlockCubicUnitEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (g : Real) : Real :=
  physlibHaarEnergyDriftC3 m kappa beta radius time observed +
    |g| * physlibHaarEnergyDriftC4
      m kappa beta radius time observed

theorem physlibReferenceBlockKineticDefect_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (g : Real) :
    0 ≤ physlibReferenceBlockKineticDefect
      m kappa beta radius time observed g := by
  unfold physlibReferenceBlockKineticDefect
  exact mul_nonneg (sq_nonneg g)
    (add_nonneg
      (mul_nonneg (abs_nonneg g)
        (physlibHaarEnergyDriftC3_nonneg
          m kappa beta radius time observed))
      (mul_nonneg (sq_nonneg g)
        (physlibHaarEnergyDriftC4_nonneg
          m kappa beta radius time observed)))

/-- Exact conversion of the `g^3 + g^4` bound into a cubic factor times a
locally bounded unit envelope. -/
theorem physlibReferenceBlockKineticDefect_eq_abs_cube_mul_unitEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (g : Real) :
    physlibReferenceBlockKineticDefect
        m kappa beta radius time observed g =
      |g| ^ 3 * physlibReferenceBlockCubicUnitEnvelope
        m kappa beta radius time observed g := by
  unfold physlibReferenceBlockKineticDefect
    physlibReferenceBlockCubicUnitEnvelope
  rw [show |g| ^ 3 = g ^ 2 * |g| by
    rw [← sq_abs]
    ring]
  rw [← sq_abs]
  ring

/-- On the unit coupling window the cubic envelope is bounded by the fixed
finite coefficient mass `C3 + C4`. -/
theorem physlibReferenceBlockKineticDefect_le_abs_cube_mul_fixedEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) {g : Real} (hg : |g| ≤ 1) :
    physlibReferenceBlockKineticDefect
        m kappa beta radius time observed g ≤
      |g| ^ 3 *
        (physlibHaarEnergyDriftC3 m kappa beta radius time observed +
          physlibHaarEnergyDriftC4 m kappa beta radius time observed) := by
  rw [physlibReferenceBlockKineticDefect_eq_abs_cube_mul_unitEnvelope]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold physlibReferenceBlockCubicUnitEnvelope
  have hC4 := physlibHaarEnergyDriftC4_nonneg
    m kappa beta radius time observed
  nlinarith

/-- Exact remainder identity after subtracting the signed order-two
coefficient from the canonical reference moment increment. -/
theorem physlibReferenceBlock_sub_kineticCoefficient_eq_highOrder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceTwoStepHaarMoment
          m kappa beta g radius time observed -
        physlibReferenceInitialHaarMoment m radius observed -
        g ^ 2 * physlibHaarFiniteTimeKineticCoefficient
          m kappa beta radius time observed =
      g ^ 3 * equalChargeFamilyInterference
          (physlibQuadraticFirstPicardCharacterCoefficient
            m kappa radius time observed)
          quadraticPhaseCharge
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge +
        g ^ 4 * sameChargeFamilySquare
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge := by
  rw [physlibReferenceTwoStepHaarMoment_eq_matchedCharge
      m kappa beta g radius time observed homega,
    physlibReferenceInitialHaarMoment_eq_sameChargeFamilySquare
      m radius observed homega,
    physlibMatchedChargeTwoStepMoment_eq_without_firstOrder]
  unfold physlibHaarFiniteTimeKineticCoefficient
  ring

/-- The reference-block increment has a fully derived residual bound.  The
right side contains exactly the bounded `A1`--`A2` and `A2`--`A2` terms. -/
theorem abs_physlibReferenceBlock_sub_kineticCoefficient_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    |physlibReferenceTwoStepHaarMoment
          m kappa beta g radius time observed -
        physlibReferenceInitialHaarMoment m radius observed -
        g ^ 2 * physlibHaarFiniteTimeKineticCoefficient
          m kappa beta radius time observed| ≤
      physlibReferenceBlockKineticDefect
        m kappa beta radius time observed g := by
  let S3 := equalChargeFamilyInterference
    (physlibQuadraticFirstPicardCharacterCoefficient
      m kappa radius time observed)
    quadraticPhaseCharge
    (completeSecondPicardCoefficient
      m kappa beta radius observed time)
    completeSecondPicardCharge
  let S4 := sameChargeFamilySquare
    (completeSecondPicardCoefficient
      m kappa beta radius observed time)
    completeSecondPicardCharge
  have hS3 : |S3| ≤
      physlibHaarEnergyDriftC3 m kappa beta radius time observed := by
    dsimp only [S3]
    simpa [physlibHaarEnergyDriftC3, physlibA1CoefficientAbsMass,
      physlibA2CoefficientAbsMass] using
      (abs_equalChargeFamilyInterference_le_two_mul_absMass
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed)
        quadraticPhaseCharge
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge)
  have hS4 : |S4| ≤
      physlibHaarEnergyDriftC4 m kappa beta radius time observed := by
    dsimp only [S4]
    simpa [physlibHaarEnergyDriftC4, physlibA2CoefficientAbsMass] using
      (abs_sameChargeFamilySquare_le_absMass_sq
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge)
  rw [physlibReferenceBlock_sub_kineticCoefficient_eq_highOrder
    m kappa beta g radius time observed homega]
  change |g ^ 3 * S3 + g ^ 4 * S4| ≤ _
  have hg3 : |g ^ 3| = g ^ 2 * |g| := by
    rw [abs_pow]
    rw [show |g| ^ 3 = |g| ^ 2 * |g| by ring, sq_abs]
  have hg4 : |g ^ 4| = g ^ 4 := abs_of_nonneg (by positivity)
  calc
    |g ^ 3 * S3 + g ^ 4 * S4| ≤
        |g ^ 3 * S3| + |g ^ 4 * S4| := abs_add_le _ _
    _ = (g ^ 2 * |g|) * |S3| + g ^ 4 * |S4| := by
      rw [abs_mul, abs_mul, hg3, hg4]
    _ ≤ (g ^ 2 * |g|) *
          physlibHaarEnergyDriftC3 m kappa beta radius time observed +
        g ^ 4 * physlibHaarEnergyDriftC4
          m kappa beta radius time observed := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hS3
          (mul_nonneg (sq_nonneg g) (abs_nonneg g)))
        (mul_le_mul_of_nonneg_left hS4 (by positivity))
    _ = physlibReferenceBlockKineticDefect
        m kappa beta radius time observed g := by
      unfold physlibReferenceBlockKineticDefect
      ring

/-! ## Kinetic Euler residual and little-o consistency -/

/-- With the energy-radius parametrization, the reference block supplies
the exact scalar interface required by kinetic Euler shadowing. -/
theorem physlibReferenceBlock_is_momentKineticEulerResidual
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {T : Real} (hT : 0 < T)
    (homega : 0 < modeFrequency m observed) :
    MomentKineticEulerResidual
      (physlibReferenceInitialHaarMoment m
        (phaseEnergyRadius energy (modeFrequency m)) observed)
      (physlibReferenceTwoStepHaarMoment m kappa beta g
        (phaseEnergyRadius energy (modeFrequency m)) T observed)
      (g ^ 2 * T)
      (normalizedSecondOrderHaarBroadening
        m kappa beta energy observed T)
      (physlibReferenceBlockKineticDefect m kappa beta
        (phaseEnergyRadius energy (modeFrequency m)) T observed g) := by
  unfold MomentKineticEulerResidual
  rw [mul_assoc,
    ← physlibHaarFiniteTimeKineticCoefficient_eq_time_mul_broadening
      m kappa beta energy observed hT homega]
  exact abs_physlibReferenceBlock_sub_kineticCoefficient_le
    m kappa beta g (phaseEnergyRadius energy (modeFrequency m)) T
      observed homega

/-- At fixed finite volume and positive block length, the explicit reference
residual divided by `g^2 T` tends to zero through nonzero couplings. -/
theorem physlibReferenceBlockKineticDefect_div_kineticScale_tendsto_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) {T : Real} (hT : 0 < T)
    (observed : Lattice.Site N) :
    Tendsto
      (fun g : Real ↦
        physlibReferenceBlockKineticDefect
          m kappa beta radius T observed g / (g ^ 2 * T))
      (nhdsWithin 0 ({0} : Set Real)ᶜ) (nhds 0) := by
  let C3 := physlibHaarEnergyDriftC3 m kappa beta radius T observed
  let C4 := physlibHaarEnergyDriftC4 m kappa beta radius T observed
  have hcontinuous : ContinuousAt
      (fun g : Real ↦ (|g| * C3 + g ^ 2 * C4) / T) 0 := by
    fun_prop
  have hlimit : Tendsto
      (fun g : Real ↦ (|g| * C3 + g ^ 2 * C4) / T)
      (nhdsWithin 0 ({0} : Set Real)ᶜ) (nhds 0) := by
    simpa only [abs_zero, zero_mul, zero_pow (by norm_num : (2 : Nat) ≠ 0),
      add_zero, zero_div] using
        hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  apply (tendsto_congr' ?_).mpr hlimit
  filter_upwards [self_mem_nhdsWithin] with g hg
  have hg0 : g ≠ 0 := by simpa using hg
  dsimp only [physlibReferenceBlockKineticDefect, C3, C4]
  field_simp [hg0, hT.ne']

/-- Sequential form consumed by kinetic-time block accumulation. -/
theorem physlibReferenceBlockKineticDefect_sequence_div_kineticScale_tendsto_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) {T : Real} (hT : 0 < T)
    (observed : Lattice.Site N)
    (g : Nat → Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0) :
    Tendsto
      (fun n ↦
        physlibReferenceBlockKineticDefect
          m kappa beta radius T observed (g n) / (g n ^ 2 * T))
      atTop (nhds 0) := by
  apply
    (physlibReferenceBlockKineticDefect_div_kineticScale_tendsto_zero
      m kappa beta radius hT observed).comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨hg, by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hg0⟩

end

end ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual

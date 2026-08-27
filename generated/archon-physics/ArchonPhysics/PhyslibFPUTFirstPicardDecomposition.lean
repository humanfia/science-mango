import ArchonPhysics.PhyslibHamiltonDuhamel
import ArchonPhysics.FreeFPUTDuhamelResonanceBridge

/-!
# Exact first-Picard decomposition of the Physlib FPUT Duhamel source

For an actual differentiable Physlib Hamilton trajectory, this module splits
the interaction-picture source into three exact pieces:

1. the quadratic source evaluated on a freely rotating reference orbit;
2. the difference between the actual and free quadratic histories;
3. the cubic source evaluated on the actual trajectory.

The free quadratic piece is exactly
`freeQuadraticInteractionPictureCorrection`, with frequency
`modeFrequency m` and physical coupling

`forcedModeSource (modeFrequency m observed) (-(kappa * g))`.

Thus its sign and `sqrt (2 * omega)` normalization are inherited from the
verified Physlib modal equation rather than postulated.  The reference
`radius` and `phase` are explicit parameters; applications should choose them
from the physical initial data.  The identity itself is valid for every such
reference, with any mismatch absorbed exactly by the history remainder.

Everything below is finite-volume deterministic algebra and calculus.  No
RPA, kinetic equation, stochastic closure, or limiting assertion is assumed.
-/

namespace ArchonPhysics.PhyslibFPUTFirstPicardDecomposition

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- The physical quadratic coupling in the complex-amplitude convention.
Unfolding `forcedModeSource` gives
`I * (-(kappa * g) : Complex) / sqrt (2 * omega)`. -/
def physlibQuadraticCoupling {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N) : Complex :=
  forcedModeSource (modeFrequency m observed) (-(kappa * g))

/-- The actual quadratic part of the rotated Physlib source. -/
def physlibQuadraticRotatedSource {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N) : Real → Complex :=
  physlibModeRotatedSource m kappa 0 g observed q

/-- The actual cubic part of the rotated Physlib source. -/
def physlibCubicRotatedSource {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N) : Real → Complex :=
  physlibModeRotatedSource m 0 beta g observed q

/-- The freely evaluated quadratic source with the exact physical coupling
and the actual Physlib normal-mode frequencies. -/
def physlibFreeQuadraticRotatedSource {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Real → Complex :=
  fun time ↦
    freeQuadraticPicardIntegrand
      (physlibQuadraticCoupling m kappa g observed *
        phaseFactor (modeFrequency m observed * time))
      m observed radius (modeFrequency m) time phase

/-- The quadratic history defect: actual quadratic source minus the same
source evaluated on the freely rotating reference history. -/
def physlibQuadraticHistoryDifference {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Real → Complex :=
  fun time ↦
    physlibQuadraticRotatedSource m kappa g observed q time -
      physlibFreeQuadraticRotatedSource
        m kappa g observed radius phase time

/-- Difference between the actual and freely rotating quadratic tensor
contractions before applying the physical force coupling and output phase. -/
def physlibQuadraticTensorHistoryDifference {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Real :=
  distinguishedTensorContraction m
      (modalCoordinates m
        (massWeightedPosition m (realReparametrize q) time)) observed 2 -
    distinguishedTensorContraction m
      (freeWeightedConfiguration radius (modeFrequency m) time phase)
      observed 2

/-- The quadratic history defect is the rotated forced-mode image of the
difference between the actual and free quadratic tensor contractions.  This
form is the exact starting point for a later nonlinear-history estimate. -/
theorem physlibQuadraticHistoryDifference_eq_tensorDifference
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibQuadraticHistoryDifference
        m kappa g observed q radius phase time =
      phaseFactor (modeFrequency m observed * time) *
        forcedModeSource (modeFrequency m observed)
          (-(kappa * g * physlibQuadraticTensorHistoryDifference
            m observed q radius phase time)) := by
  unfold physlibQuadraticHistoryDifference
    physlibQuadraticTensorHistoryDifference
    physlibQuadraticRotatedSource physlibModeRotatedSource
    physlibModeTensorForce tensorNonlinearForce
    physlibFreeQuadraticRotatedSource freeQuadraticPicardIntegrand
    physlibQuadraticCoupling forcedModeSource
  rw [freeQuadraticTensorSource_eq_complex_tensorContraction]
  push_cast
  ring

/-- Exact size of the quadratic history source.  The interaction-picture
phase has unit norm, so all growth must come from the tensor-history defect
and the physical coupling. -/
theorem norm_physlibQuadraticHistoryDifference
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    ‖physlibQuadraticHistoryDifference
        m kappa g observed q radius phase time‖ =
      |kappa * g * physlibQuadraticTensorHistoryDifference
        m observed q radius phase time| /
        Real.sqrt (2 * modeFrequency m observed) := by
  rw [physlibQuadraticHistoryDifference_eq_tensorDifference,
    norm_mul, norm_phaseFactor, one_mul]
  unfold forcedModeSource
  have hsqrt : 0 ≤ Real.sqrt (2 * modeFrequency m observed) :=
    Real.sqrt_nonneg _
  simp only [norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, one_mul, abs_neg, abs_of_nonneg hsqrt]

/-- The full true rotated source is exactly its quadratic plus cubic parts. -/
theorem physlibModeRotatedSource_eq_quadratic_add_cubic
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N) (time : Real) :
    physlibModeRotatedSource m kappa beta g observed q time =
      physlibQuadraticRotatedSource m kappa g observed q time +
        physlibCubicRotatedSource m beta g observed q time := by
  unfold physlibQuadraticRotatedSource physlibCubicRotatedSource
    physlibModeRotatedSource physlibModeTensorForce tensorNonlinearForce
    forcedModeSource
  push_cast
  ring

/-- Exact pointwise three-part split of the actual interaction-picture
source.  The second term is an identity remainder, not an assumed estimate. -/
theorem physlibModeRotatedSource_eq_freeQuadratic_add_history_add_cubic
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibModeRotatedSource m kappa beta g observed q time =
      physlibFreeQuadraticRotatedSource
          m kappa g observed radius phase time +
        physlibQuadraticHistoryDifference
          m kappa g observed q radius phase time +
        physlibCubicRotatedSource m beta g observed q time := by
  rw [physlibModeRotatedSource_eq_quadratic_add_cubic]
  unfold physlibQuadraticHistoryDifference
  ring

/-- The integrated free source is definitionally the existing free
quadratic interaction-picture first-Picard correction. -/
theorem intervalIntegral_physlibFreeQuadraticRotatedSource_eq_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    (∫ s in (0 : Real)..time,
      physlibFreeQuadraticRotatedSource
        m kappa g observed radius phase s) =
      freeQuadraticInteractionPictureCorrection
        (physlibQuadraticCoupling m kappa g observed)
        m observed radius (modeFrequency m) time phase := rfl

/-- The free quadratic rotated source is continuous.  This is obtained from
its already verified finite mismatch-exponential expansion. -/
theorem continuous_physlibFreeQuadraticRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    Continuous (physlibFreeQuadraticRotatedSource
      m kappa g observed radius phase) := by
  let coupling := physlibQuadraticCoupling m kappa g observed
  have hcontinuous : Continuous (fun time : Real ↦
      ∑ term : QuadraticPhaseTerm N,
        (coupling * quadraticPhaseCoefficient m observed radius term *
          mFourier (quadraticPhaseCharge term) phase) *
          Complex.exp
            ((Complex.I *
              (quadraticPhaseMismatch (modeFrequency m) observed term : Real)) *
              time)) := by
    fun_prop
  apply hcontinuous.congr
  intro time
  symm
  exact freeQuadraticPicardIntegrand_eq_mismatchSum
    coupling m observed radius (modeFrequency m) time phase

/-- The three exact pieces are integrable on every finite interval along a
differentiable physical configuration path. -/
theorem intervalIntegrable_physlibPicardPieces
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N) (hq : Differentiable Real q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (a b : Real) :
    IntervalIntegrable
        (physlibFreeQuadraticRotatedSource
          m kappa g observed radius phase)
        MeasureTheory.volume a b ∧
      IntervalIntegrable
        (physlibQuadraticHistoryDifference
          m kappa g observed q radius phase)
        MeasureTheory.volume a b ∧
      IntervalIntegrable
        (physlibCubicRotatedSource m beta g observed q)
        MeasureTheory.volume a b := by
  have hfree := (continuous_physlibFreeQuadraticRotatedSource
    m kappa g observed radius phase).intervalIntegrable
      (μ := MeasureTheory.volume) a b
  have hquadratic := intervalIntegrable_physlibModeRotatedSource
    m kappa 0 g observed q hq a b
  have hcubic := intervalIntegrable_physlibModeRotatedSource
    m 0 beta g observed q hq a b
  exact ⟨hfree, hquadratic.sub hfree, hcubic⟩

/-- Exact decomposition of the true Physlib Duhamel integral into the
physical free first-Picard correction, the quadratic history difference, and
the actual cubic-force remainder. -/
theorem intervalIntegral_physlibModeRotatedSource_eq_firstPicard_add_remainders
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N) (hq : Differentiable Real q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    (∫ s in (0 : Real)..time,
      physlibModeRotatedSource m kappa beta g observed q s) =
      freeQuadraticInteractionPictureCorrection
          (physlibQuadraticCoupling m kappa g observed)
          m observed radius (modeFrequency m) time phase +
        (∫ s in (0 : Real)..time,
          physlibQuadraticHistoryDifference
            m kappa g observed q radius phase s) +
        (∫ s in (0 : Real)..time,
          physlibCubicRotatedSource m beta g observed q s) := by
  obtain ⟨hfree, hhistory, hcubic⟩ :=
    intervalIntegrable_physlibPicardPieces
      m kappa beta g observed q hq radius phase 0 time
  calc
    (∫ s in (0 : Real)..time,
      physlibModeRotatedSource m kappa beta g observed q s) =
        ∫ s in (0 : Real)..time,
          (physlibFreeQuadraticRotatedSource
              m kappa g observed radius phase s +
            physlibQuadraticHistoryDifference
              m kappa g observed q radius phase s) +
            physlibCubicRotatedSource m beta g observed q s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact physlibModeRotatedSource_eq_freeQuadratic_add_history_add_cubic
        m kappa beta g observed q radius phase s
    _ =
        (∫ s in (0 : Real)..time,
          physlibFreeQuadraticRotatedSource
            m kappa g observed radius phase s) +
        (∫ s in (0 : Real)..time,
          physlibQuadraticHistoryDifference
            m kappa g observed q radius phase s) +
        (∫ s in (0 : Real)..time,
          physlibCubicRotatedSource m beta g observed q s) := by
      rw [intervalIntegral.integral_add (hfree.add hhistory) hcubic,
        intervalIntegral.integral_add hfree hhistory]
    _ = _ := by
      rw [intervalIntegral_physlibFreeQuadraticRotatedSource_eq_correction]

/-- Full interaction-picture formula for an actual Physlib Hamilton
trajectory, now with the true nonlinear Duhamel term resolved into a free
quadratic first-Picard correction and two exact remainders. -/
theorem interactionPicture_physlibMode_eq_initial_add_firstPicard_add_remainders
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
      physlibModeAmplitude m observed p q 0 +
        freeQuadraticInteractionPictureCorrection
          (physlibQuadraticCoupling m kappa g observed)
          m observed radius (modeFrequency m) time phase +
        (∫ s in (0 : Real)..time,
          physlibQuadraticHistoryDifference
            m kappa g observed q radius phase s) +
        (∫ s in (0 : Real)..time,
          physlibCubicRotatedSource m beta g observed q s) := by
  rw [interactionPicture_physlibMode_eq_initial_add_integral_of_differentiable
    m kappa beta g observed p q hp hq hHamilton homega time,
    intervalIntegral_physlibModeRotatedSource_eq_firstPicard_add_remainders
      m kappa beta g observed q hq radius phase time]
  ring

end

end ArchonPhysics.PhyslibFPUTFirstPicardDecomposition

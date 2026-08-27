import ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
import ArchonPhysics.FreeFPUTA0DirectCubicBridge

/-!
# Complete finite character family for the Physlib FPUT second Picard term

The exact unit second-Picard coefficient is the sum of two finite families:
the iterated quadratic tree and the direct cubic free-orbit term.  This module
keeps that disjoint union explicit.  Its coefficient contains the nested
two-time integral on the quadratic branch and the ordinary oscillatory
integral on the cubic branch.

All statements are finite-volume, finite-interval identities.  The
zero-frequency endpoint is inherited from tensor-level decoupling of the
observed leg, before the forced-mode normalization is simplified.
-/

namespace ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open scoped Interval

noncomputable section

/-- The complete second-Picard family is the disjoint union of the
iterated-quadratic tree and the direct cubic term. -/
abbrev CompleteSecondPicardCharacterTerm (N : Nat) :=
  IteratedQuadraticSecondPicardCharacterTerm N ⊕ CubicPhaseTerm N

/-- Initial-phase charge of a complete second-Picard term. -/
def completeSecondPicardCharge {N : Nat} [NeZero N] :
    CompleteSecondPicardCharacterTerm N → Lattice.Site N → Int
  | Sum.inl term => iteratedQuadraticSecondPicardCharge term
  | Sum.inr term => cubicPhaseCharge term

/-- Deterministic integrated coefficient of a complete second-Picard term.
The left branch uses the exact nested integral; the right branch uses the
direct cubic coefficient with the physical quartic-force parameter `beta`. -/
def completeSecondPicardCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) : CompleteSecondPicardCharacterTerm N → Complex
  | Sum.inl term =>
      iteratedQuadraticSecondPicardNestedCoefficient
        m kappa radius observed time term
  | Sum.inr term =>
      oscillatoryCoefficient
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (modeFrequency m observed) beta)
          m observed radius)
        (cubicPhaseMismatch (modeFrequency m) observed) time term

@[simp] theorem completeSecondPicardCharge_inl
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    completeSecondPicardCharge (Sum.inl term) =
      iteratedQuadraticSecondPicardCharge term := rfl

@[simp] theorem completeSecondPicardCharge_inr
    {N : Nat} [NeZero N] (term : CubicPhaseTerm N) :
    completeSecondPicardCharge (Sum.inr term) = cubicPhaseCharge term := rfl

@[simp] theorem completeSecondPicardCoefficient_inl
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    completeSecondPicardCoefficient m kappa beta radius observed time
        (Sum.inl term) =
      iteratedQuadraticSecondPicardNestedCoefficient
        m kappa radius observed time term := rfl

@[simp] theorem completeSecondPicardCoefficient_inr
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : CubicPhaseTerm N) :
    completeSecondPicardCoefficient m kappa beta radius observed time
        (Sum.inr term) =
      oscillatoryCoefficient
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (modeFrequency m observed) beta)
          m observed radius)
        (cubicPhaseMismatch (modeFrequency m) observed) time term := rfl

/-! ## Exact assembly of the two physical components -/

/-- A finite character family indexed by a sum type is exactly the sum of
the two branch families. -/
theorem finitePhaseCorrection_completeSecondPicard_eq_add
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (phase : UnitAddTorus (Lattice.Site N)) :
    finitePhaseCorrection
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge phase =
      finitePhaseCorrection
          (iteratedQuadraticSecondPicardNestedCoefficient
            m kappa radius observed time)
          iteratedQuadraticSecondPicardCharge phase +
        finitePhaseCorrection
          (oscillatoryCoefficient
            (cubicDuhamelCoefficient
              (physicalCubicUnitCoupling (modeFrequency m observed) beta)
              m observed radius)
            (cubicPhaseMismatch (modeFrequency m) observed) time)
          cubicPhaseCharge phase := by
  classical
  unfold finitePhaseCorrection
  rw [Fintype.sum_sum_type]
  rfl

/-- The complete P3 coefficient is the sum of its integrated quadratic and
direct cubic components. -/
theorem physlibFPUTSecondPicardCoefficient_eq_components
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibFPUTSecondPicardCoefficient
        m kappa beta observed radius phase time =
      physlibIteratedQuadraticSecondPicardCoefficient
          m kappa radius phase time observed +
        physlibFreeCubicSecondPicardCoefficient
          m beta observed radius phase time := by
  have hquadratic : IntervalIntegrable
      (physlibQuadraticSecondPicardRotatedSource
        m kappa observed radius phase) volume 0 time := by
    have hcomplete := intervalIntegrable_physlibFPUTSecondPicardRotatedSource
      m kappa 0 observed radius phase 0 time
    apply hcomplete.congr
    intro s hs
    unfold physlibFPUTSecondPicardRotatedSource
      physlibFreeCubicSecondPicardRotatedSource forcedModeSource
    simp
  have hcubic : IntervalIntegrable
      (physlibFreeCubicSecondPicardRotatedSource
        m beta observed radius phase) volume 0 time := by
    have hcomplete := intervalIntegrable_physlibFPUTSecondPicardRotatedSource
      m 0 beta observed radius phase 0 time
    apply hcomplete.congr
    intro s hs
    unfold physlibFPUTSecondPicardRotatedSource
      physlibQuadraticSecondPicardRotatedSource forcedModeSource
    simp
  unfold physlibFPUTSecondPicardCoefficient
    physlibFPUTSecondPicardRotatedSource
    physlibIteratedQuadraticSecondPicardCoefficient
    physlibFreeCubicSecondPicardCoefficient
  exact intervalIntegral.integral_add hquadratic hcubic

/-- Exact complete finite-character expansion of the P3 `A2` coefficient,
with no grouping or discarded terms. -/
theorem physlibFPUTSecondPicardCoefficient_eq_completeCharacterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibFPUTSecondPicardCoefficient
        m kappa beta observed radius phase time =
      finitePhaseCorrection
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge phase := by
  rw [physlibFPUTSecondPicardCoefficient_eq_components,
    physlibIteratedQuadraticSecondPicardCoefficient_eq_characterFamily,
    physlibFreeCubicSecondPicardCoefficient_eq_oscillatoryFamily]
  unfold finiteHaarOscillatorySum
  exact (finitePhaseCorrection_completeSecondPicard_eq_add
    m kappa beta radius observed time phase).symm

/-! ## Observed zero-frequency endpoint -/

/-- At zero observed frequency the complete coefficient vanishes through
the tensor-decoupled quadratic and cubic physical sources. -/
theorem completeSecondPicardCharacterFamily_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N)
    (hzero : modeFrequency m observed = 0) :
    finitePhaseCorrection
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge phase = 0 := by
  rw [← physlibFPUTSecondPicardCoefficient_eq_completeCharacterFamily,
    physlibFPUTSecondPicardCoefficient_eq_zero_of_modeFrequency_eq_zero
      m kappa beta observed radius phase time hzero]

end

end ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily

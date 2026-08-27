import ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
import ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation

/-!
# Entropy rigidity for canonical L-infinity states

An `Lp` class is only specified almost everywhere, whereas the pointwise
entropy algebra uses a bounded measurable function with a genuine positive
floor.  We select such a representative by taking the maximum of the
canonical bounded representative and the supplied essential floor.  This
does not change the quotient class and lets the bounded-measurable rigidity
theorem classify equality in the H-theorem directly at quotient level.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity

open Filter MeasureTheory
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- A pointwise floor-preserving representative of a canonical `L-infinity`
class. -/
def positiveFloorRepresentative
    (collision : ResonantThreeWaveMeasure Mode) (floor : Real)
    (action : CanonicalLInfinity collision) : Mode → Real :=
  fun mode => max floor (linfinityRepresentative collision action mode)

theorem measurable_positiveFloorRepresentative
    (collision : ResonantThreeWaveMeasure Mode) (floor : Real)
    (action : CanonicalLInfinity collision) :
    Measurable (positiveFloorRepresentative collision floor action) := by
  exact measurable_const.max
    (measurable_linfinityRepresentative collision action)

theorem floor_le_positiveFloorRepresentative
    (collision : ResonantThreeWaveMeasure Mode) (floor : Real)
    (action : CanonicalLInfinity collision) (mode : Mode) :
    floor ≤ positiveFloorRepresentative collision floor action mode := by
  exact le_max_left _ _

theorem norm_positiveFloorRepresentative_le
    (collision : ResonantThreeWaveMeasure Mode) {floor : Real}
    (hfloor : 0 ≤ floor) (action : CanonicalLInfinity collision)
    (mode : Mode) :
    ‖positiveFloorRepresentative collision floor action mode‖ ≤
      max floor ‖action‖ := by
  have hrep := norm_linfinityRepresentative_le collision action mode
  rw [Real.norm_eq_abs] at hrep ⊢
  have hnonnegative : 0 ≤
      positiveFloorRepresentative collision floor action mode :=
    hfloor.trans (floor_le_positiveFloorRepresentative
      collision floor action mode)
  rw [abs_of_nonneg hnonnegative]
  unfold positiveFloorRepresentative
  apply max_le
  · exact le_max_left _ _
  · exact (le_abs_self _).trans (hrep.trans (le_max_right _ _))

/-- If the quotient class has the supplied essential lower bound, the
floor-preserving representative agrees with it almost everywhere. -/
theorem positiveFloorRepresentative_ae_eq
    (collision : ResonantThreeWaveMeasure Mode) {floor : Real}
    (action : CanonicalLInfinity collision)
    (hactionFloor : AELowerBound collision floor action) :
    positiveFloorRepresentative collision floor action =ᵐ[
      collisionReferenceMeasure collision] action := by
  filter_upwards [linfinityRepresentative_ae_eq collision action,
    hactionFloor] with mode hrepresentative hfloor
  unfold positiveFloorRepresentative
  rw [hrepresentative, max_eq_right hfloor]

theorem positiveFloorRepresentative_isBoundedMeasurable
    (collision : ResonantThreeWaveMeasure Mode) {floor : Real}
    (hfloor : 0 ≤ floor) (action : CanonicalLInfinity collision) :
    IsBoundedMeasurable
      (positiveFloorRepresentative collision floor action) := by
  refine ⟨measurable_positiveFloorRepresentative collision floor action,
    max floor ‖action‖, ?_⟩
  exact norm_positiveFloorRepresentative_le collision hfloor action

/-- Quotient-level entropy production, evaluated on the canonical bounded
representative repaired to preserve the supplied positive floor everywhere.
-/
def canonicalLogEntropyProduction
    (collision : ResonantThreeWaveMeasure Mode) (floor : Real)
    (action : CanonicalLInfinity collision) : Real :=
  continuumLogEntropyProduction collision
    (positiveFloorRepresentative collision floor action)

/-- Equality in the quotient-level H-theorem classifies the inverse action
almost everywhere under bounded-measurable frequency-balance rigidity. -/
theorem inverseAction_ae_proportional_of_canonicalEntropy_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    (hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision)
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision)
    (hactionFloor : AELowerBound collision floor action)
    (hzero : canonicalLogEntropyProduction collision floor action = 0) :
    ∃ scale : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        (action mode)⁻¹ = scale * collision.frequency mode := by
  let representative := positiveFloorRepresentative collision floor action
  have hbounded : IsBoundedMeasurable representative :=
    positiveFloorRepresentative_isBoundedMeasurable
      collision hfloor.le action
  have hpointwiseFloor : ∀ mode, floor ≤ representative mode :=
    floor_le_positiveFloorRepresentative collision floor action
  obtain ⟨scale, hscale⟩ :=
    inverseAction_ae_proportional_of_entropyProduction_eq_zero
      collision hrigid hbounded floor hfloor hpointwiseFloor hzero
  refine ⟨scale, ?_⟩
  filter_upwards [positiveFloorRepresentative_ae_eq
      collision action hactionFloor, hscale] with mode hrep hmode
  rw [← hrep]
  exact hmode

end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity

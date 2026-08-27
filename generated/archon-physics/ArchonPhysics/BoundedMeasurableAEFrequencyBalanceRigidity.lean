import ArchonPhysics.ResonantThreeWaveKineticEquilibrium

/-!
# Bounded measurable frequency-balance rigidity

The entropy equality case never needs rigidity for arbitrary, possibly
nonmeasurable weights.  The relevant weight is the inverse of a bounded action
with a positive floor, hence it is itself bounded and measurable.  This module
records that exact contract and connects it to the continuum H-theorem.
-/

namespace ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ThreeWaveCollisionAlgebra

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The precise balance-rigidity property needed in the equality case of the
continuum H-theorem: every bounded measurable balanced weight is proportional
to frequency for the canonical collision reference measure. -/
def BoundedMeasurableAEFrequencyBalanceRigid
    (collision : ResonantThreeWaveMeasure Mode) : Prop :=
  ∀ weight : Mode → Real,
    IsBoundedMeasurable weight →
    (∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 → Mode)),
      weight (triad 0) = weight (triad 1) + weight (triad 2)) →
    ∃ scale : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        weight mode = scale * collision.frequency mode

/-- The older unrestricted rigidity contract implies the bounded measurable
one. -/
theorem boundedMeasurableAEFrequencyBalanceRigid_of_AEFrequencyBalanceRigid
    (collision : ResonantThreeWaveMeasure Mode)
    (hrigid : AEFrequencyBalanceRigid collision) :
    BoundedMeasurableAEFrequencyBalanceRigid collision := by
  intro weight _ hbalance
  exact hrigid weight hbalance

/-- Zero entropy production forces the inverse action to be
frequency-proportional under the exact bounded-measurable rigidity contract.
-/
theorem inverseAction_ae_proportional_of_entropyProduction_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    (hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision)
    {action : Mode → Real} (haction : IsBoundedMeasurable action)
    (floor : Real) (hfloor : 0 < floor)
    (hactionFloor : ∀ mode, floor ≤ action mode)
    (hzero : continuumLogEntropyProduction collision action = 0) :
    ∃ scale : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        (action mode)⁻¹ = scale * collision.frequency mode := by
  apply hrigid (fun mode => (action mode)⁻¹)
  · exact inverseAction_isBoundedMeasurable haction floor hfloor hactionFloor
  · have hbalance :=
      (continuumLogEntropyProduction_eq_zero_iff_inverseActionMismatch_ae
        collision haction floor hfloor hactionFloor).mp hzero
    filter_upwards [hbalance] with triad htriad
    exact (inverseActionMismatch_eq_zero_iff
      (action (triad 0)) (action (triad 1)) (action (triad 2))).mp htriad

end

end ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity

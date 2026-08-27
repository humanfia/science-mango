import ArchonPhysics.FrozenCollisionPerSiteNormalization

/-!
# A selected physical triad gives a lower bound on mismatch mass

The positive weighted mismatch measure is a finite sum of nonnegative Dirac
masses.  Consequently any one positive-frequency ordered triad supplies an
exact lower bound on every measurable mismatch set containing its physical
mismatch.  This elementary direction is useful when a concrete random-mass
patch has already certified a positive physical interaction weight.

No uniformity in the volume, mode labels, or mismatch width is asserted.
-/

namespace ArchonPhysics.SelectedTriadMismatchLower

open ArchonPhysics
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenCollisionPerSiteNormalization
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- One positive-frequency ordered triad is a summand of the complete
physical weighted mismatch measure. -/
theorem selectedTriad_weight_le_positiveWeightedMismatchMeasure_apply
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) (modes : OrderedModeTriple N)
    (target : Set Real) (htarget : MeasurableSet target)
    (hpositive : IsPositiveOrderedTriple m modes)
    (hmismatch : orderedThreeWaveMismatch m sign modes ∈ target) :
    ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) <=
      positiveWeightedMismatchMeasure m sign target := by
  classical
  unfold positiveWeightedMismatchMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  have hterm :
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) =
        ((if IsPositiveOrderedTriple m modes then
            ENNReal.ofReal
                (harmonicOrderedNormalizedInteractionWeight m modes) •
              Measure.dirac (orderedThreeWaveMismatch m sign modes)
          else 0) : Measure Real) target := by
    simp [hpositive, Measure.dirac_apply' _ htarget, hmismatch]
  rw [hterm]
  let summand : OrderedModeTriple N -> ENNReal := fun selected =>
    ((if IsPositiveOrderedTriple m selected then
        ENNReal.ofReal
            (harmonicOrderedNormalizedInteractionWeight m selected) •
          Measure.dirac (orderedThreeWaveMismatch m sign selected)
      else 0) : Measure Real) target
  change summand modes <= ∑ selected, summand selected
  exact Finset.single_le_sum
    (fun selected _hselected =>
      (bot_le : (0 : ENNReal) <= summand selected))
    (Finset.mem_univ modes)

/-- The same selected-triad lower bound after the canonical division by the
number of sites. -/
theorem invSite_mul_selectedTriad_weight_le_perSiteMismatch_apply
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) (modes : OrderedModeTriple N)
    (target : Set Real) (htarget : MeasurableSet target)
    (hpositive : IsPositiveOrderedTriple m modes)
    (hmismatch : orderedThreeWaveMismatch m sign modes ∈ target) :
    (↑((N : NNReal)⁻¹) : ENNReal) *
        ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) <=
      (perSitePositiveWeightedMismatchFiniteMeasure m sign : Measure Real)
        target := by
  have hselected :=
    selectedTriad_weight_le_positiveWeightedMismatchMeasure_apply
      m sign modes target htarget hpositive hmismatch
  unfold perSitePositiveWeightedMismatchFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  change (↑((N : NNReal)⁻¹) : ENNReal) *
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) <=
    (↑((N : NNReal)⁻¹) : ENNReal) * positiveWeightedMismatchMeasure m sign target
  exact mul_le_mul_of_nonneg_left hselected (by positivity)
end

end ArchonPhysics.SelectedTriadMismatchLower

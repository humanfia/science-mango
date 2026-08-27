import ArchonPhysics.DecayChannelSectorClusterHybridReduction

/-!
# Nullity endpoint for the child-repeated reduced resonance line

The child-repeated decay sector is carried by a two-frequency law with
coordinates `(omega_parent, omega_child)`.  Exact decay resonance is the
affine line `omega_parent = 2 * omega_child`.  This file proves that this line
has planar Lebesgue measure zero and records the correctly oriented absolute-
continuity endpoint needed by the canonical sector reduction.

These results do not assert that the canonical reduced law is absolutely
continuous.  That is the remaining model-facing spectral-averaging estimate;
the point of this module is to make its exact consequence kernel-checkable.
-/

namespace ArchonPhysics.ChildRepeatedReducedResonanceLineNullity

open ArchonPhysics
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ChildRepeatedCanonicalSubsequenceLimit
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedScalarClusterHybridLift
open ArchonPhysics.DecayChannelSectorClusterHybridReduction
open MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The affine reaction line `omega_parent = 2 * omega_child` has zero
two-dimensional Lebesgue measure. -/
theorem volume_childRepeatedReducedResonanceLine_eq_zero :
    (volume : Measure (Real × Real))
        childRepeatedReducedResonanceLine = 0 := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply childRepeatedReducedResonanceLine_isClosed.measurableSet]
  have hsectionZero : ∀ parent : Real,
      (volume : Measure Real)
          (Prod.mk parent ⁻¹' childRepeatedReducedResonanceLine) = 0 := by
    intro parent
    have hsection :
        Prod.mk parent ⁻¹' childRepeatedReducedResonanceLine =
          ({parent / 2} : Set Real) := by
      ext child
      simp only [mem_preimage, mem_singleton_iff]
      change parent - 2 * child = 0 ↔ child = parent / 2
      constructor <;> intro h <;> linarith
    rw [hsection]
    simp
  simp_rw [hsectionZero]
  exact lintegral_zero

/-- Any planar-absolutely-continuous reduced parent/child law gives the exact
reaction line zero mass.  The direction `measure ≪ volume` is essential. -/
theorem childRepeatedReducedResonanceLine_eq_zero_of_absolutelyContinuous
    (measure : Measure (Real × Real))
    (hupper : measure ≪ (volume : Measure (Real × Real))) :
    measure childRepeatedReducedResonanceLine = 0 :=
  hupper volume_childRepeatedReducedResonanceLine_eq_zero

/-- A quantitative planar density domination is a convenient stronger input
for the same nullity endpoint. -/
theorem childRepeatedReducedResonanceLine_eq_zero_of_le_smul_volume
    (measure : Measure (Real × Real)) (C : ENNReal)
    (hupper : measure ≤ C • (volume : Measure (Real × Real))) :
    measure childRepeatedReducedResonanceLine = 0 :=
  childRepeatedReducedResonanceLine_eq_zero_of_absolutelyContinuous
    measure (Measure.absolutelyContinuous_of_le_smul hupper)

/-- Upper absolute continuity of the reduced law closes the zero-atom branch
of any supplied scalar child-repeated hybrid lift. -/
theorem ChildRepeatedScalarClusterHybridLiftData.scalar_singleton_zero_of_reducedAC
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    (hupper :
      (((lift.markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real)) ≪
          (volume : Measure (Real × Real))) :
    (scalarTarget : Measure Real) ({0} : Set Real) = 0 := by
  apply lift.scalar_singleton_zero_iff.mpr
  exact childRepeatedReducedResonanceLine_eq_zero_of_absolutelyContinuous
    _ hupper

/-- The complete decay target has no zero atom once the all-distinct scalar
branch is null and the child reduced law has planar upper absolute
continuity. -/
theorem DecaySectorClusterHybridReductionData.target_zeroAtom_of_allDistinct_of_childReducedAC
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {target : FiniteMeasure Real}
    (reduction : DecaySectorClusterHybridReductionData
      ensemble omega target)
    (hallDistinct :
      (reduction.cluster.allDistinct : Measure Real)
        ({0} : Set Real) = 0)
    (hchildUpper :
      (((reduction.childLift.markedTarget.map
          forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection :
          FiniteMeasure (Real × Real)) : Measure (Real × Real)) ≪
        (volume : Measure (Real × Real))) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  apply reduction.target_zeroAtom_iff.mpr
  exact ⟨hallDistinct,
    childRepeatedReducedResonanceLine_eq_zero_of_absolutelyContinuous
      _ hchildUpper⟩

end

end ArchonPhysics.ChildRepeatedReducedResonanceLineNullity

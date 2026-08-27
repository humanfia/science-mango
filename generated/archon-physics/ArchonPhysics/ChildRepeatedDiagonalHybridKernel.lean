import ArchonPhysics.ActualThreeMassRepeatedChildModeObstruction
import ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit

/-!
# Child-repeated diagonal and hybrid decay kernel

A child-repeated frequency-triple law is a singular two-parameter law, not a
three-dimensional absolutely continuous sector.  This module parametrizes the
closed diagonal exactly, reconstructs every supported measure from its
`(omega_parent, omega_child)` marginal, and identifies the decay mismatch as
`omega_parent - 2 * omega_child`.

No vanishing conclusion is asserted.
-/

open scoped Topology

namespace ArchonPhysics.ChildRepeatedDiagonalHybridKernel

open ArchonPhysics
open ArchonPhysics.ActualThreeMassRepeatedChildModeObstruction
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]
/-! ## Exact parametrization of the child-frequency diagonal -/

/-- Forget the repeated third coordinate, retaining the parent frequency and
one copy of the child frequency. -/
def childRepeatedFrequencyProjection (frequency : Fin 3 -> Real) :
    Real × Real :=
  (frequency 0, frequency 1)

/-- Parametrize the child-frequency diagonal by the parent frequency and one
child frequency. -/
def childRepeatedFrequencyDiagonalLift (frequency : Real × Real) :
    Fin 3 -> Real :=
  fun r => if r = 0 then frequency.1 else frequency.2

theorem continuous_childRepeatedFrequencyProjection :
    Continuous childRepeatedFrequencyProjection := by
  exact (continuous_apply 0).prodMk (continuous_apply 1)

theorem measurable_childRepeatedFrequencyProjection :
    Measurable childRepeatedFrequencyProjection :=
  continuous_childRepeatedFrequencyProjection.measurable

theorem continuous_childRepeatedFrequencyDiagonalLift :
    Continuous childRepeatedFrequencyDiagonalLift := by
  apply continuous_pi
  intro r
  by_cases hr : r = 0
  · subst r
    simpa [childRepeatedFrequencyDiagonalLift] using
      (continuous_fst : Continuous (Prod.fst : Real × Real -> Real))
  · simpa [childRepeatedFrequencyDiagonalLift, hr] using
      (continuous_snd : Continuous (Prod.snd : Real × Real -> Real))

theorem measurable_childRepeatedFrequencyDiagonalLift :
    Measurable childRepeatedFrequencyDiagonalLift :=
  continuous_childRepeatedFrequencyDiagonalLift.measurable

@[simp]
theorem childRepeatedFrequencyProjection_diagonalLift
    (frequency : Real × Real) :
    childRepeatedFrequencyProjection
        (childRepeatedFrequencyDiagonalLift frequency) = frequency := by
  ext <;> simp [childRepeatedFrequencyProjection,
    childRepeatedFrequencyDiagonalLift]

theorem childRepeatedFrequencyDiagonalLift_mem
    (frequency : Real × Real) :
    childRepeatedFrequencyDiagonalLift frequency ∈
      childRepeatedFrequencyDiagonal := by
  simp [childRepeatedFrequencyDiagonalLift,
    childRepeatedFrequencyDiagonal]

theorem childRepeatedFrequencyDiagonalLift_projection_eq_of_mem
    {frequency : Fin 3 -> Real}
    (hfrequency : frequency ∈ childRepeatedFrequencyDiagonal) :
    childRepeatedFrequencyDiagonalLift
        (childRepeatedFrequencyProjection frequency) = frequency := by
  funext r
  fin_cases r
  · simp [childRepeatedFrequencyProjection, childRepeatedFrequencyDiagonalLift]
  · simp [childRepeatedFrequencyProjection, childRepeatedFrequencyDiagonalLift]
  · simpa [childRepeatedFrequencyProjection, childRepeatedFrequencyDiagonalLift,
      childRepeatedFrequencyDiagonal] using hfrequency

/-- A measure carried by the child-frequency diagonal is exactly reconstructed
from its two-coordinate marginal. No finiteness hypothesis is needed. -/
theorem map_diagonalLift_map_projection_eq_of_compl_diagonal_eq_zero
    (measure : Measure (Fin 3 -> Real))
    (hsupport : measure (childRepeatedFrequencyDiagonalᶜ) = 0) :
    Measure.map childRepeatedFrequencyDiagonalLift
        (Measure.map childRepeatedFrequencyProjection measure) = measure := by
  rw [Measure.map_map measurable_childRepeatedFrequencyDiagonalLift
    measurable_childRepeatedFrequencyProjection]
  calc
    Measure.map
        (childRepeatedFrequencyDiagonalLift ∘
          childRepeatedFrequencyProjection) measure =
        Measure.map id measure := by
      apply Measure.map_congr
      have haeDiagonal :
          ∀ᵐ frequency ∂measure,
            frequency ∈ childRepeatedFrequencyDiagonal :=
        ae_iff.mpr hsupport
      filter_upwards [haeDiagonal] with frequency hfrequency
      exact
        childRepeatedFrequencyDiagonalLift_projection_eq_of_mem hfrequency
    _ = measure := Measure.map_id

/-- Bundled finite-measure form of the exact diagonal reconstruction. -/
theorem finiteMeasure_map_diagonalLift_map_projection_eq_of_compl_diagonal_eq_zero
    (measure : FiniteMeasure (Fin 3 -> Real))
    (hsupport : (measure : Measure (Fin 3 -> Real))
      (childRepeatedFrequencyDiagonalᶜ) = 0) :
    (measure.map childRepeatedFrequencyProjection).map
        childRepeatedFrequencyDiagonalLift = measure := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_map]
  exact map_diagonalLift_map_projection_eq_of_compl_diagonal_eq_zero
    (measure : Measure (Fin 3 -> Real)) hsupport

/-! ## The exact lower-dimensional decay mismatch -/

/-- The decay mismatch after diagonal parametrization. -/
def childRepeatedDecayMismatch (frequency : Real × Real) : Real :=
  frequency.1 - 2 * frequency.2

theorem continuous_childRepeatedDecayMismatch :
    Continuous childRepeatedDecayMismatch := by
  unfold childRepeatedDecayMismatch
  fun_prop

theorem measurable_childRepeatedDecayMismatch :
    Measurable childRepeatedDecayMismatch :=
  continuous_childRepeatedDecayMismatch.measurable

/-- On `(omega_parent, omega_child, omega_child)`, the `(+,-,-)` mismatch is
exactly `omega_parent - 2 * omega_child`. -/
theorem frequencyTripleMismatch_decay_diagonalLift
    (frequency : Real × Real) :
    frequencyTripleMismatch decayInteractionSign
        (childRepeatedFrequencyDiagonalLift frequency) =
      childRepeatedDecayMismatch frequency := by
  unfold frequencyTripleMismatch decayInteractionSign
    childRepeatedFrequencyDiagonalLift childRepeatedDecayMismatch
  rw [Fin.sum_univ_three]
  simp
  ring

/-- The scalar decay-mismatch law of a diagonal-supported triple measure is
the one-dimensional pushforward of its two-coordinate singular reaction law. -/
theorem map_decayMismatch_eq_map_childRepeatedDecayMismatch_projection
    (measure : Measure (Fin 3 -> Real))
    (hsupport : measure (childRepeatedFrequencyDiagonalᶜ) = 0) :
    Measure.map (frequencyTripleMismatch decayInteractionSign) measure =
      Measure.map childRepeatedDecayMismatch
        (Measure.map childRepeatedFrequencyProjection measure) := by
  calc
    Measure.map (frequencyTripleMismatch decayInteractionSign) measure =
        Measure.map (frequencyTripleMismatch decayInteractionSign)
          (Measure.map childRepeatedFrequencyDiagonalLift
            (Measure.map childRepeatedFrequencyProjection measure)) :=
      congrArg (Measure.map (frequencyTripleMismatch decayInteractionSign))
        (map_diagonalLift_map_projection_eq_of_compl_diagonal_eq_zero
          measure hsupport).symm
    _ = Measure.map
          (frequencyTripleMismatch decayInteractionSign ∘
            childRepeatedFrequencyDiagonalLift)
          (Measure.map childRepeatedFrequencyProjection measure) :=
      Measure.map_map (measurable_frequencyTripleMismatch decayInteractionSign)
        measurable_childRepeatedFrequencyDiagonalLift
    _ = Measure.map childRepeatedDecayMismatch
          (Measure.map childRepeatedFrequencyProjection measure) := by
      apply Measure.map_congr
      filter_upwards [] with frequency
      exact frequencyTripleMismatch_decay_diagonalLift frequency

/-- Bundled finite-measure form of the reduced scalar mismatch pushforward. -/
theorem finiteMeasure_map_decayMismatch_eq_map_childRepeatedDecayMismatch_projection
    (measure : FiniteMeasure (Fin 3 -> Real))
    (hsupport : (measure : Measure (Fin 3 -> Real))
      (childRepeatedFrequencyDiagonalᶜ) = 0) :
    measure.map (frequencyTripleMismatch decayInteractionSign) =
      (measure.map childRepeatedFrequencyProjection).map
        childRepeatedDecayMismatch := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_map]
  exact map_decayMismatch_eq_map_childRepeatedDecayMismatch_projection
    (measure : Measure (Fin 3 -> Real)) hsupport

/-- The unnormalized finite-volume child-repeated triple law is the diagonal
lift of its parent/child frequency-pair law. -/
theorem positiveWeightedFrequencyTripleMeasureWhere_childRepeated_reconstruction
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Measure.map childRepeatedFrequencyDiagonalLift
        (Measure.map childRepeatedFrequencyProjection
          (positiveWeightedFrequencyTripleMeasureWhere m ChildRepeated)) =
      positiveWeightedFrequencyTripleMeasureWhere m ChildRepeated := by
  exact map_diagonalLift_map_projection_eq_of_compl_diagonal_eq_zero _
    (positiveWeightedFrequencyTripleMeasureWhere_childRepeated_compl_eq_zero m)

/-- The child-repeated scalar mismatch measure is exactly the reduced
`(omega_parent, omega_child) ↦ omega_parent - 2 * omega_child` pushforward. -/
theorem positiveWeightedMismatchMeasureWhere_childRepeated_decay_eq_reduced
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedMismatchMeasureWhere m decayInteractionSign ChildRepeated =
      Measure.map childRepeatedDecayMismatch
        (Measure.map childRepeatedFrequencyProjection
          (positiveWeightedFrequencyTripleMeasureWhere m ChildRepeated)) := by
  rw [← map_positiveWeightedFrequencyTripleMeasureWhere_eq_mismatchWhere]
  exact map_decayMismatch_eq_map_childRepeatedDecayMismatch_projection _
    (positiveWeightedFrequencyTripleMeasureWhere_childRepeated_compl_eq_zero m)

/-- Exact finite-volume reconstruction after site normalization. -/
theorem perSiteChildRepeatedFiniteMeasure_reconstruction
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    ((perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
          m ChildRepeated).map childRepeatedFrequencyProjection).map
        childRepeatedFrequencyDiagonalLift =
      perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
        m ChildRepeated := by
  exact
    finiteMeasure_map_diagonalLift_map_projection_eq_of_compl_diagonal_eq_zero
      _ (perSiteChildRepeatedFiniteMeasure_compl_diagonal_eq_zero m)

/-- Exact reduced scalar pushforward after site normalization. -/
theorem perSiteChildRepeatedFiniteMeasure_decayMismatch_eq_reduced
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    (perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
        m ChildRepeated).map
        (frequencyTripleMismatch decayInteractionSign) =
      ((perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
          m ChildRepeated).map childRepeatedFrequencyProjection).map
        childRepeatedDecayMismatch := by
  exact
    finiteMeasure_map_decayMismatch_eq_map_childRepeatedDecayMismatch_projection
      _ (perSiteChildRepeatedFiniteMeasure_compl_diagonal_eq_zero m)
/-- Consequently every such weak limit is exactly reconstructed from its
two-coordinate parent/child marginal. -/
theorem childRepeatedPerSiteWeakLimit_reconstruction
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : FiniteMeasure (Fin 3 -> Real))
    (hweak : Tendsto
      (fun n : Nat =>
        perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
          (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated)
      atTop (nhds target)) :
    (target.map childRepeatedFrequencyProjection).map
        childRepeatedFrequencyDiagonalLift = target := by
  exact
    finiteMeasure_map_diagonalLift_map_projection_eq_of_compl_diagonal_eq_zero
      target
      (childRepeatedPerSiteWeakLimit_compl_diagonal_eq_zero
        ensemble omega target hweak)

/-- The decay mismatch law of a child-repeated weak limit is likewise the
one-dimensional reduced pushforward of its two-coordinate singular law. -/
theorem childRepeatedPerSiteWeakLimit_decayMismatch_eq_reduced
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : FiniteMeasure (Fin 3 -> Real))
    (hweak : Tendsto
      (fun n : Nat =>
        perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
          (ensemble.restrictPositiveMass (N := n + 2) omega) ChildRepeated)
      atTop (nhds target)) :
    target.map (frequencyTripleMismatch decayInteractionSign) =
      (target.map childRepeatedFrequencyProjection).map
        childRepeatedDecayMismatch := by
  exact
    finiteMeasure_map_decayMismatch_eq_map_childRepeatedDecayMismatch_projection
      target
      (childRepeatedPerSiteWeakLimit_compl_diagonal_eq_zero
        ensemble omega target hweak)

/-- Pointwise compatibility with the existing repeated-child obstruction:
the mode-level decay mismatch is the same reduced diagonal coordinate. -/
theorem orderedThreeWaveMismatch_decay_childRepeated_eq_reduced
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (hchild : ChildRepeated modes) :
    orderedThreeWaveMismatch m decayInteractionSign modes =
      childRepeatedDecayMismatch
        (orderedModeFrequency (harmonicHermitian m) (modes 0),
          orderedModeFrequency (harmonicHermitian m) (modes 1)) := by
  simpa [childRepeatedDecayMismatch] using
    orderedThreeWaveMismatch_decay_of_childModes_eq m modes hchild

end

end ArchonPhysics.ChildRepeatedDiagonalHybridKernel

import ArchonPhysics.ResonanceSeparatedJacobianGoodBad
import ArchonPhysics.RandomMassThreeWaveCollisionNetwork

/-!
# Repeated child modes are a lower-dimensional obstruction

A tuple with equal child mode indices cannot be covered by the three-
dimensional lifted coarea chart: its two child frequencies agree identically.
This module makes the resulting obstruction precise.  The broadened child
law is supported on the planar diagonal, which has two-dimensional Lebesgue
measure zero.  Consequently, absolute continuity with respect to planar
Lebesgue measure forces the entire repeated-child contribution to vanish.

This separates a genuine model theorem still needed by the canonical F2
argument from the nondegenerate lifted-Jacobian analysis.
-/

namespace ArchonPhysics.ActualThreeMassRepeatedChildModeObstruction

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

/-- The diagonal in the two-child frequency plane has zero planar Lebesgue
measure. -/
theorem volume_childPairDiagonal_eq_zero :
    (volume : Measure (Real × Real)) (Set.diagonal Real) = 0 := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply measurableSet_diagonal]
  simp [Set.diagonal]

/-- Any lifted chart whose first two coordinates agree pointwise produces a
broadened child law supported on the planar diagonal. -/
theorem map_fst_map_withDensity_compl_diagonal_eq_zero
    (chart : MassTriple → MassTriple) (hchart : Measurable chart)
    (hdiag : ∀ point, (chart point).1.1 = (chart point).1.2)
    (source : Measure MassTriple) (T : Real) :
    Measure.map (Prod.fst : MassTriple → Real × Real)
      ((Measure.map chart source).withDensity
        (liftedResonanceKernelDensity T))
      (Set.diagonal Real)ᶜ = 0 := by
  have htarget : MeasurableSet
      ((Prod.fst : MassTriple → Real × Real) ⁻¹'
        (Set.diagonal Real)ᶜ) :=
    measurableSet_diagonal.compl.preimage measurable_fst
  rw [Measure.map_apply measurable_fst measurableSet_diagonal.compl]
  rw [withDensity_apply _ htarget]
  have hbase : Measure.map chart source
      ((Prod.fst : MassTriple → Real × Real) ⁻¹'
        (Set.diagonal Real)ᶜ) = 0 := by
    rw [Measure.map_apply hchart htarget]
    have hpreimage : chart ⁻¹'
        ((Prod.fst : MassTriple → Real × Real) ⁻¹'
          (Set.diagonal Real)ᶜ) = ∅ := by
      ext point
      simp only [mem_preimage, mem_compl_iff, mem_diagonal_iff,
        mem_empty_iff_false]
      constructor
      · intro hne
        exact hne (hdiag point)
      · intro hfalse
        exact False.elim hfalse
    rw [hpreimage, measure_empty]
  rw [Measure.restrict_eq_zero.mpr hbase]
  simp

/-- A measure supported on the planar diagonal and absolutely continuous
with respect to planar Lebesgue measure must be zero. -/
theorem eq_zero_of_absolutelyContinuous_volume_of_compl_diagonal_eq_zero
    (mu : Measure (Real × Real))
    (hupper : mu ≪ (volume : Measure (Real × Real)))
    (hsupport : mu (Set.diagonal Real)ᶜ = 0) :
    mu = 0 := by
  have hdiagonal : mu (Set.diagonal Real) = 0 :=
    hupper volume_childPairDiagonal_eq_zero
  have hrestrictDiagonal : mu.restrict (Set.diagonal Real) = 0 :=
    Measure.restrict_eq_zero.mpr hdiagonal
  have hrestrictComplement : mu.restrict (Set.diagonal Real)ᶜ = 0 :=
    Measure.restrict_eq_zero.mpr hsupport
  rw [← mu.restrict_add_restrict_compl measurableSet_diagonal,
    hrestrictDiagonal, hrestrictComplement, zero_add]

/-- Equal child mode indices force the actual lifted chart onto the planar
diagonal, for every three-mass parameter. -/
theorem actualThreeMassLiftedFrequencyChart_fst_mem_diagonal_of_childModes_eq
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (hmodes : modes 1 = modes 2) (point : MassTriple) :
    (actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes point).1 ∈
        Set.diagonal Real := by
  rw [mem_diagonal_iff]
  simp [actualThreeMassLiftedFrequencyChart, hmodes]

/-- Therefore the exact broadened repeated-child contribution is supported
on the planar diagonal. -/
theorem actualThreeMassLifted_repeatedChild_compl_diagonal_eq_zero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (hmodes : modes 1 = modes 2)
    (source : Measure MassTriple) (T : Real) :
    Measure.map (Prod.fst : MassTriple → Real × Real)
      ((Measure.map
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        source).withDensity (liftedResonanceKernelDensity T))
      (Set.diagonal Real)ᶜ = 0 := by
  apply map_fst_map_withDensity_compl_diagonal_eq_zero
  · exact (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  · intro point
    exact mem_diagonal_iff.mp
      (actualThreeMassLiftedFrequencyChart_fst_mem_diagonal_of_childModes_eq
        fixed site₀ site₁ site₂ sign modes hmodes point)

/-- In particular, planar upper absolute continuity can hold for a repeated-
child contribution only when that contribution is the zero measure. -/
theorem actualThreeMassLifted_repeatedChild_eq_zero_of_upperAC
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (hmodes : modes 1 = modes 2)
    (source : Measure MassTriple) (T : Real)
    (hupper :
      Measure.map (Prod.fst : MassTriple → Real × Real)
        ((Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          source).withDensity (liftedResonanceKernelDensity T)) ≪
        (volume : Measure (Real × Real))) :
    Measure.map (Prod.fst : MassTriple → Real × Real)
        ((Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          source).withDensity (liftedResonanceKernelDensity T)) = 0 := by
  exact eq_zero_of_absolutelyContinuous_volume_of_compl_diagonal_eq_zero
    _ hupper
    (actualThreeMassLifted_repeatedChild_compl_diagonal_eq_zero
      fixed site₀ site₁ site₂ sign modes hmodes source T)


/-! ## Decay-channel classification of repeated mode indices -/

/-- If the parent mode equals the first child mode in the decay channel,
the mismatch magnitude is exactly the remaining child frequency. -/
theorem abs_orderedThreeWaveMismatch_decay_of_parent_eq_childOne
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (hmodes : modes 0 = modes 1) :
    |orderedThreeWaveMismatch m decayInteractionSign modes| =
      orderedModeFrequency (harmonicHermitian m) (modes 2) := by
  rw [orderedThreeWaveMismatch_decay_eq, hmodes, sub_self, zero_sub,
    abs_neg, abs_of_nonneg]
  exact Real.sqrt_nonneg _

/-- If the parent mode equals the second child mode, the mismatch magnitude
is exactly the first child frequency. -/
theorem abs_orderedThreeWaveMismatch_decay_of_parent_eq_childTwo
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (hmodes : modes 0 = modes 2) :
    |orderedThreeWaveMismatch m decayInteractionSign modes| =
      orderedModeFrequency (harmonicHermitian m) (modes 1) := by
  rw [orderedThreeWaveMismatch_decay_eq, hmodes]
  have hrearrange :
      orderedModeFrequency (harmonicHermitian m) (modes 2) -
          orderedModeFrequency (harmonicHermitian m) (modes 1) -
            orderedModeFrequency (harmonicHermitian m) (modes 2) =
        -orderedModeFrequency (harmonicHermitian m) (modes 1) := by
    ring
  rw [hrearrange, abs_neg, abs_of_nonneg]
  exact Real.sqrt_nonneg _

/-- Hence a hard remaining child gives the fixed mismatch gap needed by the
off-resonance sinc-square estimate. -/
theorem mismatch_gap_of_parent_eq_childOne_of_remainingChild_hard
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (hmodes : modes 0 = modes 1)
    {delta : Real}
    (hhard : delta <=
      orderedModeFrequency (harmonicHermitian m) (modes 2)) :
    delta <= |orderedThreeWaveMismatch m decayInteractionSign modes| := by
  rwa [abs_orderedThreeWaveMismatch_decay_of_parent_eq_childOne
    m modes hmodes]

/-- Symmetric hard-gap statement when the parent equals the second child. -/
theorem mismatch_gap_of_parent_eq_childTwo_of_remainingChild_hard
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (hmodes : modes 0 = modes 2)
    {delta : Real}
    (hhard : delta <=
      orderedModeFrequency (harmonicHermitian m) (modes 1)) :
    delta <= |orderedThreeWaveMismatch m decayInteractionSign modes| := by
  rwa [abs_orderedThreeWaveMismatch_decay_of_parent_eq_childTwo
    m modes hmodes]

/-- Equal child modes are qualitatively different: the decay mismatch can
still vanish at the hard resonance `omega_parent = 2 * omega_child`. -/
theorem orderedThreeWaveMismatch_decay_of_childModes_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (hmodes : modes 1 = modes 2) :
    orderedThreeWaveMismatch m decayInteractionSign modes =
      orderedModeFrequency (harmonicHermitian m) (modes 0) -
        2 * orderedModeFrequency (harmonicHermitian m) (modes 1) := by
  rw [orderedThreeWaveMismatch_decay_eq, ← hmodes]
  ring

end

end ArchonPhysics.ActualThreeMassRepeatedChildModeObstruction

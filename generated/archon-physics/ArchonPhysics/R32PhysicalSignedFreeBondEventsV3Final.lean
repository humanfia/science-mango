import ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final

/-!
# Physical-sign canonical signed free-bond events

`FreeFPUTTensorPhaseExpansion.physicalFreePhaseEvolution` advances a canonical
phase by `-omega * time`.  The generic signed measurable field is therefore
evaluated at `-time` here.  This leaves every fixed-time Haar tail unchanged,
but it is essential for pointwise identification with the canonical physical
free orbit.

Only the finite-grid event is declared probabilistic.  Whole-window control
is obtained deterministically from the time net and a Lipschitz estimate.
-/

namespace ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final

open ArchonPhysics
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
open ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final
open MeasureTheory Set

noncomputable section

/-- Signed free physical bond field with the repository's `-omega` phase
evolution convention. -/
def physicalSignedHaarBondField {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N)
    (phase : HarmonicOrderedModeIndex N → UnitAddCircle)
    (time : Real) : Real :=
  signedHaarBondField m bond phase (-time)

theorem measurable_physicalSignedHaarBondField
    {Omega : Type*} [MeasurableSpace Omega]
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun omega ↦ (massSample omega).mass site)
    (phaseSample : Omega → HarmonicOrderedModeIndex N → UnitAddCircle)
    (hphase : Measurable phaseSample)
    (bond : Lattice.Site N) (time : Real) :
    Measurable fun omega ↦
      physicalSignedHaarBondField (massSample omega) bond
        (phaseSample omega) time := by
  exact measurable_signedHaarBondField massSample hmass
    phaseSample hphase bond (-time)

theorem measurable_canonicalPhysicalSignedHaarBondField
    {N : Nat} [NeZero N]
    (bond : Lattice.Site N) (time : Real) :
    Measurable fun sample : RandomEnsemble.SampleSpace ↦
      physicalSignedHaarBondField
        (rawCanonicalFrozenMass (N := N) sample.1) bond
        (orderedPhaseBlockFromSequence (N := N) sample.2) time := by
  exact measurable_canonicalSignedHaarBondField bond (-time)

/-- Failure at one of the concrete V2 rescaled kinetic-grid times. -/
def canonicalPhysicalSignedSimpleFreeGridBad
    {N : Nat} [NeZero N] (T g : Real) :
    Set RandomEnsemble.SampleSpace :=
  {sample |
    OrderedSingleModeProjector.SimpleOrderedSpectrum
      (MeasurableOrderedModeCoupling.Harmonic.harmonicHermitian
        (rawCanonicalFrozenMass (N := N) sample.1))} ∩
  ⋃ index : Lattice.Site N × Fin (freeTimeGridCard T g),
    {sample |
      |physicalSignedHaarBondField
        (rawCanonicalFrozenMass (N := N) sample.1) index.1
        (orderedPhaseBlockFromSequence (N := N) sample.2)
        (freeTimeGrid T g index.2)| > g ^ 4 / 2}

/-- Borel finite-grid good event with the physical phase sign. -/
def canonicalPhysicalSignedFreeGridGood
    {N : Nat} [NeZero N] (T g : Real) :
    Set RandomEnsemble.SampleSpace :=
  {sample |
    OrderedSingleModeProjector.SimpleOrderedSpectrum
      (MeasurableOrderedModeCoupling.Harmonic.harmonicHermitian
        (rawCanonicalFrozenMass (N := N) sample.1))} ∩
    (canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g)ᶜ

theorem measurableSet_canonicalPhysicalSignedSimpleFreeGridBad
    {N : Nat} [NeZero N] (T g : Real) :
    MeasurableSet
      (canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g) := by
  apply measurableSet_canonicalSimpleOrderedSpectrum.inter
  apply MeasurableSet.iUnion
  intro index
  exact measurableSet_lt measurable_const
    (measurable_canonicalPhysicalSignedHaarBondField
      (N := N) index.1 (freeTimeGrid T g index.2)).abs

theorem measurableSet_canonicalPhysicalSignedFreeGridGood
    {N : Nat} [NeZero N] (T g : Real) :
    MeasurableSet (canonicalPhysicalSignedFreeGridGood (N := N) T g) := by
  exact measurableSet_canonicalSimpleOrderedSpectrum.inter
    (measurableSet_canonicalPhysicalSignedSimpleFreeGridBad
      (N := N) T g).compl

theorem canonicalPhysicalSignedFreeGridGood_grid_bound
    {N : Nat} [NeZero N] (T g : Real)
    {sample : RandomEnsemble.SampleSpace}
    (hgood : sample ∈
      canonicalPhysicalSignedFreeGridGood (N := N) T g)
    (bond : Lattice.Site N) (index : Fin (freeTimeGridCard T g)) :
    |physicalSignedHaarBondField
      (rawCanonicalFrozenMass (N := N) sample.1) bond
      (orderedPhaseBlockFromSequence (N := N) sample.2)
      (freeTimeGrid T g index)| ≤ g ^ 4 / 2 := by
  by_contra hnot
  have hbad : sample ∈
      canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g := by
    refine ⟨hgood.1, ?_⟩
    exact Set.mem_iUnion_of_mem (bond, index) (lt_of_not_ge hnot)
  exact hgood.2 hbad

/-- The concrete V2 time net upgrades finite-grid goodness to the complete
kinetic interval.  The Lipschitz constant is explicit at the call site. -/
theorem canonicalPhysicalSignedFreeGridGood_implies_kineticWindow_bound
    {N : Nat} [NeZero N]
    (T g lipschitz : Real) (hT : 0 ≤ T) (hg : 0 < g)
    (hlipschitz_nonneg : 0 ≤ lipschitz)
    (hslack :
      lipschitz * (g / freeTimeGridScale) ^ 4 ≤ g ^ 4 / 2)
    {sample : RandomEnsemble.SampleSpace}
    (hgood : sample ∈
      canonicalPhysicalSignedFreeGridGood (N := N) T g)
    (hlipschitz : ∀ (bond : Lattice.Site N) (s t : Real),
      |physicalSignedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2) t -
        physicalSignedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2) s| ≤
        lipschitz * |t - s|)
    (bond : Lattice.Site N) (time : Real)
    (htime : time ∈ Icc (0 : Real) (T / g ^ 2)) :
    |physicalSignedHaarBondField
      (rawCanonicalFrozenMass (N := N) sample.1) bond
      (orderedPhaseBlockFromSequence (N := N) sample.2) time| ≤
      g ^ 4 := by
  have hnet := freeTimeGrid_isTimeNet T g hT hg
  obtain ⟨index, hindex⟩ := hnet time htime
  have hgrid := canonicalPhysicalSignedFreeGridGood_grid_bound
    T g hgood bond index
  have hvariation := hlipschitz bond (freeTimeGrid T g index) time
  have hvariation' :
      |physicalSignedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2) time -
        physicalSignedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2)
          (freeTimeGrid T g index)| ≤ g ^ 4 / 2 := by
    exact hvariation.trans
      ((mul_le_mul_of_nonneg_left hindex hlipschitz_nonneg).trans hslack)
  calc
    |physicalSignedHaarBondField
        (rawCanonicalFrozenMass (N := N) sample.1) bond
        (orderedPhaseBlockFromSequence (N := N) sample.2) time| ≤
        |physicalSignedHaarBondField
            (rawCanonicalFrozenMass (N := N) sample.1) bond
            (orderedPhaseBlockFromSequence (N := N) sample.2) time -
          physicalSignedHaarBondField
            (rawCanonicalFrozenMass (N := N) sample.1) bond
            (orderedPhaseBlockFromSequence (N := N) sample.2)
            (freeTimeGrid T g index)| +
        |physicalSignedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2)
          (freeTimeGrid T g index)| := by
      calc
        |_| = |(physicalSignedHaarBondField
                  (rawCanonicalFrozenMass (N := N) sample.1) bond
                  (orderedPhaseBlockFromSequence (N := N) sample.2) time -
                physicalSignedHaarBondField
                  (rawCanonicalFrozenMass (N := N) sample.1) bond
                  (orderedPhaseBlockFromSequence (N := N) sample.2)
                  (freeTimeGrid T g index)) +
                physicalSignedHaarBondField
                  (rawCanonicalFrozenMass (N := N) sample.1) bond
                  (orderedPhaseBlockFromSequence (N := N) sample.2)
                  (freeTimeGrid T g index)| := by congr 1 <;> ring
        _ ≤ _ := abs_add_le _ _
    _ ≤ g ^ 4 / 2 + g ^ 4 / 2 := add_le_add hvariation' hgrid
    _ = g ^ 4 := by ring

#print axioms measurableSet_canonicalPhysicalSignedSimpleFreeGridBad
#print axioms measurableSet_canonicalPhysicalSignedFreeGridGood
#print axioms canonicalPhysicalSignedFreeGridGood_implies_kineticWindow_bound

end

end ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final

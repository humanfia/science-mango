import ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral

/-!
# Exact mode-equality partition of the decay-channel collision measure

The three-mode sum contains structurally different sectors.  We partition it
into four mutually exclusive cases, in priority order:

1. the two child labels coincide;
2. the children differ and the parent equals child one;
3. the children and parent/child-one labels differ, while the parent equals
   child two;
4. all three labels differ.

The partition is made before taking any thermodynamic or resonance-broadening
limit.  It lets the all-distinct sector use a three-dimensional coarea chart,
the parent-child sectors use their exact off-resonance identities, and the
child-child sector remain visible as a genuinely diagonal component.
-/

namespace ArchonPhysics.DecayChannelModeEqualityPartition

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open MeasureTheory

noncomputable section

/-- The two outgoing/child labels coincide. -/
def ChildRepeated {N : Nat} [NeZero N]
    (modes : OrderedModeTriple N) : Prop :=
  modes 1 = modes 2

/-- The children differ and the parent equals child one. -/
def ParentChildOneRepeated {N : Nat} [NeZero N]
    (modes : OrderedModeTriple N) : Prop :=
  modes 1 ≠ modes 2 ∧ modes 0 = modes 1

/-- The preceding cases fail and the parent equals child two. -/
def ParentChildTwoRepeated {N : Nat} [NeZero N]
    (modes : OrderedModeTriple N) : Prop :=
  modes 1 ≠ modes 2 ∧ modes 0 ≠ modes 1 ∧ modes 0 = modes 2

/-- All three ordered mode labels are distinct. -/
def AllDistinctModes {N : Nat} [NeZero N]
    (modes : OrderedModeTriple N) : Prop :=
  modes 1 ≠ modes 2 ∧ modes 0 ≠ modes 1 ∧ modes 0 ≠ modes 2

/-- Restrict the positive coupling-weighted joint frequency measure to an
arbitrary tuple predicate. -/
def positiveWeightedFrequencyTripleMeasureWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N → Prop) : Measure (Fin 3 → Real) := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes ∧ keep modes then
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
        Measure.dirac (orderedFrequencyTriple m modes)
    else 0

/-- Restrict the coupling-weighted scalar mismatch measure to a tuple
predicate. -/
def positiveWeightedMismatchMeasureWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (keep : OrderedModeTriple N → Prop) : Measure Real := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes ∧ keep modes then
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
        Measure.dirac (orderedThreeWaveMismatch m sign modes)
    else 0

/-- The predicate-restricted scalar mismatch measure is still exactly the
signed-frequency pushforward of the corresponding joint measure. -/
theorem map_positiveWeightedFrequencyTripleMeasureWhere_eq_mismatchWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (keep : OrderedModeTriple N → Prop) :
    (positiveWeightedFrequencyTripleMeasureWhere m keep).map
        (frequencyTripleMismatch sign) =
      positiveWeightedMismatchMeasureWhere m sign keep := by
  classical
  unfold positiveWeightedFrequencyTripleMeasureWhere
    positiveWeightedMismatchMeasureWhere
  rw [Measure.map_finset_sum'
    (measurable_frequencyTripleMismatch sign).aemeasurable]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hkeep : IsPositiveOrderedTriple m modes ∧ keep modes
  · simp only [if_pos hkeep, Measure.map_smul,
      Measure.map_dirac' (measurable_frequencyTripleMismatch sign)]
    rw [frequencyTripleMismatch_orderedFrequencyTriple]
  · simp [hkeep]

/-- Exact four-sector partition of the complete finite-volume joint frequency
measure. -/
theorem positiveWeightedFrequencyTripleMeasure_eq_modeEqualityPartition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedFrequencyTripleMeasure m =
      positiveWeightedFrequencyTripleMeasureWhere m AllDistinctModes +
      positiveWeightedFrequencyTripleMeasureWhere m ChildRepeated +
      positiveWeightedFrequencyTripleMeasureWhere m ParentChildOneRepeated +
      positiveWeightedFrequencyTripleMeasureWhere m ParentChildTwoRepeated := by
  classical
  unfold positiveWeightedFrequencyTripleMeasure
    positiveWeightedFrequencyTripleMeasureWhere
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · by_cases hchild : modes 1 = modes 2
    · simp [hpositive, ChildRepeated, ParentChildOneRepeated,
        ParentChildTwoRepeated, AllDistinctModes, hchild]
    · by_cases hone : modes 0 = modes 1
      · simp [hpositive, ChildRepeated, ParentChildOneRepeated,
          ParentChildTwoRepeated, AllDistinctModes, hchild, hone]
      · by_cases htwo : modes 0 = modes 2
        · have htwoOne : modes 2 ≠ modes 1 := Ne.symm hchild
          simp [hpositive, ChildRepeated, ParentChildOneRepeated,
            ParentChildTwoRepeated, AllDistinctModes, hchild, htwo, htwoOne]
        · simp [hpositive, ChildRepeated, ParentChildOneRepeated,
            ParentChildTwoRepeated, AllDistinctModes, hchild, hone, htwo]
  · simp [hpositive]

/-- The same exact partition after signed-mismatch pushforward. -/
theorem positiveWeightedMismatchMeasure_eq_modeEqualityPartition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) :
    positiveWeightedMismatchMeasure m sign =
      positiveWeightedMismatchMeasureWhere m sign AllDistinctModes +
      positiveWeightedMismatchMeasureWhere m sign ChildRepeated +
      positiveWeightedMismatchMeasureWhere m sign ParentChildOneRepeated +
      positiveWeightedMismatchMeasureWhere m sign ParentChildTwoRepeated := by
  rw [← map_positiveWeightedFrequencyTripleMeasure_eq_mismatchMeasure,
    positiveWeightedFrequencyTripleMeasure_eq_modeEqualityPartition,
    Measure.map_add, Measure.map_add, Measure.map_add] <;>
    try exact measurable_frequencyTripleMismatch sign
  rw [map_positiveWeightedFrequencyTripleMeasureWhere_eq_mismatchWhere,
    map_positiveWeightedFrequencyTripleMeasureWhere_eq_mismatchWhere,
    map_positiveWeightedFrequencyTripleMeasureWhere_eq_mismatchWhere,
    map_positiveWeightedFrequencyTripleMeasureWhere_eq_mismatchWhere]

/-- Canonical per-site normalization of one predicate-restricted joint
frequency sector. -/
def perSitePositiveWeightedFrequencyTripleMeasureWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (keep : OrderedModeTriple N → Prop) : Measure (Fin 3 → Real) :=
  (N : ENNReal)⁻¹ • positiveWeightedFrequencyTripleMeasureWhere m keep

/-- Per-site normalization preserves the exact four-sector partition. -/
theorem perSite_positiveWeightedFrequencyTripleMeasure_eq_modeEqualityPartition
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    (N : ENNReal)⁻¹ • positiveWeightedFrequencyTripleMeasure m =
      perSitePositiveWeightedFrequencyTripleMeasureWhere m AllDistinctModes +
      perSitePositiveWeightedFrequencyTripleMeasureWhere m ChildRepeated +
      perSitePositiveWeightedFrequencyTripleMeasureWhere
        m ParentChildOneRepeated +
      perSitePositiveWeightedFrequencyTripleMeasureWhere
        m ParentChildTwoRepeated := by
  rw [positiveWeightedFrequencyTripleMeasure_eq_modeEqualityPartition,
    smul_add, smul_add, smul_add]
  rfl

end

end ArchonPhysics.DecayChannelModeEqualityPartition

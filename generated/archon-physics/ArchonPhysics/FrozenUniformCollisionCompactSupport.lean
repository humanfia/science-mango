import ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
import ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
import Mathlib.MeasureTheory.Measure.Tight

/-!
# Uniform compact support for frozen collision measures

The frozen iid mass interval gives the deterministic band edge
`orderedModeFrequency ≤ sqrt 5`.  The comparison theorem with the clean
cycle is recorded alongside that absolute band edge.  Consequently every
signed three-wave mismatch lies in the common compact interval
`[-3 * sqrt 5, 3 * sqrt 5]`.  The physical decay channel `(+,-,-)` has the
sharper interval `[-2 * sqrt 5, sqrt 5]`.

The genuine coupling-weighted mismatch measure, its finite-measure bundle,
its tuple-normalized version, and every nonzero-mass probability
normalization assign zero mass outside the corresponding interval.  This
gives explicit tightness interfaces, including when the site count varies.
No thermodynamic limit or convergence of collision measures is asserted.
-/

open scoped Topology

namespace ArchonPhysics.FrozenUniformCollisionCompactSupport

open ArchonPhysics
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open MeasureTheory

noncomputable section

/-- The frozen iid upper band edge for every physical mode frequency. -/
def collisionFrequencyCeiling : Real := Real.sqrt 5

/-- Common compact support for arbitrary signed three-wave mismatches. -/
def collisionMismatchSupport : Set Real :=
  Set.Icc (-(3 * collisionFrequencyCeiling))
    (3 * collisionFrequencyCeiling)

/-- Sharper common support for the physical decay sign channel `(+,-,-)`. -/
def decayCollisionMismatchSupport : Set Real :=
  Set.Icc (-(2 * collisionFrequencyCeiling)) collisionFrequencyCeiling

/-- The clean-cycle comparison gives a samplewise upper frequency bound
before replacing the clean eigenvalue by the absolute band edge. -/
theorem iid_orderedModeFrequency_le_cleanComparison
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (k : OrderedModeIndex N) :
    orderedModeFrequency
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) k ≤
      Real.sqrt ((5 / 4 : Real) *
        orderedEigenvalue (cleanCycleHarmonicHermitian N) k) := by
  exact Real.sqrt_le_sqrt
    (iid_orderedEigenvalue_harmonic_compare_clean ensemble omega k).2

/-- Every ordered frequency of every frozen realization belongs to the same
closed band `[0, sqrt 5]`. -/
theorem iid_orderedModeFrequency_mem_uniformBand
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (k : OrderedModeIndex N) :
    orderedModeFrequency
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) k ∈
      Set.Icc 0 collisionFrequencyCeiling := by
  constructor
  · exact Real.sqrt_nonneg _
  · exact iid_orderedModeFrequency_harmonic_le_sqrt_five ensemble omega k

/-- A mode selected by the positive-mode filter lies in `(0, sqrt 5]`. -/
theorem iid_orderedPositiveModeFrequency_mem_uniformBand
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (k : OrderedModeIndex N)
    (hk : k ∈ orderedPositiveModeIndices
      (ensemble.restrictPositiveMass (N := N) omega)) :
    orderedModeFrequency
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) k ∈
      Set.Ioc 0 collisionFrequencyCeiling := by
  exact ⟨(mem_orderedPositiveModeIndices_iff _ _).mp hk,
    (iid_orderedModeFrequency_mem_uniformBand ensemble omega k).2⟩

/-- An arbitrary three-sign mismatch lies in the common symmetric compact
interval. -/
theorem iid_orderedThreeWaveMismatch_mem_uniformSupport
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    orderedThreeWaveMismatch
        (ensemble.restrictPositiveMass (N := N) omega) sign modes ∈
      collisionMismatchSupport := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hterm (r : Fin 3) :
      -collisionFrequencyCeiling ≤
          (sign r).coefficient *
            orderedModeFrequency (harmonicHermitian m) (modes r) ∧
        (sign r).coefficient *
            orderedModeFrequency (harmonicHermitian m) (modes r) ≤
          collisionFrequencyCeiling := by
    have hfreq := iid_orderedModeFrequency_mem_uniformBand
      ensemble omega (modes r)
    rcases hfreq with ⟨hfreq0, hfreq1⟩
    dsimp only [m]
    cases hsign : sign r
    · simp only [InteractionSign.coefficient_plus, one_mul]
      constructor <;> linarith
    · simp only [InteractionSign.coefficient_minus, neg_one_mul]
      constructor <;> linarith
  rcases hterm 0 with ⟨h0l, h0u⟩
  rcases hterm 1 with ⟨h1l, h1u⟩
  rcases hterm 2 with ⟨h2l, h2u⟩
  unfold collisionMismatchSupport orderedThreeWaveMismatch
  rw [Fin.sum_univ_three]
  constructor <;> linarith

/-- Absolute-value form of the arbitrary-sign mismatch bound. -/
theorem iid_abs_orderedThreeWaveMismatch_le
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    |orderedThreeWaveMismatch
        (ensemble.restrictPositiveMass (N := N) omega) sign modes| ≤
      3 * collisionFrequencyCeiling := by
  exact abs_le.mpr
    (iid_orderedThreeWaveMismatch_mem_uniformSupport
      ensemble omega sign modes)

/-- The decay mismatch `omega_0 - omega_1 - omega_2` lies in the sharper
interval `[-2 * sqrt 5, sqrt 5]`. -/
theorem iid_orderedThreeWaveMismatch_decay_mem_uniformSupport
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (modes : OrderedModeTriple N) :
    orderedThreeWaveMismatch
        (ensemble.restrictPositiveMass (N := N) omega)
        decayInteractionSign modes ∈ decayCollisionMismatchSupport := by
  have h0 := iid_orderedModeFrequency_mem_uniformBand
    ensemble omega (modes 0)
  have h1 := iid_orderedModeFrequency_mem_uniformBand
    ensemble omega (modes 1)
  have h2 := iid_orderedModeFrequency_mem_uniformBand
    ensemble omega (modes 2)
  rw [orderedThreeWaveMismatch_decay_eq]
  unfold decayCollisionMismatchSupport
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- Symmetric absolute-value consequence for the decay mismatch. -/
theorem iid_abs_orderedThreeWaveMismatch_decay_le
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (modes : OrderedModeTriple N) :
    |orderedThreeWaveMismatch
        (ensemble.restrictPositiveMass (N := N) omega)
        decayInteractionSign modes| ≤ 2 * collisionFrequencyCeiling := by
  have h := iid_orderedThreeWaveMismatch_decay_mem_uniformSupport
    ensemble omega modes
  apply abs_le.mpr
  constructor
  · exact h.1
  · exact h.2.trans (by
      have hsqrt : 0 ≤ collisionFrequencyCeiling := Real.sqrt_nonneg _
      linarith)

/-- The genuine arbitrary-sign weighted mismatch measure has no mass outside
the common compact interval. -/
theorem iid_positiveWeightedMismatchMeasure_compl_uniformSupport_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 → InteractionSign) :
    positiveWeightedMismatchMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign
        (collisionMismatchSupportᶜ) = 0 := by
  classical
  unfold positiveWeightedMismatchMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple
      (ensemble.restrictPositiveMass (N := N) omega) modes
  · rw [if_pos hpositive]
    rw [Measure.smul_apply]
    simp [iid_orderedThreeWaveMismatch_mem_uniformSupport
      ensemble omega sign modes]
  · rw [if_neg hpositive]
    rfl

/-- The decay-channel weighted mismatch measure has no mass outside its
sharper compact interval. -/
theorem iid_positiveWeightedMismatchMeasure_decay_compl_uniformSupport_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    positiveWeightedMismatchMeasure
        (ensemble.restrictPositiveMass (N := N) omega) decayInteractionSign
        (decayCollisionMismatchSupportᶜ) = 0 := by
  classical
  unfold positiveWeightedMismatchMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple
      (ensemble.restrictPositiveMass (N := N) omega) modes
  · rw [if_pos hpositive]
    rw [Measure.smul_apply]
    simp [iid_orderedThreeWaveMismatch_decay_mem_uniformSupport
      ensemble omega modes]
  · rw [if_neg hpositive]
    rfl

/-- The bundled collision finite measure has the same compact support. -/
theorem iid_positiveWeightedMismatchFiniteMeasure_compl_uniformSupport_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 → InteractionSign) :
    (positiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign : Measure Real)
        (collisionMismatchSupportᶜ) = 0 :=
  iid_positiveWeightedMismatchMeasure_compl_uniformSupport_eq_zero
    ensemble omega sign

/-- Tuple-count normalization preserves the common compact support. -/
theorem iid_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_compl_uniformSupport_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 → InteractionSign) :
    (tupleNormalizedPositiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign : Measure Real)
        (collisionMismatchSupportᶜ) = 0 := by
  unfold tupleNormalizedPositiveWeightedMismatchFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  simp [iid_positiveWeightedMismatchFiniteMeasure_compl_uniformSupport_eq_zero
    ensemble omega sign]

/-- At nonzero mass, probability normalization preserves the same common
compact support. -/
theorem iid_normalizedPositiveWeightedMismatchMeasure_compl_uniformSupport_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 → InteractionSign)
    (hmass : (positiveWeightedMismatchFiniteMeasure
      (ensemble.restrictPositiveMass (N := N) omega) sign).mass ≠ 0) :
    (normalizedPositiveWeightedMismatchMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign : Measure Real)
        (collisionMismatchSupportᶜ) = 0 := by
  have hmeasure : positiveWeightedMismatchFiniteMeasure
      (ensemble.restrictPositiveMass (N := N) omega) sign ≠ 0 :=
    (positiveWeightedMismatchFiniteMeasure
      (ensemble.restrictPositiveMass (N := N) omega) sign).mass_nonzero_iff.mp
        hmass
  unfold normalizedPositiveWeightedMismatchMeasure
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hmeasure]
  rw [Measure.smul_apply]
  simp [iid_positiveWeightedMismatchFiniteMeasure_compl_uniformSupport_eq_zero
    ensemble omega sign]

/-- At fixed size and sign channel, the entire frozen-realization family of
genuine weighted mismatch measures is tight, with one explicit compact set. -/
theorem iid_positiveWeightedMismatchMeasure_range_isTight
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (sign : Fin 3 → InteractionSign) :
    IsTightMeasureSet (Set.range fun omega : Omega ↦
      positiveWeightedMismatchMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  refine ⟨collisionMismatchSupport, isCompact_Icc, ?_⟩
  intro mu hmu
  rcases hmu with ⟨omega, rfl⟩
  rw [iid_positiveWeightedMismatchMeasure_compl_uniformSupport_eq_zero]
  exact hepsilon.le

/-- The varying-size tuple-normalized collision finite measures form a tight
sequence without any simple-spectrum assumption. -/
theorem iid_varyingSize_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_range_isTight
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)] (omega : Nat → Omega)
    (sign : Fin 3 → InteractionSign) :
    IsTightMeasureSet (Set.range fun n ↦
      (tupleNormalizedPositiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := N n) (omega n)) sign :
          Measure Real)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  refine ⟨collisionMismatchSupport, isCompact_Icc, ?_⟩
  intro mu hmu
  rcases hmu with ⟨n, rfl⟩
  rw [iid_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_compl_uniformSupport_eq_zero]
  exact hepsilon.le

/-- The corresponding normalized probability shapes are tight whenever each
collision mass is explicitly assumed nonzero. -/
theorem iid_varyingSize_normalizedPositiveWeightedMismatchMeasure_range_isTight
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)] (omega : Nat → Omega)
    (sign : Fin 3 → InteractionSign)
    (hmass : ∀ n, (positiveWeightedMismatchFiniteMeasure
      (ensemble.restrictPositiveMass (N := N n) (omega n)) sign).mass ≠ 0) :
    IsTightMeasureSet (Set.range fun n ↦
      (normalizedPositiveWeightedMismatchMeasure
        (ensemble.restrictPositiveMass (N := N n) (omega n)) sign :
          Measure Real)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  refine ⟨collisionMismatchSupport, isCompact_Icc, ?_⟩
  intro mu hmu
  rcases hmu with ⟨n, rfl⟩
  rw [iid_normalizedPositiveWeightedMismatchMeasure_compl_uniformSupport_eq_zero
    ensemble (omega n) sign (hmass n)]
  exact hepsilon.le

/-- Under the explicit simple-spectrum hypotheses, the varying-size
tuple-normalized family is both tight and uniformly bounded in total mass. -/
theorem iid_varyingSize_tupleNormalizedCollision_tight_and_mass_uniform
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)] (omega : Nat → Omega)
    (sign : Fin 3 → InteractionSign)
    (hsimple : ∀ n, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N n) (omega n)))) :
    IsTightMeasureSet (Set.range fun n ↦
        (tupleNormalizedPositiveWeightedMismatchFiniteMeasure
          (ensemble.restrictPositiveMass (N := N n) (omega n)) sign :
            Measure Real)) ∧
      ∀ n,
        (tupleNormalizedPositiveWeightedMismatchFiniteMeasure
          (ensemble.restrictPositiveMass (N := N n) (omega n)) sign).mass ≤
          frozenCollisionMassCeiling := by
  exact ⟨
    iid_varyingSize_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_range_isTight
      ensemble N omega sign,
    iid_varyingSize_tupleNormalizedPositiveWeightedMismatchFiniteMeasure_mass_uniform
      ensemble N omega sign hsimple⟩

end

end ArchonPhysics.FrozenUniformCollisionCompactSupport

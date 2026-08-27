import ArchonPhysics.BoundedMassCompactSupportedFiniteMeasureSubsequence
import ArchonPhysics.DecayChannelMismatchSectorWeakLimit

/-!
# Simultaneous compactness of the four decay-channel sectors

Every predicate-restricted sector is a positive submeasure of the complete
canonical collision measure.  Hence the four sectors inherit the same compact
mismatch support and any common upper bound for the complete per-site mass.
Successive applications of finite-measure compactness, followed by diagonal
subsequence extraction, produce one cofinal subsequence on which all four
sectors converge simultaneously.

This removes complete-sequence sector convergence as a prerequisite for the
sector recombination theorem.  It does not assert that either the all-distinct
or child-repeated cluster is exact-resonance-null.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.DecayChannelSectorSimultaneousCompactness

open ArchonPhysics
open ArchonPhysics.BoundedMassCompactSupportedFiniteMeasureSubsequence
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FrozenCollisionPerSiteNormalization
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Restricting the positive weighted mismatch sum to any tuple predicate
produces a submeasure of the complete positive weighted mismatch measure. -/
theorem positiveWeightedMismatchMeasureWhere_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign)
    (keep : OrderedModeTriple N -> Prop) :
    positiveWeightedMismatchMeasureWhere m sign keep <=
      positiveWeightedMismatchMeasure m sign := by
  classical
  unfold positiveWeightedMismatchMeasureWhere
    positiveWeightedMismatchMeasure
  apply Finset.sum_le_sum
  intro modes _hmodes
  by_cases hkeep : IsPositiveOrderedTriple m modes ∧ keep modes
  · have hpositive := hkeep.1
    simp [hkeep]
  · rw [if_neg hkeep]
    exact bot_le

/-- Every canonical per-site sector is a submeasure of the full canonical
decay-channel collision measure at the same volume. -/
theorem canonicalDecaySectorPerSiteMismatchFiniteMeasure_le_full
    (ensemble : IIDMassPhaseEnsemble Omega)
    (keep : {N : Nat} -> [NeZero N] -> OrderedModeTriple N -> Prop)
    (n : Nat) (omega : Omega) :
    (canonicalDecaySectorPerSiteMismatchFiniteMeasure
        ensemble keep n omega : Measure Real) <=
      (canonicalCollisionPerSiteFiniteMeasure
        ensemble decayInteractionSign n omega : Measure Real) := by
  unfold canonicalDecaySectorPerSiteMismatchFiniteMeasure
    canonicalCollisionPerSiteFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasureWhere
    perSitePositiveWeightedMismatchFiniteMeasure
  simp only [FiniteMeasure.toMeasure_smul]
  gcongr
  exact positiveWeightedMismatchMeasureWhere_le
    (ensemble.restrictPositiveMass (N := n + 2) omega)
    decayInteractionSign (keep (N := n + 2))

/-- The mass of every sector is at most the full per-site collision mass. -/
theorem canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_full
    (ensemble : IIDMassPhaseEnsemble Omega)
    (keep : {N : Nat} -> [NeZero N] -> OrderedModeTriple N -> Prop)
    (n : Nat) (omega : Omega) :
    (canonicalDecaySectorPerSiteMismatchFiniteMeasure
        ensemble keep n omega).mass <=
      (canonicalCollisionPerSiteFiniteMeasure
        ensemble decayInteractionSign n omega).mass := by
  apply ENNReal.coe_le_coe.mp
  rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass]
  exact canonicalDecaySectorPerSiteMismatchFiniteMeasure_le_full
    ensemble keep n omega Set.univ

/-- The predicate-restricted raw mismatch measure inherits the common frozen
compact support directly from its Dirac summands. -/
theorem iid_positiveWeightedMismatchMeasureWhere_compl_support_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (sign : Fin 3 -> InteractionSign)
    (keep : OrderedModeTriple N -> Prop) :
    positiveWeightedMismatchMeasureWhere
        (ensemble.restrictPositiveMass (N := N) omega) sign keep
        (collisionMismatchSupportᶜ) = 0 := by
  classical
  unfold positiveWeightedMismatchMeasureWhere
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro modes _hmodes
  by_cases hkeep : IsPositiveOrderedTriple
      (ensemble.restrictPositiveMass (N := N) omega) modes ∧ keep modes
  · rw [if_pos hkeep, Measure.smul_apply]
    simp [iid_orderedThreeWaveMismatch_mem_uniformSupport
      ensemble omega sign modes]
  · rw [if_neg hkeep]
    rfl

/-- Every canonical sector inherits the same compact mismatch support. -/
theorem canonicalDecaySectorPerSiteMismatchFiniteMeasure_compl_support_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (keep : {N : Nat} -> [NeZero N] -> OrderedModeTriple N -> Prop)
    (n : Nat) (omega : Omega) :
    (canonicalDecaySectorPerSiteMismatchFiniteMeasure
        ensemble keep n omega : Measure Real)
      (collisionMismatchSupportᶜ) = 0 := by
  unfold canonicalDecaySectorPerSiteMismatchFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasureWhere
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  change _ * positiveWeightedMismatchMeasureWhere
      (ensemble.restrictPositiveMass (N := n + 2) omega)
      decayInteractionSign (keep (N := n + 2))
      (collisionMismatchSupportᶜ) = 0
  rw [iid_positiveWeightedMismatchMeasureWhere_compl_support_eq_zero]
  simp

/-- A common mass ceiling for the full per-site measure yields one cofinal
subsequence on which all four decay sectors converge weakly. -/
theorem exists_simultaneous_decaySector_weaklyConvergent_subsequence
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (massCeiling : NNReal)
    (hmass : forall n,
      (canonicalCollisionPerSiteFiniteMeasure
        ensemble decayInteractionSign n omega).mass <= massCeiling) :
    exists allDistinct childRepeated parentChildOne parentChildTwo :
        FiniteMeasure Real,
      exists subsequence : Nat -> Nat,
        StrictMono subsequence /\
        Tendsto
          (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
            (fun {_N} _inst => AllDistinctModes) (subsequence j) omega)
          atTop (nhds allDistinct) /\
        Tendsto
          (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
            (fun {_N} _inst => ChildRepeated) (subsequence j) omega)
          atTop (nhds childRepeated) /\
        Tendsto
          (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
            (fun {_N} _inst => ParentChildOneRepeated) (subsequence j) omega)
          atTop (nhds parentChildOne) /\
        Tendsto
          (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
            (fun {_N} _inst => ParentChildTwoRepeated) (subsequence j) omega)
          atTop (nhds parentChildTwo) := by
  let allSource : Nat -> FiniteMeasure Real := fun n =>
    canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => AllDistinctModes) n omega
  let childSource : Nat -> FiniteMeasure Real := fun n =>
    canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => ChildRepeated) n omega
  let oneSource : Nat -> FiniteMeasure Real := fun n =>
    canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => ParentChildOneRepeated) n omega
  let twoSource : Nat -> FiniteMeasure Real := fun n =>
    canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => ParentChildTwoRepeated) n omega
  have hsupportCompact : IsCompact collisionMismatchSupport := by
    unfold collisionMismatchSupport
    exact isCompact_Icc
  obtain ⟨allDistinct, allSubsequence, hallMono, hallLimit⟩ :=
    exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_le
      allSource massCeiling collisionMismatchSupport hsupportCompact
      (fun n => by
        dsimp [allSource]
        exact
          (canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_full
            ensemble (fun {_N} _inst => AllDistinctModes) n omega).trans
              (hmass n))
      (fun n => by
        dsimp [allSource]
        exact
          canonicalDecaySectorPerSiteMismatchFiniteMeasure_compl_support_eq_zero
            ensemble (fun {_N} _inst => AllDistinctModes) n omega)
  obtain ⟨childRepeated, childSubsequence, hchildMono, hchildLimit⟩ :=
    exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_le
      (fun j => childSource (allSubsequence j))
      massCeiling collisionMismatchSupport hsupportCompact
      (fun j => by
        dsimp [childSource]
        exact
          (canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_full
            ensemble (fun {_N} _inst => ChildRepeated)
              (allSubsequence j) omega).trans
                (hmass (allSubsequence j)))
      (fun j => by
        dsimp [childSource]
        exact
          canonicalDecaySectorPerSiteMismatchFiniteMeasure_compl_support_eq_zero
            ensemble (fun {_N} _inst => ChildRepeated)
              (allSubsequence j) omega)
  obtain ⟨parentChildOne, oneSubsequence, honeMono, honeLimit⟩ :=
    exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_le
      (fun j => oneSource (allSubsequence (childSubsequence j)))
      massCeiling collisionMismatchSupport hsupportCompact
      (fun j => by
        dsimp [oneSource]
        exact
          (canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_full
            ensemble (fun {_N} _inst => ParentChildOneRepeated)
              (allSubsequence (childSubsequence j)) omega).trans
                (hmass (allSubsequence (childSubsequence j))))
      (fun j => by
        dsimp [oneSource]
        exact
          canonicalDecaySectorPerSiteMismatchFiniteMeasure_compl_support_eq_zero
            ensemble (fun {_N} _inst => ParentChildOneRepeated)
              (allSubsequence (childSubsequence j)) omega)
  obtain ⟨parentChildTwo, twoSubsequence, htwoMono, htwoLimit⟩ :=
    exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_le
      (fun j =>
        twoSource
          (allSubsequence (childSubsequence (oneSubsequence j))))
      massCeiling collisionMismatchSupport hsupportCompact
      (fun j => by
        dsimp [twoSource]
        exact
          (canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_full
            ensemble (fun {_N} _inst => ParentChildTwoRepeated)
              (allSubsequence (childSubsequence (oneSubsequence j)))
              omega).trans
                (hmass
                  (allSubsequence (childSubsequence (oneSubsequence j)))))
      (fun j => by
        dsimp [twoSource]
        exact
          canonicalDecaySectorPerSiteMismatchFiniteMeasure_compl_support_eq_zero
            ensemble (fun {_N} _inst => ParentChildTwoRepeated)
              (allSubsequence (childSubsequence (oneSubsequence j))) omega)
  let subsequence : Nat -> Nat := fun j =>
    allSubsequence
      (childSubsequence (oneSubsequence (twoSubsequence j)))
  have hsubsequenceMono : StrictMono subsequence :=
    hallMono.comp (hchildMono.comp (honeMono.comp htwoMono))
  have hallFinal := hallLimit.comp
    (hchildMono.tendsto_atTop.comp
      (honeMono.tendsto_atTop.comp htwoMono.tendsto_atTop))
  have hchildFinal := hchildLimit.comp
    (honeMono.tendsto_atTop.comp htwoMono.tendsto_atTop)
  have honeFinal := honeLimit.comp htwoMono.tendsto_atTop
  refine ⟨allDistinct, childRepeated, parentChildOne, parentChildTwo,
    subsequence, hsubsequenceMono, ?_, ?_, ?_, ?_⟩
  · simpa [subsequence, allSource, Function.comp_def] using hallFinal
  · simpa [subsequence, childSource, Function.comp_def] using hchildFinal
  · simpa [subsequence, oneSource, Function.comp_def] using honeFinal
  · simpa [subsequence, twoSource, Function.comp_def] using htwoLimit

/-- For simple frozen spectra, the existing universal per-site mass ceiling
discharges the sole compactness bound automatically. -/
theorem exists_simultaneous_decaySector_weaklyConvergent_subsequence_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (hsimple : forall n,
      SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    exists allDistinct childRepeated parentChildOne parentChildTwo :
        FiniteMeasure Real,
      exists subsequence : Nat -> Nat,
        StrictMono subsequence /\
        Tendsto
          (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
            (fun {_N} _inst => AllDistinctModes) (subsequence j) omega)
          atTop (nhds allDistinct) /\
        Tendsto
          (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
            (fun {_N} _inst => ChildRepeated) (subsequence j) omega)
          atTop (nhds childRepeated) /\
        Tendsto
          (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
            (fun {_N} _inst => ParentChildOneRepeated) (subsequence j) omega)
          atTop (nhds parentChildOne) /\
        Tendsto
          (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
            (fun {_N} _inst => ParentChildTwoRepeated) (subsequence j) omega)
          atTop (nhds parentChildTwo) := by
  let ceiling : NNReal :=
    ⟨canonicalCollisionPerSiteMassCeiling,
      canonicalCollisionPerSiteMassCeiling_nonneg⟩
  apply exists_simultaneous_decaySector_weaklyConvergent_subsequence
    ensemble omega ceiling
  intro n
  apply NNReal.coe_le_coe.mp
  change ((canonicalCollisionPerSiteFiniteMeasure
    ensemble decayInteractionSign n omega).mass : Real) <=
      canonicalCollisionPerSiteMassCeiling
  exact canonicalCollisionPerSiteFiniteMeasure_mass_le
    ensemble decayInteractionSign n omega (hsimple n)

end

end ArchonPhysics.DecayChannelSectorSimultaneousCompactness

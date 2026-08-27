import ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit

/-!
# Permutation symmetry of canonical joint-frequency measures

The three legs of the positive weighted joint-frequency measure are dummy
ordered summation indices.  The basis-free normalized interaction weight and
the positive-frequency filter are symmetric in those legs.  Consequently the
finite-volume joint measure, its canonical per-site rescaling, its Euclidean
probability normalization, and the deterministic thermodynamic limit are
invariant under every permutation of `Fin 3`.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalJointFrequencyPermutationSymmetry

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Coordinate permutation on plain frequency triples. -/
def permutePlainFrequencyTriple (e : Equiv.Perm (Fin 3))
    (frequency : Fin 3 -> Real) : Fin 3 -> Real :=
  frequency ∘ e

theorem continuous_permutePlainFrequencyTriple (e : Equiv.Perm (Fin 3)) :
    Continuous (permutePlainFrequencyTriple e) := by
  unfold permutePlainFrequencyTriple
  fun_prop

theorem measurable_permutePlainFrequencyTriple (e : Equiv.Perm (Fin 3)) :
    Measurable (permutePlainFrequencyTriple e) :=
  (continuous_permutePlainFrequencyTriple e).measurable

/-- Reindexing equivalence on complete ordered mode triples. -/
def permuteOrderedModeTriple {N : Nat} [NeZero N]
    (e : Equiv.Perm (Fin 3)) : OrderedModeTriple N ≃ OrderedModeTriple N where
  toFun modes := modes ∘ e
  invFun modes := modes ∘ e.symm
  left_inv modes := by
    funext r
    simp [Function.comp_apply]
  right_inv modes := by
    funext r
    simp [Function.comp_apply]

/-- The basis-free ordered interaction tensor square is symmetric in all
three legs, without any simple-spectrum assumption. -/
theorem harmonicOrderedInteractionWeightSq_perm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (e : Equiv.Perm (Fin 3)) :
    harmonicOrderedInteractionWeightSq m (modes ∘ e) =
      harmonicOrderedInteractionWeightSq m modes := by
  unfold harmonicOrderedInteractionWeightSq orderedInteractionWeightSq
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro l _hl
  exact Equiv.prod_comp e
    (fun r => projectedBondKernel (massWeightedDifferenceMatrix m)
      (harmonicHermitian m) (modes r) j l)

/-- The positive-frequency normalized basis-free interaction weight is
invariant under every permutation of its three legs. -/
theorem harmonicOrderedNormalizedInteractionWeight_perm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (e : Equiv.Perm (Fin 3)) :
    harmonicOrderedNormalizedInteractionWeight m (modes ∘ e) =
      harmonicOrderedNormalizedInteractionWeight m modes := by
  unfold harmonicOrderedNormalizedInteractionWeight
  rw [harmonicOrderedInteractionWeightSq_perm]
  congr 1
  exact Equiv.prod_comp e
    (fun r =>
      (2 * orderedModeFrequency (harmonicHermitian m) (modes r))⁻¹)

/-- Positivity of every leg is unchanged by reordering the legs. -/
theorem isPositiveOrderedTriple_perm_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (e : Equiv.Perm (Fin 3)) :
    IsPositiveOrderedTriple m (modes ∘ e) ↔
      IsPositiveOrderedTriple m modes := by
  constructor
  · intro h r
    simpa [Function.comp_apply] using h (e.symm r)
  · intro h r
    exact h (e r)

/-- Permuting the mode tuple permutes exactly the three recorded frequency
coordinates. -/
theorem orderedFrequencyTriple_comp_perm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (e : Equiv.Perm (Fin 3)) :
    orderedFrequencyTriple m (modes ∘ e) =
      permutePlainFrequencyTriple e (orderedFrequencyTriple m modes) := by
  rfl

/-- Fixed-volume weighted joint-frequency finite measures are invariant
under every coordinate permutation. -/
theorem map_positiveWeightedFrequencyTripleFiniteMeasure_perm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (e : Equiv.Perm (Fin 3)) :
    (positiveWeightedFrequencyTripleFiniteMeasure m).map
        (permutePlainFrequencyTriple e) =
      positiveWeightedFrequencyTripleFiniteMeasure m := by
  classical
  apply FiniteMeasure.toMeasure_injective
  change
    (positiveWeightedFrequencyTripleMeasure m).map
        (permutePlainFrequencyTriple e) =
      positiveWeightedFrequencyTripleMeasure m
  unfold positiveWeightedFrequencyTripleMeasure
  rw [Measure.map_finset_sum'
    (measurable_permutePlainFrequencyTriple e).aemeasurable]
  calc
    (∑ modes : OrderedModeTriple N,
        Measure.map (permutePlainFrequencyTriple e)
          (if IsPositiveOrderedTriple m modes then
            ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
              Measure.dirac (orderedFrequencyTriple m modes)
          else 0)) =
      ∑ modes : OrderedModeTriple N,
        (if IsPositiveOrderedTriple m (modes ∘ e) then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m (modes ∘ e)) •
            Measure.dirac (orderedFrequencyTriple m (modes ∘ e))
        else 0) := by
          apply Finset.sum_congr rfl
          intro modes _hmodes
          by_cases hpositive : IsPositiveOrderedTriple m modes
          · rw [if_pos hpositive,
              if_pos ((isPositiveOrderedTriple_perm_iff m modes e).2 hpositive),
              Measure.map_smul,
              Measure.map_dirac' (measurable_permutePlainFrequencyTriple e)]
            rw [harmonicOrderedNormalizedInteractionWeight_perm,
              orderedFrequencyTriple_comp_perm]
          · rw [if_neg hpositive,
              if_neg (mt (isPositiveOrderedTriple_perm_iff m modes e).1 hpositive)]
            simp
    _ = ∑ modes : OrderedModeTriple N,
        (if IsPositiveOrderedTriple m modes then
          ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
            Measure.dirac (orderedFrequencyTriple m modes)
        else 0) := by
          exact Equiv.sum_comp (permuteOrderedModeTriple e)
            (fun modes : OrderedModeTriple N =>
              if IsPositiveOrderedTriple m modes then
                ENNReal.ofReal
                    (harmonicOrderedNormalizedInteractionWeight m modes) •
                  Measure.dirac (orderedFrequencyTriple m modes)
              else 0)

/-- Canonical per-site finite joint measures inherit exact permutation
invariance at every sample and volume. -/
theorem map_canonicalJointFrequencyPerSiteFiniteMeasure_perm
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega)
    (e : Equiv.Perm (Fin 3)) :
    (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).map
        (permutePlainFrequencyTriple e) =
      canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega := by
  unfold canonicalJointFrequencyPerSiteFiniteMeasure
  rw [FiniteMeasure.map_smul,
    map_positiveWeightedFrequencyTripleFiniteMeasure_perm]

/-- Coordinate permutation on the Euclidean frequency-triple model. -/
def permuteEuclideanFrequencyTriple (e : Equiv.Perm (Fin 3))
    (frequency : EuclideanSpace Real (Fin 3)) :
    EuclideanSpace Real (Fin 3) :=
  plainFrequencyTripleToEuclidean
    (permutePlainFrequencyTriple e
      (euclideanFrequencyTripleToPlain frequency))

theorem continuous_permuteEuclideanFrequencyTriple
    (e : Equiv.Perm (Fin 3)) :
    Continuous (permuteEuclideanFrequencyTriple e) := by
  unfold permuteEuclideanFrequencyTriple
  exact continuous_plainFrequencyTripleToEuclidean.comp
    ((continuous_permutePlainFrequencyTriple e).comp
      continuous_euclideanFrequencyTripleToPlain)

theorem measurable_permuteEuclideanFrequencyTriple
    (e : Equiv.Perm (Fin 3)) :
    Measurable (permuteEuclideanFrequencyTriple e) :=
  (continuous_permuteEuclideanFrequencyTriple e).measurable

@[simp] theorem permuteEuclideanFrequencyTriple_plain
    (e : Equiv.Perm (Fin 3)) (frequency : Fin 3 -> Real) :
    permuteEuclideanFrequencyTriple e
        (plainFrequencyTripleToEuclidean frequency) =
      plainFrequencyTripleToEuclidean
        (permutePlainFrequencyTriple e frequency) := by
  simp [permuteEuclideanFrequencyTriple]

/-- The Euclidean per-site finite joint measure is invariant under every
coordinate permutation. -/
theorem map_canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_perm
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega)
    (e : Equiv.Perm (Fin 3)) :
    (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).map (permuteEuclideanFrequencyTriple e) =
      canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble n omega := by
  apply FiniteMeasure.toMeasure_injective
  unfold canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
  simp only [FiniteMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_permuteEuclideanFrequencyTriple e)
    measurable_plainFrequencyTripleToEuclidean]
  have hcomp :
      permuteEuclideanFrequencyTriple e ∘
          plainFrequencyTripleToEuclidean =
        plainFrequencyTripleToEuclidean ∘
          permutePlainFrequencyTriple e := by
    funext frequency
    exact permuteEuclideanFrequencyTriple_plain e frequency
  rw [hcomp, ← Measure.map_map
    measurable_plainFrequencyTripleToEuclidean
    (measurable_permutePlainFrequencyTriple e)]
  rw [← FiniteMeasure.toMeasure_map]
  rw [map_canonicalJointFrequencyPerSiteFiniteMeasure_perm]

/-- The normalized Euclidean canonical measure is exactly invariant under
every permutation whenever the finite collision mass is nonzero. -/
theorem map_canonicalEuclideanNormalizedJointFrequencyMeasure_perm
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega)
    (e : Equiv.Perm (Fin 3))
    (hmass :
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass ≠ 0) :
    ProbabilityMeasure.map
        (canonicalEuclideanNormalizedJointFrequencyMeasure ensemble n omega)
        (measurable_permuteEuclideanFrequencyTriple e).aemeasurable =
      canonicalEuclideanNormalizedJointFrequencyMeasure ensemble n omega := by
  have hmassEuclidean :
      (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass ≠ 0 := by
    rw [canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_mass_eq]
    exact hmass
  rw [canonicalEuclideanNormalizedJointFrequencyMeasure_eq_finite_normalize
    ensemble n omega hmass]
  rw [probabilityMeasure_map_finiteMeasure_normalize_eq
    (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure ensemble n omega)
    (permuteEuclideanFrequencyTriple e)
    (measurable_permuteEuclideanFrequencyTriple e) hmassEuclidean]
  rw [map_canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_perm]

/-- The deterministic joint-frequency thermodynamic limit is invariant
under every permutation of its three legs. -/
theorem map_canonicalJointFrequencyMeasureLimit_perm
    (ensemble : IIDMassPhaseEnsemble Omega) (e : Equiv.Perm (Fin 3)) :
    ProbabilityMeasure.map (canonicalJointFrequencyMeasureLimit ensemble)
        (measurable_permuteEuclideanFrequencyTriple e).aemeasurable =
      canonicalJointFrequencyMeasureLimit ensemble := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      (∀ n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega))) ∧
      Tendsto
        (fun n : Nat => canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble (n + 1) omega)
        atTop (nhds (canonicalJointFrequencyMeasureLimit ensemble)) := by
    filter_upwards
      [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalEuclideanNormalizedJointFrequencyMeasure_tendsto_limit_ae
        ensemble] with omega hsimple hlimit
    exact ⟨hsimple, hlimit⟩
  obtain ⟨omega, hsimple, hlimit⟩ := hevent.exists
  have hmapped :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n : Nat => canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble (n + 1) omega)
      (canonicalJointFrequencyMeasureLimit ensemble) hlimit
      (continuous_permuteEuclideanFrequencyTriple e)
  have hfixed : ∀ n : Nat,
      ProbabilityMeasure.map
          (canonicalEuclideanNormalizedJointFrequencyMeasure
            ensemble (n + 1) omega)
          (measurable_permuteEuclideanFrequencyTriple e).aemeasurable =
        canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble (n + 1) omega := by
    intro n
    exact map_canonicalEuclideanNormalizedJointFrequencyMeasure_perm
      ensemble (n + 1) omega e
        (canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
          ensemble (fun _ => InteractionSign.plus) (n + 1) omega
          (by omega) (by simpa [Nat.add_assoc] using hsimple n))
  have hmappedLimit :
      Tendsto
        (fun n : Nat =>
          canonicalEuclideanNormalizedJointFrequencyMeasure
            ensemble (n + 1) omega)
        atTop
        (nhds (ProbabilityMeasure.map
          (canonicalJointFrequencyMeasureLimit ensemble)
          (measurable_permuteEuclideanFrequencyTriple e).aemeasurable)) := by
    simpa only [hfixed] using hmapped
  exact tendsto_nhds_unique hmappedLimit hlimit

end

end ArchonPhysics.CanonicalJointFrequencyPermutationSymmetry

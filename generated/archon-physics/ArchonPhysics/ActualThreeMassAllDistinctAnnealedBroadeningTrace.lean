import ArchonPhysics.ActualLiftedMismatchSmallBall
import ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
import ArchonPhysics.BroadenedResonanceMeasure
import ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
import ArchonPhysics.DecayChannelSectorSimultaneousCompactness
import ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction

/-!
# Annealed all-distinct broadening from the actual three-mass chart

The finite-volume mismatch measure of one realization is atomic, so it has no
realization-wise Lebesgue density.  The legal use of three-mass spectral
averaging is instead conditional and annealed: freeze the complementary mass
coordinates, average the three selected iid masses through the genuine
lifted spectral chart, and only then integrate the frozen environment.

This module records that exact reconstruction for the all-distinct decay
sector and transports the actual regular/Jacobian and kernel-weighted bad
budgets to an annealed broadened trace bound.  It does not infer a quenched
bound, a volume-uniform budget, or positivity of the on-shell coefficient.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace

open ArchonPhysics
open ArchonPhysics.ActualLiftedMismatchSmallBall
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecayChannelSectorSimultaneousCompactness
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The genuine collision weight of one tuple after three-mass resampling,
retained only when its three ordered mode labels are distinct. -/
def actualThreeMassAllDistinctTupleWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (triple : MassTriple) : ENNReal := by
  classical
  exact if AllDistinctModes modes then
      actualThreeMassPositiveTupleWeight
        fixed site₀ site₁ site₂ modes triple
    else 0

theorem measurable_actualThreeMassAllDistinctTupleWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) :
    Measurable
      (actualThreeMassAllDistinctTupleWeight
        fixed site₀ site₁ site₂ modes) := by
  classical
  unfold actualThreeMassAllDistinctTupleWeight
  split_ifs
  · exact measurable_actualThreeMassPositiveTupleWeight
      fixed site₀ site₁ site₂ modes
  · exact measurable_const

/-- The broadened all-distinct collision trace of one deterministic positive
mass configuration, with the physical inverse-volume normalization. -/
def allDistinctPerSiteBroadenedTrace
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (T : Real) : ENNReal := by
  classical
  exact (N : ENNReal)⁻¹ *
    ∑ modes : OrderedModeTriple N,
      if IsPositiveOrderedTriple mass modes ∧ AllDistinctModes modes then
        ENNReal.ofReal
            (harmonicOrderedNormalizedInteractionWeight mass modes) *
          ENNReal.ofReal
            (normalizedFiniteTimeResonanceKernel
              (orderedThreeWaveMismatch mass sign modes) T)
      else 0

/-- Coordinatewise measurable mass samples give a measurable all-distinct
broadened trace. -/
theorem measurable_allDistinctPerSiteBroadenedTrace
    {Omega : Type*} [MeasurableSpace Omega]
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun omega => (massSample omega).mass site)
    (sign : Fin 3 → InteractionSign) {T : Real} (hT : 0 < T) :
    Measurable fun omega =>
      allDistinctPerSiteBroadenedTrace (massSample omega) sign T := by
  classical
  unfold allDistinctPerSiteBroadenedTrace
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro modes _hmodes
  by_cases hdistinct : AllDistinctModes modes
  · have hmatrix : Measurable fun omega =>
        harmonicHermitian (massSample omega) := by
      apply Measurable.subtype_mk
      exact
        MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
          massSample hmass
    have hfrequencies : Measurable fun omega => fun mode =>
        orderedModeFrequency
          (harmonicHermitian (massSample omega)) mode :=
      measurable_orderedModeFrequencies_unconditional
        (fun omega => harmonicHermitian (massSample omega)) hmatrix
    have hpositive : MeasurableSet {omega |
        IsPositiveOrderedTriple (massSample omega) modes} := by
      rw [show {omega |
          IsPositiveOrderedTriple (massSample omega) modes} =
          ⋂ r, {omega | 0 < orderedModeFrequency
            (harmonicHermitian (massSample omega)) (modes r)} by
        ext omega
        simp [IsPositiveOrderedTriple]]
      exact MeasurableSet.iInter fun r =>
        measurableSet_lt measurable_const hfrequencies.eval
    have hweight : Measurable fun omega =>
        ENNReal.ofReal
          (harmonicOrderedNormalizedInteractionWeight
            (massSample omega) modes) :=
      (measurable_harmonicOrderedNormalizedInteractionWeight
        massSample hmass modes).ennreal_ofReal
    have hmismatch : Measurable fun omega =>
        orderedThreeWaveMismatch (massSample omega) sign modes := by
      unfold orderedThreeWaveMismatch
      apply Finset.measurable_sum
      intro r _hr
      exact measurable_const.mul hfrequencies.eval
    have hkernel : Measurable fun omega =>
        ENNReal.ofReal
          (normalizedFiniteTimeResonanceKernel
            (orderedThreeWaveMismatch (massSample omega) sign modes) T) :=
      ((continuous_normalizedFiniteTimeResonanceKernel hT).measurable.comp
        hmismatch).ennreal_ofReal
    simp only [hdistinct, and_true]
    exact Measurable.ite hpositive (hweight.mul hkernel) measurable_const
  · simp [hdistinct]

/-- One conditionally resampled all-distinct broadened child law, summed over
all ordered tuples with the exact inverse-volume normalization. -/
def actualThreeMassAllDistinctConditionalBroadenedChildMeasure
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) (T : Real) : Measure (Real × Real) :=
  actualThreeMassConditionalPerSiteBroadenedChildMeasure
    fixed site₀ site₁ site₂ sign
    (actualThreeMassAllDistinctTupleWeight fixed site₀ site₁ site₂) T

/-- The conditional broadened child law is supported on the actual frozen
frequency square. -/
theorem actualThreeMassAllDistinctConditionalBroadenedChildMeasure_ae_mem
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) {T : Real} (hT : 0 < T) :
    ∀ᵐ pair ∂actualThreeMassAllDistinctConditionalBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign T,
      pair ∈ childFrequencySquare (Real.sqrt 5) := by
  classical
  unfold actualThreeMassAllDistinctConditionalBroadenedChildMeasure
    actualThreeMassConditionalPerSiteBroadenedChildMeasure
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro modes _hmodes
  unfold actualThreeMassConditionalTupleBroadenedChildMeasure
  apply (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_childFrequencySquare (Real.sqrt 5))).2
  apply (ae_withDensity_iff
    (measurable_liftedResonanceKernelDensity hT)).2
  filter_upwards
    [ae_map_actualThreeMassLiftedFrequencyChart_mem_childCylinder
      fixed hfixed site₀ site₁ site₂ sign modes
      (iidMassTripleLaw.withDensity
        (actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂ modes))]
      with value hvalue _hkernel
  exact hvalue.1

/-- Evaluating the conditional child law on its support square is the full
conditional broadened trace. -/
theorem actualThreeMassAllDistinctConditionalBroadenedChildMeasure_univ_eq
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) {T : Real} (hT : 0 < T) :
    actualThreeMassAllDistinctConditionalBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign T Set.univ =
      actualThreeMassAllDistinctConditionalBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign T
          (childFrequencySquare (Real.sqrt 5)) := by
  let source := actualThreeMassAllDistinctConditionalBroadenedChildMeasure
    fixed site₀ site₁ site₂ sign T
  have hrestrict : source.restrict
      (childFrequencySquare (Real.sqrt 5)) = source :=
    Measure.restrict_eq_self_of_ae_mem
      (actualThreeMassAllDistinctConditionalBroadenedChildMeasure_ae_mem
        fixed hfixed site₀ site₁ site₂ sign hT)
  have happ := congrArg (fun measure : Measure (Real × Real) =>
    measure Set.univ) hrestrict
  rw [Measure.restrict_apply MeasurableSet.univ] at happ
  simpa [source] using happ.symm

end


end ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace

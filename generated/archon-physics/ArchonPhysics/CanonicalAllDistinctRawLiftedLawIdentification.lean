import ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeTrace
import ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
import ArchonPhysics.CanonicalChildAtlasTraceCertificateBridge

/-!
# Exact raw all-distinct lifted-law identification

The actual three-mass coarea law is the conditional iid average of the
finite-volume **all-distinct** collision sector.  This file proves that
identification before resonance broadening, first for a frozen complement and
then after the exact finite-volume iid Fubini decomposition.

The complete canonical joint law also contains mode-equality sectors.  In
particular, the child-repeated sector is carried by the plane where its two
child frequencies agree.  We therefore also prove the precise obstruction:
three-dimensional Lebesgue domination of the complete lifted law forces its
entire child-frequency diagonal mass to vanish.  Thus iid mass density by
itself identifies the all-distinct conditional law, but it cannot turn a
possibly nonzero child-repeated diagonal component into a three-dimensional
density.
-/

namespace ArchonPhysics.CanonicalAllDistinctRawLiftedLawIdentification

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeTrace
open ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalOnShellChildPairUniformIntegrabilityClosure
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## The exact finite-volume raw lifted sector -/

/-- The raw `(child frequency pair, signed mismatch)` observable on a plain
frequency triple. -/
def plainChildMismatchCoordinates
    (sign : Fin 3 -> InteractionSign) (frequency : Fin 3 -> Real) :
    MassTriple :=
  ((frequency 1, frequency 2), frequencyTripleMismatch sign frequency)

theorem continuous_plainChildMismatchCoordinates
    (sign : Fin 3 -> InteractionSign) :
    Continuous (plainChildMismatchCoordinates sign) := by
  unfold plainChildMismatchCoordinates
  exact ((continuous_apply 1).prodMk (continuous_apply 2)).prodMk (by
    unfold frequencyTripleMismatch
    apply continuous_finsetSum
    intro r _hr
    exact continuous_const.mul (continuous_apply r))

theorem measurable_plainChildMismatchCoordinates
    (sign : Fin 3 -> InteractionSign) :
    Measurable (plainChildMismatchCoordinates sign) :=
  (continuous_plainChildMismatchCoordinates sign).measurable

/-- The all-distinct part of one finite-volume per-site joint law, pushed to
the exact three-dimensional chart coordinates used by the actual coarea
construction. -/
def allDistinctPerSiteRawLiftedMeasure
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) : Measure MassTriple :=
  Measure.map (plainChildMismatchCoordinates sign)
    (perSitePositiveWeightedFrequencyTripleMeasureWhere
      mass AllDistinctModes)

/-- The measurable atom integrand obtained by evaluating one actual
three-mass chart pushforward on a measurable target. -/
def actualThreeMassAllDistinctRawAtomIntegrand
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site0 site1 site2 : Lattice.Site N)
    (sign : Fin 3 -> InteractionSign) (modes : OrderedModeTriple N)
    (A : Set MassTriple) (triple : MassTriple) : ENNReal :=
  actualThreeMassAllDistinctTupleWeight
      fixed site0 site1 site2 modes triple *
    A.indicator (1 : MassTriple → ENNReal)
      (actualThreeMassLiftedFrequencyChart
        fixed site0 site1 site2 sign modes triple)

theorem measurable_actualThreeMassAllDistinctRawAtomIntegrand
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site0 site1 site2 : Lattice.Site N)
    (sign : Fin 3 -> InteractionSign) (modes : OrderedModeTriple N)
    {A : Set MassTriple} (hA : MeasurableSet A) :
    Measurable (actualThreeMassAllDistinctRawAtomIntegrand
      fixed site0 site1 site2 sign modes A) := by
  apply (measurable_actualThreeMassAllDistinctTupleWeight
    fixed site0 site1 site2 modes).mul
  exact (Measurable.indicator measurable_const hA).comp
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site0 site1 site2 sign modes).measurable

/-- Evaluating the resampled finite-volume all-distinct raw sector gives the
normalized sum of the same chart atom integrands. -/
theorem allDistinctPerSiteRawLiftedMeasure_threeMassSiteConfig_apply
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site0 site1 site2 : Lattice.Site N)
    (sign : Fin 3 -> InteractionSign)
    {A : Set MassTriple} (hA : MeasurableSet A) (triple : MassTriple) :
    allDistinctPerSiteRawLiftedMeasure
        (threeMassSiteConfig fixed site0 site1 site2 triple) sign A =
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualThreeMassAllDistinctRawAtomIntegrand
            fixed site0 site1 site2 sign modes A triple := by
  classical
  unfold allDistinctPerSiteRawLiftedMeasure
    perSitePositiveWeightedFrequencyTripleMeasureWhere
    positiveWeightedFrequencyTripleMeasureWhere
    actualThreeMassAllDistinctRawAtomIntegrand
  rw [Measure.map_apply (measurable_plainChildMismatchCoordinates sign) hA,
    Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hdistinct : AllDistinctModes modes
  · by_cases hpositive : IsPositiveOrderedTriple
        (threeMassSiteConfig fixed site0 site1 site2 triple) modes
    · simp only [actualThreeMassAllDistinctTupleWeight, hdistinct,
        if_true, actualThreeMassPositiveTupleWeight, hpositive, and_self]
      rw [Measure.smul_apply, Measure.dirac_apply' _
        ((measurable_plainChildMismatchCoordinates sign) hA)]
      simp only [smul_eq_mul]
      change _ * A.indicator (1 : MassTriple → ENNReal)
          (plainChildMismatchCoordinates sign
            (orderedFrequencyTriple
              (threeMassSiteConfig fixed site0 site1 site2 triple) modes)) =
        _ * A.indicator (1 : MassTriple → ENNReal)
          (actualThreeMassLiftedFrequencyChart
            fixed site0 site1 site2 sign modes triple)
      rfl
    · simp [actualThreeMassAllDistinctTupleWeight,
        actualThreeMassPositiveTupleWeight, hdistinct, hpositive]
  · simp [actualThreeMassAllDistinctTupleWeight, hdistinct]

/-- The genuine actual three-mass raw lifted law is exactly the conditional
iid average of the finite-volume all-distinct sector, on every measurable
target set. -/
theorem actualThreeMassAllDistinctJointLiftedMeasure_apply_eq_lintegral_raw
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site0 site1 site2 : Lattice.Site N)
    (sign : Fin 3 -> InteractionSign)
    {A : Set MassTriple} (hA : MeasurableSet A) :
    actualThreeMassAllDistinctJointLiftedMeasure
        fixed site0 site1 site2 sign A =
      ∫⁻ triple,
        allDistinctPerSiteRawLiftedMeasure
          (threeMassSiteConfig fixed site0 site1 site2 triple) sign A
        ∂iidMassTripleLaw := by
  classical
  rw [show (∫⁻ triple,
        allDistinctPerSiteRawLiftedMeasure
          (threeMassSiteConfig fixed site0 site1 site2 triple) sign A
        ∂iidMassTripleLaw) =
      ∫⁻ triple, (N : ENNReal)⁻¹ *
        (∑ modes : OrderedModeTriple N,
          actualThreeMassAllDistinctRawAtomIntegrand
            fixed site0 site1 site2 sign modes A triple)
        ∂iidMassTripleLaw by
      apply lintegral_congr
      intro triple
      exact allDistinctPerSiteRawLiftedMeasure_threeMassSiteConfig_apply
        fixed site0 site1 site2 sign hA triple]
  rw [lintegral_const_mul _
      (Finset.measurable_sum _ fun modes _ =>
        measurable_actualThreeMassAllDistinctRawAtomIntegrand
          fixed site0 site1 site2 sign modes hA),
    lintegral_finsetSum Finset.univ (fun modes _ =>
      measurable_actualThreeMassAllDistinctRawAtomIntegrand
        fixed site0 site1 site2 sign modes hA)]
  unfold actualThreeMassAllDistinctJointLiftedMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  unfold actualThreeMassAllDistinctRawAtomIntegrand
  rw [Measure.map_apply
      (continuous_actualThreeMassLiftedFrequencyChart
        fixed site0 site1 site2 sign modes).measurable hA,
    withDensity_apply _
      ((continuous_actualThreeMassLiftedFrequencyChart
        fixed site0 site1 site2 sign modes).measurable hA),
    <- lintegral_indicator
      ((continuous_actualThreeMassLiftedFrequencyChart
        fixed site0 site1 site2 sign modes).measurable hA)]
  apply lintegral_congr
  intro triple
  by_cases hmem : actualThreeMassLiftedFrequencyChart
      fixed site0 site1 site2 sign modes triple ∈ A
  · simp [hmem]
  · simp [hmem]

/-! ## Exact finite-volume iid Fubini identification -/

/-- Evaluation of the raw all-distinct lifted sector is measurable for every
coordinatewise measurable positive-mass sample. -/
theorem measurable_allDistinctPerSiteRawLiftedMeasure_apply
    {X : Type*} [MeasurableSpace X]
    {N : Nat} [NeZero N]
    (massSample : X -> Lattice.PositiveMassConfig N)
    (hmass : forall site, Measurable fun x => (massSample x).mass site)
    (sign : Fin 3 -> InteractionSign)
    {A : Set MassTriple} (hA : MeasurableSet A) :
    Measurable fun x =>
      allDistinctPerSiteRawLiftedMeasure (massSample x) sign A := by
  classical
  have hmatrix : Measurable fun x => harmonicHermitian (massSample x) := by
    apply Measurable.subtype_mk
    exact
      MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
        massSample hmass
  have hfrequencies : Measurable fun x => fun mode =>
      orderedModeFrequency (harmonicHermitian (massSample x)) mode :=
    measurable_orderedModeFrequencies_unconditional
      (fun x => harmonicHermitian (massSample x)) hmatrix
  have hweight (modes : OrderedModeTriple N) : Measurable fun x =>
      ENNReal.ofReal
        (harmonicOrderedNormalizedInteractionWeight (massSample x) modes) :=
    (measurable_harmonicOrderedNormalizedInteractionWeight
      massSample hmass modes).ennreal_ofReal
  have hpositive (modes : OrderedModeTriple N) : MeasurableSet
      {x | IsPositiveOrderedTriple (massSample x) modes} := by
    rw [show {x | IsPositiveOrderedTriple (massSample x) modes} =
        ⋂ r, {x | 0 < orderedModeFrequency
          (harmonicHermitian (massSample x)) (modes r)} by
      ext x
      simp [IsPositiveOrderedTriple]]
    exact MeasurableSet.iInter fun r =>
      measurableSet_lt measurable_const hfrequencies.eval
  have htriple (modes : OrderedModeTriple N) : Measurable fun x =>
      orderedFrequencyTriple (massSample x) modes := by
    unfold orderedFrequencyTriple
    exact measurable_pi_lambda _ fun r => hfrequencies.eval
  have hpreimage : MeasurableSet
      (plainChildMismatchCoordinates sign ⁻¹' A) :=
    (measurable_plainChildMismatchCoordinates sign) hA
  have hsummand (modes : OrderedModeTriple N) : Measurable fun x =>
      (if IsPositiveOrderedTriple (massSample x) modes ∧
          AllDistinctModes modes then
        ENNReal.ofReal
            (harmonicOrderedNormalizedInteractionWeight
              (massSample x) modes) •
          Measure.dirac (orderedFrequencyTriple (massSample x) modes)
      else 0) (plainChildMismatchCoordinates sign ⁻¹' A) := by
    by_cases hdistinct : AllDistinctModes modes
    · simp only [hdistinct, and_true]
      have hdirac : Measurable fun x =>
          Measure.dirac (orderedFrequencyTriple (massSample x) modes) :=
        Measure.measurable_dirac.comp (htriple modes)
      have heval : Measurable fun x =>
          Measure.dirac (orderedFrequencyTriple (massSample x) modes)
            (plainChildMismatchCoordinates sign ⁻¹' A) :=
        (Measure.measurable_coe hpreimage).comp hdirac
      simp_rw [apply_ite (fun measure : Measure (Fin 3 → Real) =>
        measure (plainChildMismatchCoordinates sign ⁻¹' A))]
      apply Measurable.ite (hpositive modes)
      · simp_rw [Measure.smul_apply, smul_eq_mul]
        rw [show (fun x =>
            ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight
              (massSample x) modes) *
              Measure.dirac (orderedFrequencyTriple (massSample x) modes)
                (plainChildMismatchCoordinates sign ⁻¹' A)) =
            (fun x => ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight
                (massSample x) modes)) *
              (fun x => Measure.dirac
                (orderedFrequencyTriple (massSample x) modes)
                (plainChildMismatchCoordinates sign ⁻¹' A)) by
          funext x
          rfl]
        exact (hweight modes).mul heval
      · exact measurable_const
    · simp [hdistinct]
  unfold allDistinctPerSiteRawLiftedMeasure
    perSitePositiveWeightedFrequencyTripleMeasureWhere
    positiveWeightedFrequencyTripleMeasureWhere
  simp_rw [Measure.map_apply
      (measurable_plainChildMismatchCoordinates sign) hA,
    Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  exact measurable_const.mul
    (Finset.measurable_sum _ fun modes _ => hsummand modes)

/-- The ensemble average of the finite-volume raw all-distinct sector is
exactly the complementary-environment average of the genuine actual
three-mass lifted law.  This is the raw, pre-broadening Fubini identification
missing from the previous actual-chart API. -/
theorem lintegral_allDistinctPerSiteRawLiftedMeasure_eq_complement
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site0 site1 site2 : Lattice.Site N)
    (h01 : site0 ≠ site1) (h02 : site0 ≠ site2)
    (h12 : site1 ≠ site2)
    (sign : Fin 3 -> InteractionSign)
    {A : Set MassTriple} (hA : MeasurableSet A) :
    (∫⁻ omega,
      allDistinctPerSiteRawLiftedMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign A
      ∂ensemble.probability) =
      ∫⁻ rest,
        actualThreeMassAllDistinctJointLiftedMeasure
          (finiteEnvironmentPositiveMassConfig site0 site1 site2 rest)
          site0 site1 site2 sign A
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site0 site1 site2) := by
  let observable : Lattice.PositiveMassConfig N -> ENNReal := fun mass =>
    allDistinctPerSiteRawLiftedMeasure mass sign A
  let _ : IsProbabilityMeasure iidMassPairLaw := by
    unfold iidMassPairLaw
    infer_instance
  let _ : IsProbabilityMeasure iidMassTripleLaw := by
    unfold iidMassTripleLaw
    infer_instance
  let _ : IsProbabilityMeasure (iidFiniteMassVectorLaw
      (finiteVolumeMassComplement site0 site1 site2)) := by
    unfold iidFiniteMassVectorLaw
    infer_instance
  have hobservable : Measurable fun state :
      MassTriple × FiniteMassVector
        (finiteVolumeMassComplement site0 site1 site2) =>
      observable (finiteVolumePositiveMassReconstruction
        site0 site1 site2 state) :=
    measurable_allDistinctPerSiteRawLiftedMeasure_apply
      (finiteVolumePositiveMassReconstruction site0 site1 site2)
      (fun site =>
        measurable_finiteVolumePositiveMassReconstruction_mass
          site0 site1 site2 site) sign hA
  calc
    (∫⁻ omega,
        observable (ensemble.restrictPositiveMass (N := N) omega)
        ∂ensemble.probability) =
      ∫⁻ state,
        observable (finiteVolumePositiveMassReconstruction
          site0 site1 site2 state)
        ∂(iidMassTripleLaw.prod
          (iidFiniteMassVectorLaw
            (finiteVolumeMassComplement site0 site1 site2))) :=
      lintegral_finiteVolumePositiveMassConfig_eq_massTriple_prod_complement
        ensemble site0 site1 site2 h01 h02 h12
          hobservable.aemeasurable
    _ = ∫⁻ rest,
        ∫⁻ triple,
          observable (finiteVolumePositiveMassReconstruction
            site0 site1 site2 (triple, rest))
          ∂iidMassTripleLaw
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site0 site1 site2) :=
      lintegral_prod_symm _ hobservable.aemeasurable
    _ = ∫⁻ rest,
        actualThreeMassAllDistinctJointLiftedMeasure
          (finiteEnvironmentPositiveMassConfig site0 site1 site2 rest)
          site0 site1 site2 sign A
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site0 site1 site2) := by
      apply lintegral_congr
      intro rest
      simpa [observable, finiteVolumePositiveMassReconstruction] using
        (actualThreeMassAllDistinctJointLiftedMeasure_apply_eq_lintegral_raw
          (finiteEnvironmentPositiveMassConfig site0 site1 site2 rest)
          site0 site1 site2 sign hA).symm

/-! ## The full-law diagonal obstruction -/

/-- The child-frequency diagonal in the raw lifted target space. -/
def liftedChildFrequencyDiagonal : Set MassTriple :=
  {point | point.1.1 = point.1.2}

theorem liftedChildFrequencyDiagonal_isClosed :
    IsClosed liftedChildFrequencyDiagonal := by
  exact isClosed_eq (continuous_fst.comp continuous_fst)
    (continuous_snd.comp continuous_fst)

theorem liftedChildFrequencyDiagonal_measurableSet :
    MeasurableSet liftedChildFrequencyDiagonal :=
  liftedChildFrequencyDiagonal_isClosed.measurableSet

/-- The lifted child-frequency diagonal is null for three-dimensional
Lebesgue measure. -/
theorem volume_liftedChildFrequencyDiagonal :
    (((volume : Measure (Real × Real)).prod (volume : Measure Real))
      liftedChildFrequencyDiagonal) = 0 := by
  let pairDiagonal : Set (Real × Real) := {pair | pair.1 = pair.2}
  have hpairMeasurable : MeasurableSet pairDiagonal :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hpairZero : (volume : Measure (Real × Real)) pairDiagonal = 0 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.measure_prod_null hpairMeasurable).2
    filter_upwards with x
    simp [pairDiagonal]
  have heq : liftedChildFrequencyDiagonal =
      pairDiagonal ×ˢ (Set.univ : Set Real) := by
    ext point
    simp [liftedChildFrequencyDiagonal, pairDiagonal]
  rw [heq, Measure.prod_prod, hpairZero]
  simp

/-- The Euclidean lifted observable lands on its child-frequency diagonal
exactly when the two Euclidean child coordinates agree. -/
theorem preimage_liftedChildFrequencyDiagonal_euclidean
    (sign : Fin 3 -> InteractionSign) :
    euclideanChildMismatchCoordinates sign ⁻¹'
        liftedChildFrequencyDiagonal =
      {frequency : EuclideanSpace Real (Fin 3) |
        (euclideanFrequencyTripleToPlain frequency) 1 =
          (euclideanFrequencyTripleToPlain frequency) 2} := by
  ext frequency
  simp [liftedChildFrequencyDiagonal, euclideanChildMismatchCoordinates,
    CanonicalOnShellChildPairUniformIntegrability.childMismatchCoordinates,
    euclideanChildFrequencyPair]

/-- A full three-dimensional lifted density bound forces the deterministic
canonical joint-frequency target to have zero mass on the entire child
frequency diagonal.  This necessary condition is not supplied by iid mass
density and is incompatible with retaining an arbitrary nonzero
child-repeated singular component. -/
theorem canonical_childFrequencyDiagonal_eq_zero_of_euclidean_lifted_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (C : ENNReal)
    (hlifted :
      Measure.map (euclideanChildMismatchCoordinates sign)
          (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
            Measure (EuclideanSpace Real (Fin 3))) <=
        C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))) :
    (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
        Measure (EuclideanSpace Real (Fin 3)))
      {frequency |
        (euclideanFrequencyTripleToPlain frequency) 1 =
          (euclideanFrequencyTripleToPlain frequency) 2} = 0 := by
  have hmapZero : Measure.map (euclideanChildMismatchCoordinates sign)
      (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
        Measure (EuclideanSpace Real (Fin 3)))
      liftedChildFrequencyDiagonal = 0 := by
    apply le_antisymm _ bot_le
    calc
      _ <= (C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))) liftedChildFrequencyDiagonal :=
        (Measure.le_iff.mp hlifted) liftedChildFrequencyDiagonal
          liftedChildFrequencyDiagonal_measurableSet
      _ = 0 := by
        rw [Measure.smul_apply, volume_liftedChildFrequencyDiagonal]
        simp
  rw [Measure.map_apply
      (measurable_euclideanChildMismatchCoordinates sign)
      liftedChildFrequencyDiagonal_measurableSet,
    preimage_liftedChildFrequencyDiagonal_euclidean sign] at hmapZero
  exact hmapZero

end

end ArchonPhysics.CanonicalAllDistinctRawLiftedLawIdentification

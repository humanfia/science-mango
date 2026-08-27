import ArchonPhysics.CanonicalCollisionPolynomialApproximationScheme
import ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
import ArchonPhysics.HarmonicComplexThreeLegKernelApproximation
import ArchonPhysics.JointFrequencyThreeLegWeierstrassApproximation
import ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Canonical joint-frequency Fourier transform per site

For one fixed independent three-leg parameter, the exact positive weighted
frequency-triple Fourier sum is normalized by the volume N = n + 2.  A
countable family of six-polynomial approximations has deterministic local
window limits, while the harmonic edge frame gives a volume-uniform
replacement estimate whose error vanishes with the approximation index.

The exact joint Fourier sequence therefore has a deterministic almost-sure
thermodynamic limit.  All band, simplicity, and approximation premises are
discharged internally.  No weak limit of joint measures is asserted.
-/

namespace ArchonPhysics.CanonicalJointFrequencyFourierPerSiteLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionPolynomialApproximationScheme
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
open ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw
open ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.HarmonicComplexThreeLegKernelApproximation
open ArchonPhysics.HarmonicModes
open ArchonPhysics.JointFrequencyThreeLegWeierstrassApproximation
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedPhaseEffectiveWeightBound
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open ArchonPhysics.VanishingUniformApproximationLimit
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A chosen joint three-leg approximation at tolerance 1 / (k + 1).  Its
six coefficient families and common radius depend only on parameter and k. -/
def canonicalJointFrequencyPolynomialApproximation
    (parameter : Fin 3 -> Real) (k : Nat) :
    JointFrequencyThreeLegPolynomialApproximation parameter
      (collisionApproximationTolerance k) :=
  Classical.choice
    (exists_jointFrequencyThreeLegPolynomialApproximation parameter
      (collisionApproximationTolerance_pos k))

/-- The chosen object exposes all six approximation estimates and their
single common locality radius. -/
theorem canonicalJointFrequencyPolynomialApproximation_spec
    (parameter : Fin 3 -> Real) (k : Nat) :
    (forall r,
      (canonicalJointFrequencyPolynomialApproximation parameter k).cosineDegree r +
          1 <=
        (canonicalJointFrequencyPolynomialApproximation parameter k).windowRadius) ∧
    (forall r,
      (canonicalJointFrequencyPolynomialApproximation parameter k).sineDegree r +
          1 <=
        (canonicalJointFrequencyPolynomialApproximation parameter k).windowRadius) ∧
    (forall r lambda, lambda ∈ Icc (0 : Real) 5 ->
      abs ((∑ n ∈ Finset.range
          ((canonicalJointFrequencyPolynomialApproximation parameter k).cosineDegree r +
            1),
        (canonicalJointFrequencyPolynomialApproximation parameter k).cosineCoefficient
            r n * lambda ^ (n + 1)) -
        regularizedCosineLegWeight (parameter r) 1 lambda) <
          collisionApproximationTolerance k ∧
      abs ((∑ n ∈ Finset.range
          ((canonicalJointFrequencyPolynomialApproximation parameter k).sineDegree r +
            1),
        (canonicalJointFrequencyPolynomialApproximation parameter k).sineCoefficient
            r n * lambda ^ (n + 1)) -
        regularizedSineLegWeight (parameter r) 1 lambda) <
          collisionApproximationTolerance k) := by
  let approximation :=
    canonicalJointFrequencyPolynomialApproximation parameter k
  exact ⟨approximation.cosineDegree_le_radius,
    approximation.sineDegree_le_radius,
    fun r lambda hlambda =>
      ⟨approximation.cosine_error r lambda hlambda,
        approximation.sine_error r lambda hlambda⟩⟩

/-- The scalar physical effective-weight bound is independent of the three
joint Fourier parameters. -/
theorem norm_jointFrequencyPhysicalEffectiveWeight_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall q, orderedEigenvalue (harmonicHermitian m) q <= 5)
    (parameter : Fin 3 -> Real) (r : Fin 3) (q : OrderedModeIndex N) :
    ‖(orderedEigenvalue (harmonicHermitian m) q : Complex) *
        orderedJointFrequencyNormalizedPhaseLeg m parameter r q‖ <=
      collisionPhysicalEffectiveBound := by
  rw [orderedJointFrequencyNormalizedPhaseLeg_eq_plusPhaseLeg]
  exact norm_collisionPhysicalEffectiveWeight_le m hband
    (fun _ : Fin 3 => InteractionSign.plus) (parameter r) r q

/-- Each chosen joint polynomial effective leg is bounded by the common
physical bound plus its complex approximation error. -/
theorem norm_jointFrequencyPolynomialEffectiveWeight_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall q,
      orderedEigenvalue (harmonicHermitian m) q ∈ Icc (0 : Real) 5)
    (parameter : Fin 3 -> Real) (k : Nat)
    (r : Fin 3) (q : OrderedModeIndex N) :
    ‖(orderedEigenvalue (harmonicHermitian m) q : Complex) *
        complexSpectralPolynomialLegWeight (harmonicHermitian m)
          ((canonicalJointFrequencyPolynomialApproximation
            parameter k).cosineDegree r)
          ((canonicalJointFrequencyPolynomialApproximation
            parameter k).sineDegree r)
          ((canonicalJointFrequencyPolynomialApproximation
            parameter k).cosineCoefficient r)
          ((canonicalJointFrequencyPolynomialApproximation
            parameter k).sineCoefficient r) q‖ <=
      collisionPolynomialEffectiveBound k := by
  let approximation :=
    canonicalJointFrequencyPolynomialApproximation parameter k
  let physical : Complex :=
    (orderedEigenvalue (harmonicHermitian m) q : Complex) *
      orderedJointFrequencyNormalizedPhaseLeg m parameter r q
  let polynomial : Complex :=
    (orderedEigenvalue (harmonicHermitian m) q : Complex) *
      complexSpectralPolynomialLegWeight (harmonicHermitian m)
        (approximation.cosineDegree r) (approximation.sineDegree r)
        (approximation.cosineCoefficient r)
        (approximation.sineCoefficient r) q
  have hdifference : ‖physical - polynomial‖ <=
      collisionComplexEffectiveError k := by
    unfold collisionComplexEffectiveError
    exact
      (approximation.harmonic_complex_effectiveWeight_error
        m hband r q).le
  have hphysical : ‖physical‖ <= collisionPhysicalEffectiveBound := by
    exact norm_jointFrequencyPhysicalEffectiveWeight_le m
      (fun p => (hband p).2) parameter r q
  change ‖polynomial‖ <= collisionPolynomialEffectiveBound k
  calc
    ‖polynomial‖ = ‖(polynomial - physical) + physical‖ := by
      rw [sub_add_cancel]
    _ <= ‖polynomial - physical‖ + ‖physical‖ := norm_add_le _ _
    _ <= collisionComplexEffectiveError k +
        collisionPhysicalEffectiveBound := by
      exact add_le_add (by simpa [norm_sub_rev] using hdifference) hphysical
    _ = collisionPolynomialEffectiveBound k := by
      unfold collisionPolynomialEffectiveBound
      ring

/-- The exact positive weighted joint frequency-triple Fourier transform per
site at volume N = n + 2. -/
def canonicalJointFrequencyFourierPerSite
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (n : Nat) (omega : Omega) : Complex :=
  positiveWeightedFrequencyTripleFourierSum
      (ensemble.restrictPositiveMass (N := n + 2) omega) parameter /
    (((n + 2 : Nat) : Real) : Complex)

/-- Row k of the chosen joint polynomial approximation at the same volume. -/
def canonicalJointFrequencyPolynomialPerSite
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (k n : Nat) (omega : Omega) : Complex :=
  canonicalPositiveVolumeComplexSpectralPolynomialMoment ensemble
    (canonicalJointFrequencyPolynomialApproximation parameter k).cosineDegree
    (canonicalJointFrequencyPolynomialApproximation parameter k).sineDegree
    (canonicalJointFrequencyPolynomialApproximation
      parameter k).cosineCoefficient
    (canonicalJointFrequencyPolynomialApproximation parameter k).sineCoefficient
    (n + 1) omega

/-- Deterministic local-window limit of joint approximation row k. -/
def canonicalJointFrequencyPolynomialLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (k : Nat) : Complex :=
  let approximation :=
    canonicalJointFrequencyPolynomialApproximation parameter k
  complexWindowMean ensemble (2 * approximation.windowRadius + 1)
    (complexPolynomialRowWindowObservable approximation.windowRadius
      approximation.cosineDegree approximation.sineDegree
      approximation.cosineCoefficient approximation.sineCoefficient)

/-- Every fixed joint polynomial row converges almost surely along all
nondegenerate volumes N = n + 2. -/
theorem canonicalJointFrequencyPolynomialPerSite_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (k : Nat) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalJointFrequencyPolynomialPerSite
            ensemble parameter k n omega)
        atTop
        (nhds (canonicalJointFrequencyPolynomialLimit
          ensemble parameter k)) := by
  let approximation :=
    canonicalJointFrequencyPolynomialApproximation parameter k
  have hlimit :=
    canonicalPositiveVolumeComplexSpectralPolynomialMoment_strongLaw_ae
      ensemble approximation.windowRadius
      approximation.cosineDegree approximation.sineDegree
      approximation.cosineCoefficient approximation.sineCoefficient
      approximation.cosineDegree_le_radius
      approximation.sineDegree_le_radius
  filter_upwards [hlimit] with omega homega
  have hshift := homega.comp (tendsto_add_atTop_nat 1)
  change Tendsto
    (fun n : Nat =>
      canonicalPositiveVolumeComplexSpectralPolynomialMoment ensemble
        approximation.cosineDegree approximation.sineDegree
        approximation.cosineCoefficient approximation.sineCoefficient
        (n + 1) omega)
    atTop
    (nhds (complexWindowMean ensemble
      (2 * approximation.windowRadius + 1)
      (complexPolynomialRowWindowObservable approximation.windowRadius
        approximation.cosineDegree approximation.sineDegree
        approximation.cosineCoefficient approximation.sineCoefficient))) at hshift
  simpa [canonicalJointFrequencyPolynomialPerSite,
    canonicalJointFrequencyPolynomialLimit, approximation] using hshift

/-- At a simple frozen realization, exact joint Fourier/N and one chosen
polynomial row differ by the common volume-independent three-leg error. -/
theorem canonicalJointFrequencyFourierPerSite_sub_polynomial_norm_le_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (k n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    ‖canonicalJointFrequencyFourierPerSite ensemble parameter n omega -
        canonicalJointFrequencyPolynomialPerSite
          ensemble parameter k n omega‖ <=
      collisionThreeLegReplacementError k := by
  let m : Lattice.PositiveMassConfig (n + 2) :=
    ensemble.restrictPositiveMass omega
  let approximation :=
    canonicalJointFrequencyPolynomialApproximation parameter k
  let polynomialWeight : Fin 3 -> OrderedModeIndex (n + 2) -> Complex :=
    fun r => complexSpectralPolynomialLegWeight (harmonicHermitian m)
      (approximation.cosineDegree r) (approximation.sineDegree r)
      (approximation.cosineCoefficient r)
      (approximation.sineCoefficient r)
  have hband : forall q,
      orderedEigenvalue (harmonicHermitian m) q ∈ Icc (0 : Real) 5 := by
    intro q
    exact ⟨harmonicHermitian_orderedEigenvalue_nonneg m q,
      iid_orderedEigenvalue_harmonic_le_five ensemble omega q⟩
  have hdifference : forall r q,
      ‖(orderedEigenvalue (harmonicHermitian m) q : Complex) *
          orderedJointFrequencyNormalizedPhaseLeg m parameter r q -
        (orderedEigenvalue (harmonicHermitian m) q : Complex) *
          polynomialWeight r q‖ <= collisionComplexEffectiveError k := by
    intro r q
    simpa [polynomialWeight, approximation,
      collisionComplexEffectiveError] using
      le_of_lt (approximation.harmonic_complex_effectiveWeight_error
        m hband r q)
  have heffective : forall r q,
      ‖(orderedEigenvalue (harmonicHermitian m) q : Complex) *
          orderedJointFrequencyNormalizedPhaseLeg m parameter r q‖ <=
        collisionPhysicalEffectiveBound := by
    intro r q
    exact norm_jointFrequencyPhysicalEffectiveWeight_le m
      (fun p => (hband p).2) parameter r q
  have hpolynomialEffective : forall r q,
      ‖(orderedEigenvalue (harmonicHermitian m) q : Complex) *
          polynomialWeight r q‖ <= collisionPolynomialEffectiveBound k := by
    intro r q
    let exactWeight : Complex :=
      (orderedEigenvalue (harmonicHermitian m) q : Complex) *
        orderedJointFrequencyNormalizedPhaseLeg m parameter r q
    let approximateWeight : Complex :=
      (orderedEigenvalue (harmonicHermitian m) q : Complex) *
        polynomialWeight r q
    calc
      ‖approximateWeight‖ =
          ‖exactWeight - (exactWeight - approximateWeight)‖ := by
        congr 1
        abel
      _ <= ‖exactWeight‖ + ‖exactWeight - approximateWeight‖ :=
        norm_sub_le _ _
      _ <= collisionPhysicalEffectiveBound +
          collisionComplexEffectiveError k :=
        add_le_add (heffective r q) (hdifference r q)
      _ = collisionPolynomialEffectiveBound k := by
        rfl
  have hreplacement :=
    harmonic_threeLeg_complexProjectedKernel_replacementPerSite_norm_le
      m hsimple
      (fun r => orderedJointFrequencyNormalizedPhaseLeg m parameter r)
      polynomialWeight
      (fun _ => collisionComplexEffectiveError k)
      (fun _ => collisionPhysicalEffectiveBound)
      (fun _ => collisionPolynomialEffectiveBound k)
      (fun _ => collisionComplexEffectiveError_nonneg k)
      (fun _ => collisionPhysicalEffectiveBound_nonneg)
      (fun _ => collisionPolynomialEffectiveBound_nonneg k)
      hdifference heffective hpolynomialEffective
  have hleft :
      ‖canonicalJointFrequencyFourierPerSite ensemble parameter n omega -
          canonicalJointFrequencyPolynomialPerSite
            ensemble parameter k n omega‖ =
        ‖((∑ j, ∑ l, ∏ r : Fin 3,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix m) (harmonicHermitian m)
                (orderedJointFrequencyNormalizedPhaseLeg
                  m parameter r) j l) -
            (∑ j, ∑ l, ∏ r : Fin 3,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix m) (harmonicHermitian m)
                (polynomialWeight r) j l)) /
            (((n + 2 : Nat) : Real) : Complex)‖ := by
    unfold canonicalJointFrequencyFourierPerSite
      canonicalJointFrequencyPolynomialPerSite
      canonicalPositiveVolumeComplexSpectralPolynomialMoment
    change ‖positiveWeightedFrequencyTripleFourierSum m parameter /
          (((n + 2 : Nat) : Real) : Complex) -
        complexWeightedInteractionMoment (massWeightedDifferenceMatrix m)
          (harmonicHermitian m) polynomialWeight /
          (((n + 1 + 1 : Nat) : Real) : Complex)‖ = _
    rw [positiveWeightedFrequencyTripleFourierSum_factorization,
      complexWeightedInteractionMoment_factorization]
    have hdenominator :
        ((((n + 1 + 1 : Nat) : Real) : Complex)) =
          ((((n + 2 : Nat) : Real) : Complex)) := by
      rfl
    rw [hdenominator]
    rw [← sub_div]
  rw [hleft]
  simpa [collisionThreeLegReplacementError] using hreplacement

/-- On one probability-one event, every approximation row and volume satisfy
the same deterministic joint replacement estimate. -/
theorem canonicalJointFrequencyFourierPerSite_uniformApproximation_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) :
    ∀ᵐ omega ∂ensemble.probability, forall k n,
      dist (canonicalJointFrequencyFourierPerSite
          ensemble parameter n omega)
        (canonicalJointFrequencyPolynomialPerSite
          ensemble parameter k n omega) <=
      collisionThreeLegReplacementError k := by
  filter_upwards
    [canonicalPositiveVolumes_simpleOrderedSpectrum_ae ensemble] with
      omega hsimple
  intro k n
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega)) := by
    simpa [Nat.add_assoc] using hsimple (n + 1) (by omega)
  simpa [dist_eq_norm] using
    canonicalJointFrequencyFourierPerSite_sub_polynomial_norm_le_of_simple
      ensemble parameter k n omega hsimple'

/-- The exact positive weighted joint Fourier transform per site has a
deterministic almost-sure thermodynamic limit for each fixed parameter. -/
theorem exists_canonicalJointFrequencyFourierPerSite_limit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) :
    exists L : Complex,
      Tendsto
        (canonicalJointFrequencyPolynomialLimit ensemble parameter)
        atTop (nhds L) ∧
      ∀ᵐ omega ∂ensemble.probability,
        Tendsto
          (fun n : Nat =>
            canonicalJointFrequencyFourierPerSite
              ensemble parameter n omega)
          atTop (nhds L) := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  exact exists_commonLimit_ae_of_vanishing_uniformApproximation
    ensemble.probability
    (canonicalJointFrequencyFourierPerSite ensemble parameter)
    (canonicalJointFrequencyPolynomialPerSite ensemble parameter)
    (canonicalJointFrequencyPolynomialLimit ensemble parameter)
    collisionThreeLegReplacementError
    collisionThreeLegReplacementError_tendsto_zero
    (canonicalJointFrequencyPolynomialPerSite_strongLaw_ae
      ensemble parameter)
    (canonicalJointFrequencyFourierPerSite_uniformApproximation_ae
      ensemble parameter)

end

end ArchonPhysics.CanonicalJointFrequencyFourierPerSiteLimit

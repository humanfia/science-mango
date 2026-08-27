import ArchonPhysics.CanonicalCollisionPolynomialApproximationScheme
import ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
import ArchonPhysics.HarmonicComplexThreeLegKernelApproximation
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Canonical collision Fourier transform per site

For one fixed sign channel and time, the exact positive-mode mismatch
Fourier sum is normalized by the volume `N = n + 2`.  The canonical
Weierstrass approximants have deterministic local-window limits, while the
explicit harmonic edge frame gives a volume-uniform replacement estimate.
The replacement error vanishes, so the exact Fourier sequence and the
deterministic polynomial limits converge to one common deterministic value.

All spectrum, band, frame, and approximation hypotheses are discharged in
the theorem.  The volume starts at two only to avoid the degenerate
one-site cycle.
-/

namespace ArchonPhysics.CanonicalCollisionFourierPerSiteLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionPolynomialApproximationScheme
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
open ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw
open ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.ComplexThreeLegWeierstrassApproximation
open ArchonPhysics.HarmonicComplexThreeLegKernelApproximation
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedPhaseEffectiveWeightBound
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open ArchonPhysics.VanishingUniformApproximationLimit
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The exact positive-mode collision mismatch Fourier transform per site at
volume `N = n + 2`. -/
def canonicalCollisionFourierPerSite
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (n : Nat) (omega : Omega) : Complex :=
  positiveWeightedMismatchFourierSum
      (ensemble.restrictPositiveMass (N := n + 2) omega) sign time /
    (((n + 2 : Nat) : Real) : Complex)

/-- Row `k` of the canonical polynomial approximation, evaluated at the
same volume `N = n + 2` as the exact Fourier transform. -/
def canonicalCollisionPolynomialPerSite
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (k n : Nat) (omega : Omega) : Complex :=
  canonicalPositiveVolumeComplexSpectralPolynomialMoment ensemble
    (collisionPolynomialApproximation sign time k).cosineDegree
    (collisionPolynomialApproximation sign time k).sineDegree
    (collisionPolynomialApproximation sign time k).cosineCoefficient
    (collisionPolynomialApproximation sign time k).sineCoefficient
    (n + 1) omega

/-- The deterministic local-window limit of row `k`. -/
def canonicalCollisionPolynomialLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (k : Nat) : Complex :=
  let approximation := collisionPolynomialApproximation sign time k
  complexWindowMean ensemble (2 * approximation.windowRadius + 1)
    (complexPolynomialRowWindowObservable approximation.windowRadius
      approximation.cosineDegree approximation.sineDegree
      approximation.cosineCoefficient approximation.sineCoefficient)

/-- Every fixed polynomial row converges almost surely along the common
volume sequence `N = n + 2`. -/
theorem canonicalCollisionPolynomialPerSite_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real) (k : Nat) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalCollisionPolynomialPerSite ensemble sign time k n omega)
        atTop
        (nhds (canonicalCollisionPolynomialLimit ensemble sign time k)) := by
  let approximation := collisionPolynomialApproximation sign time k
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
  simpa [canonicalCollisionPolynomialPerSite,
    canonicalCollisionPolynomialLimit, approximation] using hshift

/-- At one simple-spectrum realization, the exact Fourier transform and a
chosen polynomial row differ by the canonical volume-independent error. -/
theorem canonicalCollisionFourierPerSite_sub_polynomial_norm_le_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (k n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    ‖canonicalCollisionFourierPerSite ensemble sign time n omega -
        canonicalCollisionPolynomialPerSite ensemble sign time k n omega‖ <=
      collisionThreeLegReplacementError k := by
  let m : Lattice.PositiveMassConfig (n + 2) :=
    ensemble.restrictPositiveMass omega
  let approximation := collisionPolynomialApproximation sign time k
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
          orderedNormalizedPhaseLeg m sign time r q -
        (orderedEigenvalue (harmonicHermitian m) q : Complex) *
          polynomialWeight r q‖ <= collisionComplexEffectiveError k := by
    intro r q
    simpa [polynomialWeight, approximation,
      collisionComplexEffectiveError] using
      le_of_lt (approximation.harmonic_complex_effectiveWeight_error
        m hband r q)
  have heffective : forall r q,
      ‖(orderedEigenvalue (harmonicHermitian m) q : Complex) *
          orderedNormalizedPhaseLeg m sign time r q‖ <=
        collisionPhysicalEffectiveBound := by
    intro r q
    simpa [collisionPhysicalEffectiveBound] using
      norm_eigenvalue_mul_orderedNormalizedPhaseLeg_le_sqrtFive_div_two
        m (fun p => (hband p).2) sign time r q
  have hpolynomialEffective : forall r q,
      ‖(orderedEigenvalue (harmonicHermitian m) q : Complex) *
          polynomialWeight r q‖ <= collisionPolynomialEffectiveBound k := by
    intro r q
    let exactWeight : Complex :=
      (orderedEigenvalue (harmonicHermitian m) q : Complex) *
        orderedNormalizedPhaseLeg m sign time r q
    let approximateWeight : Complex :=
      (orderedEigenvalue (harmonicHermitian m) q : Complex) *
        polynomialWeight r q
    calc
      ‖approximateWeight‖ = ‖exactWeight - (exactWeight - approximateWeight)‖ := by
        congr 1
        abel
      _ <= ‖exactWeight‖ + ‖exactWeight - approximateWeight‖ :=
        norm_sub_le _ _
      _ <= collisionPhysicalEffectiveBound + collisionComplexEffectiveError k :=
        add_le_add (heffective r q) (hdifference r q)
      _ = collisionPolynomialEffectiveBound k := by
        rfl
  have hreplacement :=
    harmonic_threeLeg_complexProjectedKernel_replacementPerSite_norm_le
      m hsimple
      (fun r => orderedNormalizedPhaseLeg m sign time r)
      polynomialWeight
      (fun _ => collisionComplexEffectiveError k)
      (fun _ => collisionPhysicalEffectiveBound)
      (fun _ => collisionPolynomialEffectiveBound k)
      (fun _ => collisionComplexEffectiveError_nonneg k)
      (fun _ => collisionPhysicalEffectiveBound_nonneg)
      (fun _ => collisionPolynomialEffectiveBound_nonneg k)
      hdifference heffective hpolynomialEffective
  have hleft :
      ‖canonicalCollisionFourierPerSite ensemble sign time n omega -
          canonicalCollisionPolynomialPerSite ensemble sign time k n omega‖ =
        ‖((∑ j, ∑ l, ∏ r : Fin 3,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix m) (harmonicHermitian m)
                (orderedNormalizedPhaseLeg m sign time r) j l) -
            (∑ j, ∑ l, ∏ r : Fin 3,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix m) (harmonicHermitian m)
                (polynomialWeight r) j l)) /
            (((n + 2 : Nat) : Real) : Complex)‖ := by
    unfold canonicalCollisionFourierPerSite
      canonicalCollisionPolynomialPerSite
      canonicalPositiveVolumeComplexSpectralPolynomialMoment
    change ‖positiveWeightedMismatchFourierSum m sign time /
          (((n + 2 : Nat) : Real) : Complex) -
        complexWeightedInteractionMoment (massWeightedDifferenceMatrix m)
          (harmonicHermitian m) polynomialWeight /
          (((n + 1 + 1 : Nat) : Real) : Complex)‖ = _
    rw [positiveWeightedMismatchFourierSum_factorization,
      complexWeightedInteractionMoment_factorization]
    have hdenominator :
        ((((n + 1 + 1 : Nat) : Real) : Complex)) =
          ((((n + 2 : Nat) : Real) : Complex)) := by
      rfl
    rw [hdenominator]
    rw [← sub_div]
  rw [hleft]
  simpa [collisionThreeLegReplacementError] using hreplacement

/-- On one probability-one event, every approximation row and every volume
obey the same deterministic replacement estimate. -/
theorem canonicalCollisionFourierPerSite_uniformApproximation_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real) :
    ∀ᵐ omega ∂ensemble.probability, forall k n,
      dist (canonicalCollisionFourierPerSite ensemble sign time n omega)
        (canonicalCollisionPolynomialPerSite ensemble sign time k n omega) <=
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
    canonicalCollisionFourierPerSite_sub_polynomial_norm_le_of_simple
      ensemble sign time k n omega hsimple'

/-- The exact positive-mode collision Fourier transform per site has a
deterministic almost-sure thermodynamic limit.  The chosen polynomial limits
converge to the same value. -/
theorem exists_canonicalCollisionFourierPerSite_limit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real) :
    exists L : Complex,
      Tendsto
        (canonicalCollisionPolynomialLimit ensemble sign time)
        atTop (nhds L) /\
      ∀ᵐ omega ∂ensemble.probability,
        Tendsto
          (fun n : Nat =>
            canonicalCollisionFourierPerSite ensemble sign time n omega)
          atTop (nhds L) := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  exact exists_commonLimit_ae_of_vanishing_uniformApproximation
    ensemble.probability
    (canonicalCollisionFourierPerSite ensemble sign time)
    (canonicalCollisionPolynomialPerSite ensemble sign time)
    (canonicalCollisionPolynomialLimit ensemble sign time)
    collisionThreeLegReplacementError
    collisionThreeLegReplacementError_tendsto_zero
    (canonicalCollisionPolynomialPerSite_strongLaw_ae ensemble sign time)
    (canonicalCollisionFourierPerSite_uniformApproximation_ae
      ensemble sign time)

end

end ArchonPhysics.CanonicalCollisionFourierPerSiteLimit

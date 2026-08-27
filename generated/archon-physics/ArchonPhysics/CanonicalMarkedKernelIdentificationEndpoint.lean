import ArchonPhysics.CanonicalCollisionFourierCompactUniformLimit
import ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
import ArchonPhysics.DeterministicPeriodicKernelWindowReindex
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Canonical marked-kernel identification endpoint

This module makes explicit the finite deterministic arrow which was implicit
between the continuous collision leg approximation and the local-window
strong-law observable.  At every volume, the exact collision Fourier sum per
site differs from an explicit centered translated-window average by the same
error depending only on the approximation index.  The error is independent
of the volume and tends to zero.

The existing complete-sequence rank--frequency marked-measure theorems are
then exposed as the qualitative varying-size endpoint.  No random-operator,
kinetic, or thermodynamic hypothesis is added here.  This module does not
claim a quantitative probability rate compatible with a joint kinetic
scaling.
-/

open scoped Topology

namespace ArchonPhysics.CanonicalMarkedKernelIdentificationEndpoint

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionFourierCompactUniformLimit
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionPolynomialApproximationScheme
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
open ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CanonicalThresholdCountMcDiarmid
open ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.DeterministicPeriodicKernelWindowReindex
open ArchonPhysics.HarmonicComplexThreeLegKernelApproximation
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PeriodicPolynomialWindowGeometricInterior
open ArchonPhysics.PeriodicPolynomialWindowReindex
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The explicit centered translated-window average associated with one
canonical collision-polynomial approximation. -/
def collisionPolynomialCenteredWindowAverage
    {m : Nat} [NeZero m]
    (sign : Fin 3 → InteractionSign) (time : Real) (k : Nat)
    (x : Fin
      ((2 * (collisionPolynomialApproximation sign time k).windowRadius + 1) +
        m) → Real) : Complex :=
  let approximation := collisionPolynomialApproximation sign time k
  let centerBig :=
    Fin.castAdd m (centeredWindowIndex approximation.windowRadius)
  (∑ target : Fin ((2 * approximation.windowRadius + 1) + m),
      complexPolynomialRowWindowObservable approximation.windowRadius
        approximation.cosineDegree approximation.sineDegree
        approximation.cosineCoefficient approximation.sineCoefficient
        (translatedMassWindow x
          (finCenteringShift centerBig target))) /
    ((((2 * approximation.windowRadius + 1) + m : Nat) : Real) : Complex)

/-- Generic deterministic replacement estimate on the frozen spectral band.
It is uniform in the finite volume and in the positive mass realization. -/
theorem positiveWeightedMismatchFourierSum_sub_polynomialMoment_norm_le
    {N : Nat} [NeZero N]
    (mass : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian mass))
    (hband : ∀ q,
      orderedEigenvalue (harmonicHermitian mass) q ∈ Icc (0 : Real) 5)
    (sign : Fin 3 → InteractionSign) (time : Real) (k : Nat) :
    let approximation := collisionPolynomialApproximation sign time k
    ‖positiveWeightedMismatchFourierSum mass sign time /
          (((N : Nat) : Real) : Complex) -
        complexWeightedInteractionMoment
          (massWeightedDifferenceMatrix mass) (harmonicHermitian mass)
          (fun r ↦ complexSpectralPolynomialLegWeight
            (harmonicHermitian mass)
            (approximation.cosineDegree r)
            (approximation.sineDegree r)
            (approximation.cosineCoefficient r)
            (approximation.sineCoefficient r)) /
          (((N : Nat) : Real) : Complex)‖ ≤
      collisionThreeLegReplacementError k := by
  dsimp only
  let approximation := collisionPolynomialApproximation sign time k
  let polynomialWeight : Fin 3 → OrderedModeIndex N → Complex :=
    fun r ↦ complexSpectralPolynomialLegWeight (harmonicHermitian mass)
      (approximation.cosineDegree r) (approximation.sineDegree r)
      (approximation.cosineCoefficient r)
      (approximation.sineCoefficient r)
  have hdifference : ∀ r q,
      ‖(orderedEigenvalue (harmonicHermitian mass) q : Complex) *
          orderedNormalizedPhaseLeg mass sign time r q -
        (orderedEigenvalue (harmonicHermitian mass) q : Complex) *
          polynomialWeight r q‖ ≤ collisionComplexEffectiveError k := by
    intro r q
    simpa [polynomialWeight, approximation,
      collisionComplexEffectiveError] using
      le_of_lt (approximation.harmonic_complex_effectiveWeight_error
        mass hband r q)
  have heffective : ∀ r q,
      ‖(orderedEigenvalue (harmonicHermitian mass) q : Complex) *
          orderedNormalizedPhaseLeg mass sign time r q‖ ≤
        collisionPhysicalEffectiveBound := by
    intro r q
    exact norm_collisionPhysicalEffectiveWeight_le mass
      (fun p ↦ (hband p).2) sign time r q
  have hpolynomialEffective : ∀ r q,
      ‖(orderedEigenvalue (harmonicHermitian mass) q : Complex) *
          polynomialWeight r q‖ ≤ collisionPolynomialEffectiveBound k := by
    intro r q
    exact norm_collisionPolynomialEffectiveWeight_le
      mass hband sign time k r q
  have hreplacement :=
    harmonic_threeLeg_complexProjectedKernel_replacementPerSite_norm_le
      mass hsimple
      (fun r ↦ orderedNormalizedPhaseLeg mass sign time r)
      polynomialWeight
      (fun _ ↦ collisionComplexEffectiveError k)
      (fun _ ↦ collisionPhysicalEffectiveBound)
      (fun _ ↦ collisionPolynomialEffectiveBound k)
      (fun _ ↦ collisionComplexEffectiveError_nonneg k)
      (fun _ ↦ collisionPhysicalEffectiveBound_nonneg)
      (fun _ ↦ collisionPolynomialEffectiveBound_nonneg k)
      hdifference heffective hpolynomialEffective
  rw [positiveWeightedMismatchFourierSum_factorization,
    complexWeightedInteractionMoment_factorization, ← sub_div]
  simpa [polynomialWeight, collisionThreeLegReplacementError] using
    hreplacement

/-- For an arbitrary finite real mass vector, clipping supplies the frozen
band automatically.  The exact continuous collision Fourier moment per site
is within the volume-independent canonical error of the explicit centered
translated-window average. -/
theorem clippedCollisionFourierPerSite_sub_centeredWindowAverage_norm_le
    {m : Nat} [NeZero m]
    (sign : Fin 3 → InteractionSign) (time : Real) (k : Nat)
    (x : Fin
      ((2 * (collisionPolynomialApproximation sign time k).windowRadius + 1) +
        m) → Real)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (clippedPositiveMassConfig (siteVectorOfFin x)))) :
    ‖positiveWeightedMismatchFourierSum
          (clippedPositiveMassConfig (siteVectorOfFin x)) sign time /
          (((((2 *
            (collisionPolynomialApproximation sign time k).windowRadius + 1) +
              m : Nat) : Real)) : Complex) -
        collisionPolynomialCenteredWindowAverage sign time k x‖ ≤
      collisionThreeLegReplacementError k := by
  let approximation := collisionPolynomialApproximation sign time k
  let mass := clippedPositiveMassConfig (siteVectorOfFin x)
  have hmassLower : ∀ i, RandomEnsemble.massLower ≤ mass.mass i := by
    intro i
    change RandomEnsemble.massLower ≤
      RandomEnsemble.clippedMass (siteVectorOfFin x i)
    exact (RandomEnsemble.clippedMass_mem_support _).1
  have hband : ∀ q,
      orderedEigenvalue (harmonicHermitian mass) q ∈ Icc (0 : Real) 5 := by
    intro q
    refine ⟨harmonicHermitian_orderedEigenvalue_nonneg mass q, ?_⟩
    simpa [RandomEnsemble.massLower] using
      orderedEigenvalue_harmonic_le_four_div_massLower
        mass RandomEnsemble.massLower RandomEnsemble.massLower_pos
        hmassLower q
  have hreplacement :=
    positiveWeightedMismatchFourierSum_sub_polynomialMoment_norm_le
      mass hsimple hband sign time k
  have hpolynomial :=
    complexWeightedInteractionPolynomialMomentPerSite_eq_centeredWindowAverage
      x hsimple approximation.cosineDegree approximation.sineDegree
      approximation.cosineCoefficient approximation.sineCoefficient
      approximation.cosineDegree_le_radius
      approximation.sineDegree_le_radius
  rw [show collisionPolynomialCenteredWindowAverage sign time k x =
      complexWeightedInteractionMoment
        (massWeightedDifferenceMatrix mass) (harmonicHermitian mass)
        (fun r ↦ complexSpectralPolynomialLegWeight
          (harmonicHermitian mass)
          (approximation.cosineDegree r) (approximation.sineDegree r)
          (approximation.cosineCoefficient r)
          (approximation.sineCoefficient r)) /
        (((((2 * approximation.windowRadius + 1) + m : Nat) : Real)) :
          Complex) by
    simpa [collisionPolynomialCenteredWindowAverage, approximation, mass]
      using hpolynomial.symm]
  simpa [approximation, mass] using hreplacement

/-- The preceding explicit finite-volume error is genuinely vanishing and
does not require a volume schedule. -/
theorem clippedCollisionCenteredWindowReplacementError_tendsto_zero :
    Tendsto collisionThreeLegReplacementError atTop (nhds 0) :=
  collisionThreeLegReplacementError_tendsto_zero

/-- Full qualitative varying-size marked-kernel identification: the complete
unnormalized rank--frequency marked finite measures converge almost surely,
along every canonical physical volume, to one deterministic per-site finite
measure. -/
theorem canonicalFullMarkedKernel_tendsto_limit_ae :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun n : Nat ↦ canonicalRankFrequencyTriplePerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble (n + 1) omega)
        atTop
        (nhds (canonicalRankFrequencyMarkedPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble)) :=
  canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendsto_limit_ae

/-- The same full marked-kernel limit in probability, for a pseudometric
which induces exactly the weak topology on finite measures. -/
theorem canonicalFullMarkedKernel_tendstoInMeasure_limit :
    let _ : PseudoMetricSpace
        (FiniteMeasure (Fin 3 → RankFrequencyMark)) :=
      canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (fun n omega ↦ canonicalRankFrequencyTriplePerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble (n + 1) omega)
      atTop
      (fun _omega ↦ canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble) :=
  canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendstoInMeasure_limit

/-- Every signed scalar collision kernel is exactly the corresponding
mismatch pushforward of the full deterministic marked-kernel limit. -/
theorem canonicalFullMarkedKernelLimit_map_mismatch
    (sign : Fin 3 → InteractionSign) :
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble).map
          (markedFrequencyMismatch sign) =
      canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign :=
  map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_eq_collision
    canonicalIIDMassPhaseEnsemble sign

end

end ArchonPhysics.CanonicalMarkedKernelIdentificationEndpoint

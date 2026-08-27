import ArchonPhysics.TwoScaleProbabilityDiagonalization
import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal

/-!
# Canonical broadened-mass two-scale diagonalization

At every fixed positive integer observation time, the complete-volume
canonical broadened marked collision mass converges almost surely, hence in
probability, to the deterministic scalar broadened coefficient.  Its
realization measurability is proved by transporting the marked mass to the
scalar mismatch measure and using measurability of integration against a
random measure.

The general two-scale theorem therefore supplies one deterministic volume
cutoff for every integer observation time.  The only remaining analytic input
for convergence along every admitted joint path is convergence of the
deterministic broadened coefficients to a proposed on-shell value.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalBroadenedMassTwoScaleDiagonalization

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenCollisionPerSiteNormalization
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TwoScaleProbabilityDiagonalization
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The real finite-volume broadened marked collision mass at integer time
`T = t + 1` and marked size `N + 1` (physical volume `N + 3`). -/
def canonicalBroadenedMarkedPerSiteMassSample
    (sign : Fin 3 -> InteractionSign) (t N : Nat)
    (omega : RandomEnsemble.SampleSpace) : Real :=
  ((canonicalRankFrequencyTripleBroadenedPerSiteFiniteMeasure
    canonicalIIDMassPhaseEnsemble (N + 1) omega sign
    ((t + 1 : Nat) : Real) (by positivity)).mass : Real)

/-- The deterministic scalar broadened collision coefficient at integer time
`T = t + 1`. -/
def canonicalBroadenedScalarCoefficient
    (sign : Fin 3 -> InteractionSign) (t : Nat) : Real :=
  ((canonicalBroadenedCollisionPerSiteMeasureLimit
    canonicalIIDMassPhaseEnsemble sign ((t + 1 : Nat) : Real)
    (by positivity)).mass : Real)

/-- At every finite volume, pushing the raw marked measure through its signed
mismatch gives exactly the scalar collision per-site measure. -/
theorem map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_markedMismatch
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega) :
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega).map
        (markedFrequencyMismatch sign) =
      canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega := by
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.toMeasure_map]
  change Measure.map
      (euclideanFrequencyTripleMismatch sign ∘
        forgetRankFrequencyTripleEuclidean)
      (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega :
        Measure _) = _
  rw [← Measure.map_map
    (continuous_euclideanFrequencyTripleMismatch sign).measurable
    measurable_forgetRankFrequencyTripleEuclidean]
  have hforget :
      Measure.map forgetRankFrequencyTripleEuclidean
          (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega :
            Measure _) =
        (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
          ensemble n omega : Measure _) := by
    simpa only [FiniteMeasure.toMeasure_map] using
      congrArg FiniteMeasure.toMeasure
        (map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_forgetRankEuclidean
          ensemble n omega)
  rw [hforget]
  exact congrArg FiniteMeasure.toMeasure
    (map_canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_eq_collisionPerSite
      ensemble sign n omega)

/-- The finite-volume marked broadened mass is exactly its scalar mismatch
broadening. -/
theorem canonicalBroadenedMarkedPerSiteMassSample_eq_scalar
    (sign : Fin 3 -> InteractionSign) (t N : Nat)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalBroadenedMarkedPerSiteMassSample sign t N omega =
      ((broadenedResonanceMeasure
        (canonicalCollisionPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble sign (N + 1) omega)
        id measurable_id ((t + 1 : Nat) : Real) (by positivity)).mass : Real) := by
  unfold canonicalBroadenedMarkedPerSiteMassSample
    canonicalRankFrequencyTripleBroadenedPerSiteFiniteMeasure
  rw [broadenedResonanceMeasure_mass_eq_map]
  rw [map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_markedMismatch]

/-- The canonical scalar collision measure is a measurable measure-valued
function of the random realization at every finite volume. -/
theorem measurable_canonicalCollisionPerSiteMeasure
    (sign : Fin 3 -> InteractionSign) (N : Nat) :
    Measurable fun omega =>
      (canonicalCollisionPerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble sign (N + 1) omega : Measure Real) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [canonicalCollisionPerSiteFiniteMeasure,
    perSitePositiveWeightedMismatchFiniteMeasure,
    positiveWeightedMismatchFiniteMeasure]
  exact measurable_const.mul
    ((Measure.measurable_coe hs).comp
      (measurable_canonicalPositiveWeightedMismatchMeasure sign))

/-- The real finite-volume broadened marked mass is a genuine measurable
random variable. -/
theorem measurable_canonicalBroadenedMarkedPerSiteMassSample
    (sign : Fin 3 -> InteractionSign) (t N : Nat) :
    Measurable (canonicalBroadenedMarkedPerSiteMassSample sign t N) := by
  have hkernel : Measurable fun x : Real =>
      ENNReal.ofReal (normalizedFiniteTimeResonanceKernel
        x ((t + 1 : Nat) : Real)) :=
    (continuous_normalizedFiniteTimeResonanceKernel
      (by positivity)).measurable.ennreal_ofReal
  have hlintegral : Measurable fun omega =>
      (∫⁻ x : Real, ENNReal.ofReal (normalizedFiniteTimeResonanceKernel
          x ((t + 1 : Nat) : Real))
        ∂(canonicalCollisionPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble sign (N + 1) omega : Measure Real)).toReal :=
    ((Measure.measurable_lintegral hkernel).comp
      (measurable_canonicalCollisionPerSiteMeasure sign N)).ennreal_toReal
  convert hlintegral using 1
  funext omega
  rw [canonicalBroadenedMarkedPerSiteMassSample_eq_scalar]
  rw [broadenedResonanceMeasure_mass_eq_integral]
  simp only [id_eq]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x =>
      normalizedFiniteTimeResonanceKernel_nonneg x ((t + 1 : Nat) : Real))
    (continuous_normalizedFiniteTimeResonanceKernel
      (by positivity)).aestronglyMeasurable]

/-- At every fixed integer observation time, the complete-volume broadened
marked mass converges in probability to the deterministic scalar broadened
coefficient. -/
theorem canonicalBroadenedMarkedPerSiteMass_tendstoInMeasure_fixedTime
    (sign : Fin 3 -> InteractionSign) (t : Nat) :
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (canonicalBroadenedMarkedPerSiteMassSample sign t)
      atTop (fun _omega => canonicalBroadenedScalarCoefficient sign t) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro N
    exact
      (measurable_canonicalBroadenedMarkedPerSiteMassSample
        sign t N).aestronglyMeasurable
  · have hmass :=
      canonicalRankFrequencyTripleBroadenedPerSiteMass_tendsto_scalar_limit_ae
        sign ((t + 1 : Nat) : Real) (by positivity)
    filter_upwards [hmass] with omega homega
    have hcoe := (NNReal.continuous_coe.tendsto _).comp homega
    convert hcoe using 1 <;>
      simp [canonicalBroadenedMarkedPerSiteMassSample,
        canonicalBroadenedScalarCoefficient, Function.comp_def]

/-- The deterministic size cutoff selected from all fixed-time canonical
convergence-in-probability statements. -/
def canonicalBroadenedMarkedPerSiteMassSizeCutoff
    (sign : Fin 3 -> InteractionSign) : Nat -> Nat :=
  twoScaleProbabilitySizeCutoff RandomEnsemble.canonicalLaw
    (canonicalBroadenedMarkedPerSiteMassSample sign)
    (canonicalBroadenedScalarCoefficient sign)
    (canonicalBroadenedMarkedPerSiteMass_tendstoInMeasure_fixedTime sign)

/-- If the deterministic scalar broadened coefficients converge to an
on-shell value, then every integer-time/volume path admitted by the canonical
cutoff converges in probability to that value. -/
theorem canonicalBroadenedMarkedPerSiteMass_tendstoInMeasure_along_cutoff
    (sign : Fin 3 -> InteractionSign) (onShellValue : Real)
    (hcoefficient : Tendsto (canonicalBroadenedScalarCoefficient sign)
      atTop (nhds onShellValue))
    (timeIndex sizeIndex : Nat -> Nat)
    (htime : Tendsto timeIndex atTop atTop)
    (hcutoff : ∀ᶠ j in atTop,
      canonicalBroadenedMarkedPerSiteMassSizeCutoff sign (timeIndex j) <=
        sizeIndex j) :
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (fun j omega => canonicalBroadenedMarkedPerSiteMassSample sign
        (timeIndex j) (sizeIndex j) omega)
      atTop (fun _omega => onShellValue) := by
  apply tendstoInMeasure_along_twoScaleProbabilitySizeCutoff
    RandomEnsemble.canonicalLaw
    (canonicalBroadenedMarkedPerSiteMassSample sign)
    (canonicalBroadenedScalarCoefficient sign) onShellValue
    (canonicalBroadenedMarkedPerSiteMass_tendstoInMeasure_fixedTime sign)
    hcoefficient timeIndex sizeIndex htime
  simpa [canonicalBroadenedMarkedPerSiteMassSizeCutoff] using hcutoff

end

end ArchonPhysics.CanonicalBroadenedMassTwoScaleDiagonalization

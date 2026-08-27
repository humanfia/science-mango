import ArchonPhysics.CanonicalCollisionFourierPerSiteLimit
import ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
import ArchonPhysics.DenseCharacteristicFunctionCompactness

/-!
# Canonical normalized collision-measure weak limit

At the nondegenerate volumes `N = n + 3`, the genuine positive weighted
mismatch measure is normalized by its total mass.  The deterministic
per-site Fourier limits, the extensive positive mass lower bound, and the
common compact mismatch support give almost-sure weak convergence to one
deterministic probability measure.

Only rational Fourier frequencies are intersected, so the almost-sure event
remains countable.  Spectral simplicity and nonzero collision mass are
discharged on that event and are not exposed in the endpoint.
-/

open scoped Topology

namespace ArchonPhysics.CanonicalCollisionMeasureWeakLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionFourierPerSiteLimit
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.DenseCharacteristicFunctionCompactness
open ArchonPhysics.FrozenCollisionMassExtensiveLowerBound
open ArchonPhysics.FrozenCollisionPerSiteNormalization
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
open ArchonPhysics.FrozenUniformCollisionMassBound
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A deterministic choice of the exact per-site Fourier limit. -/
def canonicalCollisionFourierLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real) : Complex :=
  Classical.choose
    (exists_canonicalCollisionFourierPerSite_limit_ae ensemble sign time)

/-- The chosen deterministic Fourier value is the almost-sure limit. -/
theorem canonicalCollisionFourierPerSite_tendsto_chosenLimit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalCollisionFourierPerSite ensemble sign time n omega)
        atTop (nhds (canonicalCollisionFourierLimit ensemble sign time)) := by
  exact (Classical.choose_spec
    (exists_canonicalCollisionFourierPerSite_limit_ae
      ensemble sign time)).2

/-- The same limit along the nondegenerate sequence `N = n + 3`. -/
theorem canonicalCollisionFourierPerSite_shift_tendsto_chosenLimit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalCollisionFourierPerSite ensemble sign time (n + 1) omega)
        atTop (nhds (canonicalCollisionFourierLimit ensemble sign time)) := by
  filter_upwards
    [canonicalCollisionFourierPerSite_tendsto_chosenLimit_ae
      ensemble sign time] with omega hlimit
  exact hlimit.comp (tendsto_add_atTop_nat 1)

/-- The genuine probability-normalized collision shape at volume
`N = n + 3`. -/
def canonicalCollisionNormalizedMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega) : ProbabilityMeasure Real :=
  normalizedPositiveWeightedMismatchMeasure
    (ensemble.restrictPositiveMass (N := n + 3) omega) sign

/-- One probability-one event carries simple ordered spectrum at every
volume `N = n + 3`. -/
theorem canonicalCollisionVolumes_simpleOrderedSpectrum_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability, forall n : Nat,
      SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega)) := by
  filter_upwards
    [canonicalPositiveVolumes_simpleOrderedSpectrum_ae ensemble] with
      omega hsimple
  intro n
  simpa [Nat.add_assoc] using hsimple (n + 2) (by omega)

/-- At a simple realization, the site-normalized collision mass at
`N = n + 3` has the fixed positive lower bound. -/
theorem canonicalCollisionPerSite_mass_lower_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega))) :
    iidCollisionWeightDensityLower <=
      ((canonicalCollisionPerSiteFiniteMeasure ensemble sign (n + 1) omega).mass :
        Real) := by
  simpa [canonicalCollisionPerSiteFiniteMeasure, Nat.add_assoc] using
    iidCollisionWeightDensityLower_le_perSite_mass
      ensemble omega (N := n + 3) (by omega) hsimple sign

/-- The same hypotheses discharge the nonzero-mass premise of probability
normalization. -/
theorem canonicalCollisionFiniteMeasure_mass_ne_zero_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega))) :
    (positiveWeightedMismatchFiniteMeasure
      (ensemble.restrictPositiveMass (N := n + 3) omega) sign).mass ≠ 0 := by
  have hlower := iid_collisionWeight_extensive_lower_toNNReal_le_mass
    ensemble omega (N := n + 3) (by omega) hsimple sign
  have hpositive : 0 <
      Real.toNNReal
        (iidCollisionWeightDensityLower * (((n + 3 : Nat) : Real))) := by
    exact Real.toNNReal_pos.mpr
      (mul_pos iidCollisionWeightDensityLower_pos (by positivity))
  exact ne_of_gt (hpositive.trans_le hlower)

/-- The zero-frequency deterministic limit is bounded away from zero. -/
theorem canonicalCollisionFourierLimit_zero_re_lower
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    iidCollisionWeightDensityLower <=
      (canonicalCollisionFourierLimit ensemble sign 0).re := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      (forall n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega))) ∧
      Tendsto
        (fun n : Nat =>
          canonicalCollisionFourierPerSite ensemble sign 0 (n + 1) omega)
        atTop (nhds (canonicalCollisionFourierLimit ensemble sign 0)) := by
    filter_upwards
      [canonicalCollisionVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalCollisionFourierPerSite_shift_tendsto_chosenLimit_ae
        ensemble sign 0] with omega hsimple hlimit
    exact ⟨hsimple, hlimit⟩
  obtain ⟨omega, hsimple, hlimit⟩ := hevent.exists
  have hlimitRe : Tendsto
      (fun n : Nat =>
        (canonicalCollisionFourierPerSite ensemble sign 0 (n + 1) omega).re)
      atTop
      (nhds (canonicalCollisionFourierLimit ensemble sign 0).re) :=
    (Complex.continuous_re.tendsto _).comp hlimit
  apply ge_of_tendsto' hlimitRe
  intro n
  have hzero : canonicalCollisionFourierPerSite ensemble sign 0 (n + 1) omega =
      (((canonicalCollisionPerSiteFiniteMeasure
        ensemble sign (n + 1) omega).mass : Real) : Complex) := by
    unfold canonicalCollisionFourierPerSite
    rw [← canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div,
      canonicalCollisionPerSiteFourierIntegral_zero]
  rw [hzero]
  exact canonicalCollisionPerSite_mass_lower_of_simple
    ensemble sign n omega (hsimple n)

/-- In particular, the zero-frequency deterministic denominator is
nonzero. -/
theorem canonicalCollisionFourierLimit_zero_ne_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    canonicalCollisionFourierLimit ensemble sign 0 ≠ 0 := by
  intro hzero
  have hlower := canonicalCollisionFourierLimit_zero_re_lower ensemble sign
  rw [hzero] at hlower
  simp only [Complex.zero_re] at hlower
  exact (not_lt_of_ge hlower) iidCollisionWeightDensityLower_pos


/-- Deterministic limiting characteristic-function value at a rational
frequency. -/
def canonicalCollisionNormalizedCharFunLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (q : Rat) : Complex :=
  canonicalCollisionFourierLimit ensemble sign (q : Real) /
    canonicalCollisionFourierLimit ensemble sign 0

/-- On one probability-one event, all rational characteristic functions of
the genuine normalized collision measures converge to deterministic ratios.
Only this countable event is used below. -/
theorem canonicalCollisionNormalizedMeasure_charFun_rat_tendsto_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    ∀ᵐ omega ∂ensemble.probability, forall q : Rat,
      Tendsto
        (fun n : Nat => charFun
          (canonicalCollisionNormalizedMeasure ensemble sign n omega :
            Measure Real) (q : Real))
        atTop
        (nhds (canonicalCollisionNormalizedCharFunLimit ensemble sign q)) := by
  have hratFourier : ∀ᵐ omega ∂ensemble.probability, forall q : Rat,
      Tendsto
        (fun n : Nat => canonicalCollisionFourierPerSite
          ensemble sign (q : Real) (n + 1) omega)
        atTop
        (nhds (canonicalCollisionFourierLimit ensemble sign (q : Real))) := by
    apply ae_all_iff.mpr
    intro q
    exact canonicalCollisionFourierPerSite_shift_tendsto_chosenLimit_ae
      ensemble sign (q : Real)
  filter_upwards
    [canonicalCollisionVolumes_simpleOrderedSpectrum_ae ensemble,
    canonicalCollisionFourierPerSite_shift_tendsto_chosenLimit_ae
      ensemble sign 0,
    hratFourier] with omega hsimple hzero hrat
  intro q
  have hratio := (hrat q).div hzero
    (canonicalCollisionFourierLimit_zero_ne_zero ensemble sign)
  unfold canonicalCollisionNormalizedCharFunLimit
  apply hratio.congr'
  exact Eventually.of_forall fun n => by
    have hchar :=
      charFun_normalizedPositiveWeightedMismatchMeasure_eq_perSiteFourier_ratio
        ensemble sign (q : Real) (n + 1) omega (by omega) (hsimple n)
    rw [canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div,
      canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div] at hchar
    simpa [canonicalCollisionNormalizedMeasure,
      canonicalCollisionFourierPerSite, Nat.add_assoc] using hchar.symm

/-- At a realization with simultaneous simplicity, the whole varying-volume
family of normalized collision shapes is tight. -/
theorem canonicalCollisionNormalizedMeasure_range_isTight_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (omega : Omega)
    (hsimple : forall n : Nat, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega))) :
    IsTightMeasureSet
      {((nu : ProbabilityMeasure Real) : Measure Real) |
        nu ∈ Set.range
          (fun n => canonicalCollisionNormalizedMeasure
            ensemble sign n omega)} := by
  have hset :
      {((nu : ProbabilityMeasure Real) : Measure Real) |
        nu ∈ Set.range
          (fun n => canonicalCollisionNormalizedMeasure
            ensemble sign n omega)} =
        Set.range (fun n =>
          (canonicalCollisionNormalizedMeasure ensemble sign n omega :
            Measure Real)) := by
    ext mu
    simp
  rw [hset]
  let _ : forall n : Nat, NeZero (n + 3) := fun n => ⟨by omega⟩
  have hmass : forall n,
      (positiveWeightedMismatchFiniteMeasure
        (ensemble.restrictPositiveMass (N := n + 3) omega) sign).mass ≠ 0 :=
    fun n => canonicalCollisionFiniteMeasure_mass_ne_zero_of_simple
      ensemble sign n omega (hsimple n)
  simpa [canonicalCollisionNormalizedMeasure] using
    iid_varyingSize_normalizedPositiveWeightedMismatchMeasure_range_isTight
      ensemble (fun n => n + 3) (fun _n => omega) sign hmass


/-- For every fixed ensemble and sign channel, the genuine normalized
positive weighted mismatch measures at N = n + 3 converge almost surely
to one deterministic probability measure. -/
theorem exists_canonicalCollisionNormalizedMeasure_weakLimit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    exists target : ProbabilityMeasure Real,
      ∀ᵐ omega ∂ensemble.probability,
        Tendsto
          (fun n : Nat =>
            canonicalCollisionNormalizedMeasure ensemble sign n omega)
          atTop (nhds target) := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      (forall n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega))) ∧
      (forall q : Rat, Tendsto
        (fun n : Nat => charFun
          (canonicalCollisionNormalizedMeasure ensemble sign n omega :
            Measure Real) (q : Real))
        atTop
        (nhds (canonicalCollisionNormalizedCharFunLimit ensemble sign q))) := by
    filter_upwards
      [canonicalCollisionVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalCollisionNormalizedMeasure_charFun_rat_tendsto_ae
        ensemble sign] with omega hsimple hrat
    exact ⟨hsimple, hrat⟩
  obtain ⟨omega0, hsimple0, hrat0⟩ := hevent.exists
  obtain ⟨target, htarget⟩ := exists_tendsto_of_tight_of_charFun_rat
    (fun n => canonicalCollisionNormalizedMeasure ensemble sign n omega0)
    (canonicalCollisionNormalizedMeasure_range_isTight_of_simple
      ensemble sign omega0 hsimple0)
    (fun q =>
      ⟨canonicalCollisionNormalizedCharFunLimit ensemble sign q, hrat0 q⟩)
  refine ⟨target, ?_⟩
  filter_upwards [hevent] with omega hgood
  rcases hgood with ⟨hsimple, hrat⟩
  obtain ⟨candidate, hcandidate⟩ := exists_tendsto_of_tight_of_charFun_rat
    (fun n => canonicalCollisionNormalizedMeasure ensemble sign n omega)
    (canonicalCollisionNormalizedMeasure_range_isTight_of_simple
      ensemble sign omega hsimple)
    (fun q =>
      ⟨canonicalCollisionNormalizedCharFunLimit ensemble sign q, hrat q⟩)
  have hcandidateTarget : candidate = target := by
    apply probabilityMeasure_eq_of_charFun_rat_eq
    intro q
    have hcandidateValue :
        charFun (candidate : Measure Real) (q : Real) =
          canonicalCollisionNormalizedCharFunLimit ensemble sign q :=
      tendsto_nhds_unique
        ((ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hcandidate)
          (q : Real))
        (hrat q)
    have htargetValue :
        charFun (target : Measure Real) (q : Real) =
          canonicalCollisionNormalizedCharFunLimit ensemble sign q :=
      tendsto_nhds_unique
        ((ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp htarget)
          (q : Real))
        (hrat0 q)
    exact hcandidateValue.trans htargetValue.symm
  simpa [hcandidateTarget] using hcandidate


/-- The deterministic probability-measure limit selected by the preceding
existence theorem. -/
def canonicalCollisionMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) : ProbabilityMeasure Real :=
  Classical.choose
    (exists_canonicalCollisionNormalizedMeasure_weakLimit_ae ensemble sign)

/-- The canonical normalized collision measures converge almost surely to
the selected deterministic target. -/
theorem canonicalCollisionNormalizedMeasure_tendsto_limit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalCollisionNormalizedMeasure ensemble sign n omega)
        atTop (nhds (canonicalCollisionMeasureLimit ensemble sign)) := by
  exact Classical.choose_spec
    (exists_canonicalCollisionNormalizedMeasure_weakLimit_ae ensemble sign)

/-- The full real characteristic function of the deterministic target is
the normalized exact per-site Fourier limit. -/
theorem charFun_canonicalCollisionMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real) :
    charFun (canonicalCollisionMeasureLimit ensemble sign : Measure Real) time =
      canonicalCollisionFourierLimit ensemble sign time /
        canonicalCollisionFourierLimit ensemble sign 0 := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      (forall n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega))) ∧
      Tendsto
        (fun n : Nat =>
          canonicalCollisionNormalizedMeasure ensemble sign n omega)
        atTop (nhds (canonicalCollisionMeasureLimit ensemble sign)) ∧
      Tendsto
        (fun n : Nat => canonicalCollisionFourierPerSite
          ensemble sign time (n + 1) omega)
        atTop (nhds (canonicalCollisionFourierLimit ensemble sign time)) ∧
      Tendsto
        (fun n : Nat => canonicalCollisionFourierPerSite
          ensemble sign 0 (n + 1) omega)
        atTop (nhds (canonicalCollisionFourierLimit ensemble sign 0)) := by
    filter_upwards
      [canonicalCollisionVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalCollisionNormalizedMeasure_tendsto_limit_ae ensemble sign,
      canonicalCollisionFourierPerSite_shift_tendsto_chosenLimit_ae
        ensemble sign time,
      canonicalCollisionFourierPerSite_shift_tendsto_chosenLimit_ae
        ensemble sign 0] with omega hsimple hweak htime hzero
    exact ⟨hsimple, hweak, htime, hzero⟩
  obtain ⟨omega, hsimple, hweak, htime, hzero⟩ := hevent.exists
  have hweakChar :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hweak) time
  have hratio := htime.div hzero
    (canonicalCollisionFourierLimit_zero_ne_zero ensemble sign)
  have hcharRatio : Tendsto
      (fun n : Nat => charFun
        (canonicalCollisionNormalizedMeasure ensemble sign n omega :
          Measure Real) time)
      atTop
      (nhds (canonicalCollisionFourierLimit ensemble sign time /
        canonicalCollisionFourierLimit ensemble sign 0)) := by
    apply hratio.congr'
    exact Eventually.of_forall fun n => by
      have hchar :=
        charFun_normalizedPositiveWeightedMismatchMeasure_eq_perSiteFourier_ratio
          ensemble sign time (n + 1) omega (by omega) (hsimple n)
      rw [canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div,
        canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div] at hchar
      simpa [canonicalCollisionNormalizedMeasure,
        canonicalCollisionFourierPerSite, Nat.add_assoc] using hchar.symm
  exact tendsto_nhds_unique hweakChar hcharRatio


/-- The deterministic limiting mass density of the per-site collision
finite measures. -/
def canonicalCollisionPerSiteMassLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) : NNReal :=
  Real.toNNReal (canonicalCollisionFourierLimit ensemble sign 0).re

theorem canonicalCollisionPerSiteMassLimit_pos
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    0 < canonicalCollisionPerSiteMassLimit ensemble sign := by
  unfold canonicalCollisionPerSiteMassLimit
  rw [Real.toNNReal_pos]
  exact iidCollisionWeightDensityLower_pos.trans_le
    (canonicalCollisionFourierLimit_zero_re_lower ensemble sign)

/-- The masses of the N = n + 3 per-site finite measures converge almost
surely to the deterministic zero-frequency limit. -/
theorem canonicalCollisionPerSiteFiniteMeasure_mass_tendsto_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          (canonicalCollisionPerSiteFiniteMeasure
            ensemble sign (n + 1) omega).mass)
        atTop (nhds (canonicalCollisionPerSiteMassLimit ensemble sign)) := by
  filter_upwards
    [canonicalCollisionFourierPerSite_shift_tendsto_chosenLimit_ae
      ensemble sign 0] with omega hzero
  have hmassComplex : Tendsto
      (fun n : Nat =>
        (((canonicalCollisionPerSiteFiniteMeasure
          ensemble sign (n + 1) omega).mass : Real) : Complex))
      atTop (nhds (canonicalCollisionFourierLimit ensemble sign 0)) := by
    apply hzero.congr'
    exact Eventually.of_forall fun n => by
      change canonicalCollisionFourierPerSite ensemble sign 0 (n + 1) omega =
        (((canonicalCollisionPerSiteFiniteMeasure
          ensemble sign (n + 1) omega).mass : Real) : Complex)
      unfold canonicalCollisionFourierPerSite
      rw [← canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div,
        canonicalCollisionPerSiteFourierIntegral_zero]
  have hmassReal :=
    (Complex.continuous_re.tendsto
      (canonicalCollisionFourierLimit ensemble sign 0)).comp hmassComplex
  have hmassNNReal :=
    (continuous_real_toNNReal.tendsto
      (canonicalCollisionFourierLimit ensemble sign 0).re).comp hmassReal
  unfold canonicalCollisionPerSiteMassLimit
  apply hmassNNReal.congr'
  exact Eventually.of_forall fun n => by
    simp [Function.comp_apply]


/-- Probability normalization is unchanged by the positive per-site scalar
at every simple volume N = n + 3. -/
theorem canonicalCollisionPerSiteFiniteMeasure_normalize_eq
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega))) :
    (canonicalCollisionPerSiteFiniteMeasure
        ensemble sign (n + 1) omega).normalize =
      canonicalCollisionNormalizedMeasure ensemble sign n omega := by
  let original := positiveWeightedMismatchFiniteMeasure
    (ensemble.restrictPositiveMass (N := n + 3) omega) sign
  let source := canonicalCollisionPerSiteFiniteMeasure
    ensemble sign (n + 1) omega
  have horiginalMass : original.mass ≠ 0 := by
    simpa [original] using
      canonicalCollisionFiniteMeasure_mass_ne_zero_of_simple
        ensemble sign n omega hsimple
  have horiginal : original ≠ 0 := original.mass_nonzero_iff.mp horiginalMass
  have hsourceMass : source.mass ≠ 0 := by
    intro hzero
    have hlower := canonicalCollisionPerSite_mass_lower_of_simple
      ensemble sign n omega hsimple
    change iidCollisionWeightDensityLower <= (source.mass : Real) at hlower
    rw [hzero] at hlower
    norm_num at hlower
    exact (not_lt_of_ge hlower) iidCollisionWeightDensityLower_pos
  have hsource : source ≠ 0 := source.mass_nonzero_iff.mp hsourceMass
  change source.normalize = original.normalize
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s hs
  rw [source.normalize_eq_of_nonzero hsource,
    original.normalize_eq_of_nonzero horiginal]
  dsimp only [source, original]
  unfold canonicalCollisionPerSiteFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasure
  have hvolume : (((n + 1 + 2 : Nat) : NNReal)⁻¹) ≠ 0 := by
    positivity
  simp only [FiniteMeasure.mass, FiniteMeasure.smul_apply, smul_eq_mul]
  rw [mul_inv_rev]
  field_simp


/-- The deterministic finite-measure limit: limiting mass density times the
deterministic limiting collision shape. -/
def canonicalCollisionPerSiteMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) : FiniteMeasure Real :=
  canonicalCollisionPerSiteMassLimit ensemble sign •
    (canonicalCollisionMeasureLimit ensemble sign).toFiniteMeasure

@[simp]
theorem canonicalCollisionPerSiteMeasureLimit_mass
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    (canonicalCollisionPerSiteMeasureLimit ensemble sign).mass =
      canonicalCollisionPerSiteMassLimit ensemble sign := by
  unfold canonicalCollisionPerSiteMeasureLimit FiniteMeasure.mass
  rw [FiniteMeasure.smul_apply]
  simp

@[simp]
theorem canonicalCollisionPerSiteMeasureLimit_normalize
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    (canonicalCollisionPerSiteMeasureLimit ensemble sign).normalize =
      canonicalCollisionMeasureLimit ensemble sign := by
  let target := canonicalCollisionPerSiteMeasureLimit ensemble sign
  have hmass : target.mass ≠ 0 := by
    rw [canonicalCollisionPerSiteMeasureLimit_mass]
    exact (canonicalCollisionPerSiteMassLimit_pos ensemble sign).ne'
  have htarget : target ≠ 0 := target.mass_nonzero_iff.mp hmass
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s hs
  rw [target.normalize_eq_of_nonzero htarget]
  dsimp only [target]
  rw [canonicalCollisionPerSiteMeasureLimit_mass]
  unfold canonicalCollisionPerSiteMeasureLimit
  rw [FiniteMeasure.smul_apply]
  simp [(canonicalCollisionPerSiteMassLimit_pos ensemble sign).ne']

/-- The N = n + 3 per-site finite collision measures themselves converge
almost surely to a deterministic finite measure. -/
theorem canonicalCollisionPerSiteFiniteMeasure_tendsto_limit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalCollisionPerSiteFiniteMeasure
            ensemble sign (n + 1) omega)
        atTop
        (nhds (canonicalCollisionPerSiteMeasureLimit ensemble sign)) := by
  filter_upwards
    [canonicalCollisionVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalCollisionNormalizedMeasure_tendsto_limit_ae ensemble sign,
      canonicalCollisionPerSiteFiniteMeasure_mass_tendsto_ae ensemble sign] with
      omega hsimple hnormalize hmass
  apply
    FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  · rw [canonicalCollisionPerSiteMeasureLimit_normalize]
    apply hnormalize.congr'
    exact Eventually.of_forall fun n =>
      (canonicalCollisionPerSiteFiniteMeasure_normalize_eq
        ensemble sign n omega (hsimple n)).symm
  · simpa using hmass

end

end ArchonPhysics.CanonicalCollisionMeasureWeakLimit

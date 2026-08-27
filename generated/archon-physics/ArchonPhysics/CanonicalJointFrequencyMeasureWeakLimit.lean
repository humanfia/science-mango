import ArchonPhysics.CanonicalCollisionMeasureWeakLimit
import ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
import ArchonPhysics.CanonicalJointFrequencyFourierPerSiteLimit
import ArchonPhysics.DenseJointCharacteristicFunctionCompactness

/-!
# Canonical joint-frequency measure weak limit

At the nondegenerate volumes `N = n + 3`, the normalized positive weighted
joint frequency measures converge almost surely to one deterministic
probability measure on `EuclideanSpace Real (Fin 3)`.  The proof combines the
exact deterministic Fourier limits, a countable rational parameter grid, and
the common compact frequency support.

The selected limit is also identified at every real three-frequency
parameter.  Signed mismatch pushforwards are identified with the already
constructed scalar collision-measure limits.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyFourierPerSiteLimit
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.DenseJointCharacteristicFunctionCompactness
open ArchonPhysics.FrozenCollisionMassExtensiveLowerBound
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The zero joint Fourier parameter. -/
def zeroJointFrequencyParameter : Fin 3 -> Real := fun _ => 0

/-- A deterministic choice of the exact joint Fourier transform per-site
limit at a fixed three-frequency parameter. -/
def canonicalJointFrequencyFourierLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) : Complex :=
  Classical.choose
    (exists_canonicalJointFrequencyFourierPerSite_limit_ae
      ensemble parameter)

/-- The selected deterministic joint Fourier value is the almost-sure
limit along all volumes `N = n + 2`. -/
theorem canonicalJointFrequencyFourierPerSite_tendsto_chosenLimit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalJointFrequencyFourierPerSite
            ensemble parameter n omega)
        atTop
        (nhds (canonicalJointFrequencyFourierLimit ensemble parameter)) := by
  exact (Classical.choose_spec
    (exists_canonicalJointFrequencyFourierPerSite_limit_ae
      ensemble parameter)).2

/-- The same deterministic Fourier limit along the nondegenerate sequence
`N = n + 3`. -/
theorem canonicalJointFrequencyFourierPerSite_shift_tendsto_chosenLimit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalJointFrequencyFourierPerSite
            ensemble parameter (n + 1) omega)
        atTop
        (nhds (canonicalJointFrequencyFourierLimit ensemble parameter)) := by
  filter_upwards
    [canonicalJointFrequencyFourierPerSite_tendsto_chosenLimit_ae
      ensemble parameter] with omega hlimit
  exact hlimit.comp (tendsto_add_atTop_nat 1)

/-- A probability-one event carries simple ordered spectrum at every
nondegenerate joint-measure volume `N = n + 3`. -/
theorem canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae
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

/-- At zero parameter the exact joint Fourier transform per site is exactly
the mass of the corresponding per-site joint finite measure. -/
theorem canonicalJointFrequencyFourierPerSite_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    canonicalJointFrequencyFourierPerSite
        ensemble zeroJointFrequencyParameter n omega =
      (((canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass : Real) : Complex) := by
  unfold canonicalJointFrequencyFourierPerSite
  rw [← canonicalJointFrequencyPerSiteFourierIntegral_eq_fourierSum_div]
  unfold canonicalJointFrequencyPerSiteFourierIntegral
  have hcharacter : forall frequency : Fin 3 -> Real,
      frequencyTripleFourierCharacter zeroJointFrequencyParameter frequency = 1 := by
    intro frequency
    unfold frequencyTripleFourierCharacter zeroJointFrequencyParameter
    simp only [zero_mul, Finset.sum_const_zero, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero]
  rw [integral_congr_ae (ae_of_all _ hcharacter), integral_const,
    Complex.real_smul]
  simp only [mul_one]
  congr 1

/-- The per-site joint mass at `N = n + 3` has the fixed positive collision
density lower bound whenever the frozen spectrum is simple. -/
theorem canonicalJointFrequencyPerSite_mass_lower_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega))) :
    iidCollisionWeightDensityLower <=
      ((canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble (n + 1) omega).mass : Real) := by
  simpa [Nat.add_assoc] using
    iidCollisionWeightDensityLower_le_canonicalJointFrequencyPerSite_mass
      ensemble (fun _ => InteractionSign.plus) (n + 1) omega
      (by omega) hsimple

/-- The deterministic zero-parameter joint Fourier limit is bounded away
from zero. -/
theorem canonicalJointFrequencyFourierLimit_zero_re_lower
    (ensemble : IIDMassPhaseEnsemble Omega) :
    iidCollisionWeightDensityLower <=
      (canonicalJointFrequencyFourierLimit
        ensemble zeroJointFrequencyParameter).re := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      (forall n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega))) ∧
      Tendsto
        (fun n : Nat =>
          canonicalJointFrequencyFourierPerSite ensemble
            zeroJointFrequencyParameter (n + 1) omega)
        atTop
        (nhds (canonicalJointFrequencyFourierLimit
          ensemble zeroJointFrequencyParameter)) := by
    filter_upwards
      [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalJointFrequencyFourierPerSite_shift_tendsto_chosenLimit_ae
        ensemble zeroJointFrequencyParameter] with omega hsimple hlimit
    exact ⟨hsimple, hlimit⟩
  obtain ⟨omega, hsimple, hlimit⟩ := hevent.exists
  have hlimitRe : Tendsto
      (fun n : Nat =>
        (canonicalJointFrequencyFourierPerSite ensemble
          zeroJointFrequencyParameter (n + 1) omega).re)
      atTop
      (nhds (canonicalJointFrequencyFourierLimit
        ensemble zeroJointFrequencyParameter).re) :=
    (Complex.continuous_re.tendsto _).comp hlimit
  apply ge_of_tendsto' hlimitRe
  intro n
  rw [canonicalJointFrequencyFourierPerSite_zero]
  exact canonicalJointFrequencyPerSite_mass_lower_of_simple
    ensemble n omega (hsimple n)

/-- Consequently the deterministic zero-parameter denominator is nonzero. -/
theorem canonicalJointFrequencyFourierLimit_zero_ne_zero
    (ensemble : IIDMassPhaseEnsemble Omega) :
    canonicalJointFrequencyFourierLimit
      ensemble zeroJointFrequencyParameter ≠ 0 := by
  intro hzero
  have hlower :=
    canonicalJointFrequencyFourierLimit_zero_re_lower ensemble
  rw [hzero] at hlower
  simp only [Complex.zero_re] at hlower
  exact (not_lt_of_ge hlower) iidCollisionWeightDensityLower_pos

/-- At every nonzero finite-volume joint mass, the characteristic function
of the normalized Euclidean measure is the ratio of the exact per-site joint
Fourier transform to its zero-parameter value. -/
theorem charFun_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_fourier_ratio
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (n : Nat) (omega : Omega)
    (hmass :
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass ≠ 0) :
    charFun
        (canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble n omega : Measure (EuclideanSpace Real (Fin 3)))
        (plainFrequencyTripleToEuclidean parameter) =
      canonicalJointFrequencyFourierPerSite ensemble parameter n omega /
        canonicalJointFrequencyFourierPerSite
          ensemble zeroJointFrequencyParameter n omega := by
  rw [charFun_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_mass_inv_mul
    ensemble parameter n omega hmass]
  rw [canonicalJointFrequencyPerSiteFourierIntegral_eq_fourierSum_div]
  change
    ((((canonicalJointFrequencyPerSiteFiniteMeasure
      ensemble n omega).mass⁻¹ : NNReal) : Real) : Complex) *
        canonicalJointFrequencyFourierPerSite ensemble parameter n omega = _
  rw [canonicalJointFrequencyFourierPerSite_zero]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  rw [← Complex.ofReal_inv]
  congr 1

/-- Deterministic limiting characteristic-function value on the rational
three-frequency grid. -/
def canonicalJointFrequencyNormalizedCharFunLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (q : Fin 3 -> Rat) : Complex :=
  canonicalJointFrequencyFourierLimit ensemble (fun r => (q r : Real)) /
    canonicalJointFrequencyFourierLimit ensemble zeroJointFrequencyParameter

/-- On one probability-one event, all rational-grid characteristic functions
of the genuine normalized joint measures converge to deterministic ratios. -/
theorem canonicalEuclideanNormalizedJointFrequencyMeasure_charFun_rat_tendsto_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability, forall q : Fin 3 -> Rat,
      Tendsto
        (fun n : Nat => charFun
          (canonicalEuclideanNormalizedJointFrequencyMeasure
            ensemble (n + 1) omega :
            Measure (EuclideanSpace Real (Fin 3)))
          (rationalFrequencyTriple q))
        atTop
        (nhds (canonicalJointFrequencyNormalizedCharFunLimit ensemble q)) := by
  have hratFourier : ∀ᵐ omega ∂ensemble.probability, forall q : Fin 3 -> Rat,
      Tendsto
        (fun n : Nat => canonicalJointFrequencyFourierPerSite ensemble
          (fun r => (q r : Real)) (n + 1) omega)
        atTop
        (nhds (canonicalJointFrequencyFourierLimit
          ensemble (fun r => (q r : Real)))) := by
    apply ae_all_iff.mpr
    intro q
    exact canonicalJointFrequencyFourierPerSite_shift_tendsto_chosenLimit_ae
      ensemble (fun r => (q r : Real))
  filter_upwards
    [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble,
    canonicalJointFrequencyFourierPerSite_shift_tendsto_chosenLimit_ae
      ensemble zeroJointFrequencyParameter,
    hratFourier] with omega hsimple hzero hrat
  intro q
  have hratio := (hrat q).div hzero
    (canonicalJointFrequencyFourierLimit_zero_ne_zero ensemble)
  unfold canonicalJointFrequencyNormalizedCharFunLimit
  apply hratio.congr'
  exact Eventually.of_forall fun n => by
    have hmass :
        (canonicalJointFrequencyPerSiteFiniteMeasure
          ensemble (n + 1) omega).mass ≠ 0 :=
      canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
        ensemble (fun _ => InteractionSign.plus) (n + 1) omega
        (by omega) (by simpa [Nat.add_assoc] using hsimple n)
    rw [rationalFrequencyTriple_eq_plainFrequencyTripleToEuclidean]
    exact
      (charFun_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_fourier_ratio
        ensemble (fun r => (q r : Real)) (n + 1) omega hmass).symm

/-- At a realization with simultaneous spectral simplicity, the whole
`N = n + 3` family of normalized Euclidean joint measures is tight. -/
theorem canonicalEuclideanNormalizedJointFrequencyMeasure_range_isTight_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (hsimple : forall n : Nat, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega))) :
    IsTightMeasureSet
      {((nu : ProbabilityMeasure (EuclideanSpace Real (Fin 3))) :
          Measure (EuclideanSpace Real (Fin 3))) |
        nu ∈ Set.range
          (fun n => canonicalEuclideanNormalizedJointFrequencyMeasure
            ensemble (n + 1) omega)} := by
  have hset :
      {((nu : ProbabilityMeasure (EuclideanSpace Real (Fin 3))) :
          Measure (EuclideanSpace Real (Fin 3))) |
        nu ∈ Set.range
          (fun n => canonicalEuclideanNormalizedJointFrequencyMeasure
            ensemble (n + 1) omega)} =
        Set.range (fun n =>
          (canonicalEuclideanNormalizedJointFrequencyMeasure
            ensemble (n + 1) omega :
            Measure (EuclideanSpace Real (Fin 3)))) := by
    ext mu
    simp
  rw [hset]
  simpa [Nat.add_assoc] using
    canonicalEuclideanNormalizedJointFrequencyMeasure_range_isTight
      ensemble (fun n => n + 1) (fun _n => omega)
      (fun _ => InteractionSign.plus)
      (fun _n => by omega)
      (fun n => by simpa [Nat.add_assoc] using hsimple n)

/-- The genuine normalized joint frequency measures at `N = n + 3`
converge almost surely to one deterministic probability measure. -/
theorem exists_canonicalJointFrequencyNormalizedMeasure_weakLimit_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    exists target : ProbabilityMeasure (EuclideanSpace Real (Fin 3)),
      ∀ᵐ omega ∂ensemble.probability,
        Tendsto
          (fun n : Nat =>
            canonicalEuclideanNormalizedJointFrequencyMeasure
              ensemble (n + 1) omega)
          atTop (nhds target) := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      (forall n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega))) ∧
      (forall q : Fin 3 -> Rat, Tendsto
        (fun n : Nat => charFun
          (canonicalEuclideanNormalizedJointFrequencyMeasure
            ensemble (n + 1) omega :
            Measure (EuclideanSpace Real (Fin 3)))
          (rationalFrequencyTriple q))
        atTop
        (nhds (canonicalJointFrequencyNormalizedCharFunLimit ensemble q))) := by
    filter_upwards
      [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalEuclideanNormalizedJointFrequencyMeasure_charFun_rat_tendsto_ae
        ensemble] with omega hsimple hrat
    exact ⟨hsimple, hrat⟩
  obtain ⟨omega0, hsimple0, hrat0⟩ := hevent.exists
  obtain ⟨target, htarget⟩ :=
    exists_tendsto_of_tight_of_charFun_rationalTriple
      (fun n => canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble (n + 1) omega0)
      (canonicalEuclideanNormalizedJointFrequencyMeasure_range_isTight_of_simple
        ensemble omega0 hsimple0)
      (fun q =>
        ⟨canonicalJointFrequencyNormalizedCharFunLimit ensemble q,
          hrat0 q⟩)
  refine ⟨target, ?_⟩
  filter_upwards [hevent] with omega hgood
  rcases hgood with ⟨hsimple, hrat⟩
  obtain ⟨candidate, hcandidate⟩ :=
    exists_tendsto_of_tight_of_charFun_rationalTriple
      (fun n => canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble (n + 1) omega)
      (canonicalEuclideanNormalizedJointFrequencyMeasure_range_isTight_of_simple
        ensemble omega hsimple)
      (fun q =>
        ⟨canonicalJointFrequencyNormalizedCharFunLimit ensemble q,
          hrat q⟩)
  have hcandidateTarget : candidate = target := by
    apply probabilityMeasure_eq_of_charFun_rationalTriple_eq
    intro q
    have hcandidateValue :
        charFun (candidate : Measure (EuclideanSpace Real (Fin 3)))
            (rationalFrequencyTriple q) =
          canonicalJointFrequencyNormalizedCharFunLimit ensemble q :=
      tendsto_nhds_unique
        ((ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hcandidate)
          (rationalFrequencyTriple q))
        (hrat q)
    have htargetValue :
        charFun (target : Measure (EuclideanSpace Real (Fin 3)))
            (rationalFrequencyTriple q) =
          canonicalJointFrequencyNormalizedCharFunLimit ensemble q :=
      tendsto_nhds_unique
        ((ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp htarget)
          (rationalFrequencyTriple q))
        (hrat0 q)
    exact hcandidateValue.trans htargetValue.symm
  simpa [hcandidateTarget] using hcandidate

/-- The deterministic probability-measure limit selected by the weak-limit
existence theorem. -/
def canonicalJointFrequencyMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ProbabilityMeasure (EuclideanSpace Real (Fin 3)) :=
  Classical.choose
    (exists_canonicalJointFrequencyNormalizedMeasure_weakLimit_ae ensemble)

/-- The canonical normalized Euclidean joint measures converge almost surely
to the selected deterministic target. -/
theorem canonicalEuclideanNormalizedJointFrequencyMeasure_tendsto_limit_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalEuclideanNormalizedJointFrequencyMeasure
            ensemble (n + 1) omega)
        atTop (nhds (canonicalJointFrequencyMeasureLimit ensemble)) := by
  exact Classical.choose_spec
    (exists_canonicalJointFrequencyNormalizedMeasure_weakLimit_ae ensemble)

/-- At every real three-frequency parameter, the characteristic function of
the deterministic joint limit is the normalized exact Fourier limit. -/
theorem charFun_canonicalJointFrequencyMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) :
    charFun
        (canonicalJointFrequencyMeasureLimit ensemble :
          Measure (EuclideanSpace Real (Fin 3)))
        (plainFrequencyTripleToEuclidean parameter) =
      canonicalJointFrequencyFourierLimit ensemble parameter /
        canonicalJointFrequencyFourierLimit
          ensemble zeroJointFrequencyParameter := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      (forall n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega))) ∧
      Tendsto
        (fun n : Nat => canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble (n + 1) omega)
        atTop (nhds (canonicalJointFrequencyMeasureLimit ensemble)) ∧
      Tendsto
        (fun n : Nat => canonicalJointFrequencyFourierPerSite
          ensemble parameter (n + 1) omega)
        atTop (nhds (canonicalJointFrequencyFourierLimit
          ensemble parameter)) ∧
      Tendsto
        (fun n : Nat => canonicalJointFrequencyFourierPerSite
          ensemble zeroJointFrequencyParameter (n + 1) omega)
        atTop (nhds (canonicalJointFrequencyFourierLimit
          ensemble zeroJointFrequencyParameter)) := by
    filter_upwards
      [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalEuclideanNormalizedJointFrequencyMeasure_tendsto_limit_ae
        ensemble,
      canonicalJointFrequencyFourierPerSite_shift_tendsto_chosenLimit_ae
        ensemble parameter,
      canonicalJointFrequencyFourierPerSite_shift_tendsto_chosenLimit_ae
        ensemble zeroJointFrequencyParameter] with
        omega hsimple hweak hparameter hzero
    exact ⟨hsimple, hweak, hparameter, hzero⟩
  obtain ⟨omega, hsimple, hweak, hparameter, hzero⟩ := hevent.exists
  have hweakChar :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hweak)
      (plainFrequencyTripleToEuclidean parameter)
  have hratio := hparameter.div hzero
    (canonicalJointFrequencyFourierLimit_zero_ne_zero ensemble)
  have hcharRatio : Tendsto
      (fun n : Nat => charFun
        (canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble (n + 1) omega :
          Measure (EuclideanSpace Real (Fin 3)))
        (plainFrequencyTripleToEuclidean parameter))
      atTop
      (nhds (canonicalJointFrequencyFourierLimit ensemble parameter /
        canonicalJointFrequencyFourierLimit
          ensemble zeroJointFrequencyParameter)) := by
    apply hratio.congr'
    exact Eventually.of_forall fun n => by
      have hmass :
          (canonicalJointFrequencyPerSiteFiniteMeasure
            ensemble (n + 1) omega).mass ≠ 0 :=
        canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
          ensemble (fun _ => InteractionSign.plus) (n + 1) omega
          (by omega) (by simpa [Nat.add_assoc] using hsimple n)
      exact
        (charFun_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_fourier_ratio
          ensemble parameter (n + 1) omega hmass).symm
  exact tendsto_nhds_unique hweakChar hcharRatio

/-- Mapping commutes with nonzero finite-measure normalization. -/
theorem probabilityMeasure_map_finiteMeasure_normalize_eq
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    [Nonempty alpha] [Nonempty beta]
    (mu : FiniteMeasure alpha) (f : alpha -> beta)
    (hf : Measurable f) (hmass : mu.mass ≠ 0) :
    ProbabilityMeasure.map mu.normalize hf.aemeasurable =
      (mu.map f).normalize := by
  have hmu : mu ≠ 0 := mu.mass_nonzero_iff.mp hmass
  have hmapMass : (mu.map f).mass ≠ 0 := by
    rw [finiteMeasure_mass_map_of_measurable mu f hf]
    exact hmass
  have hmap : mu.map f ≠ 0 :=
    (mu.map f).mass_nonzero_iff.mp hmapMass
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero mu hmu]
  rw [Measure.map_smul]
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero (mu.map f) hmap]
  rw [finiteMeasure_mass_map_of_measurable mu f hf]
  rfl

/-- The canonical Euclidean normalized joint measure is equivalently the
normalization of the Euclidean per-site finite measure. -/
theorem canonicalEuclideanNormalizedJointFrequencyMeasure_eq_finite_normalize
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega)
    (hmass :
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass
        ≠ 0) :
    canonicalEuclideanNormalizedJointFrequencyMeasure ensemble n omega =
      (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).normalize := by
  unfold canonicalEuclideanNormalizedJointFrequencyMeasure
    canonicalNormalizedJointFrequencyMeasure
    canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
  exact probabilityMeasure_map_finiteMeasure_normalize_eq
    (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega)
    plainFrequencyTripleToEuclidean
    measurable_plainFrequencyTripleToEuclidean hmass

/-- At every simple volume `N = n + 3`, signed pushforward of the normalized
Euclidean joint measure is exactly the canonical normalized scalar mismatch
measure. -/
theorem map_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_collisionNormalized
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 3) omega))) :
    ProbabilityMeasure.map
        (canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble (n + 1) omega)
        (measurable_euclideanFrequencyTripleMismatch sign).aemeasurable =
      canonicalCollisionNormalizedMeasure ensemble sign n omega := by
  have hmass :
      (canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble (n + 1) omega).mass ≠ 0 :=
    canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
      ensemble sign (n + 1) omega (by omega)
      (by simpa [Nat.add_assoc] using hsimple)
  have hEuclideanMass :
      (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
        ensemble (n + 1) omega).mass ≠ 0 := by
    rw [canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_mass_eq]
    exact hmass
  rw [canonicalEuclideanNormalizedJointFrequencyMeasure_eq_finite_normalize
    ensemble (n + 1) omega hmass]
  rw [probabilityMeasure_map_finiteMeasure_normalize_eq
    (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
      ensemble (n + 1) omega)
    (euclideanFrequencyTripleMismatch sign)
    (measurable_euclideanFrequencyTripleMismatch sign) hEuclideanMass]
  rw [map_canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_eq_collisionPerSite]
  exact canonicalCollisionPerSiteFiniteMeasure_normalize_eq
    ensemble sign n omega hsimple

/-- Every signed continuous mismatch pushforward of the deterministic joint
limit is the previously constructed deterministic scalar collision limit. -/
theorem map_canonicalJointFrequencyMeasureLimit_eq_canonicalCollisionMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    ProbabilityMeasure.map
        (canonicalJointFrequencyMeasureLimit ensemble)
        (measurable_euclideanFrequencyTripleMismatch sign).aemeasurable =
      canonicalCollisionMeasureLimit ensemble sign := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat => canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble (n + 1) omega)
        atTop (nhds (canonicalJointFrequencyMeasureLimit ensemble)) ∧
      Tendsto
        (fun n : Nat => canonicalCollisionNormalizedMeasure
          ensemble sign n omega)
        atTop (nhds (canonicalCollisionMeasureLimit ensemble sign)) ∧
      (forall n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega))) := by
    filter_upwards
      [canonicalEuclideanNormalizedJointFrequencyMeasure_tendsto_limit_ae
        ensemble,
      canonicalCollisionNormalizedMeasure_tendsto_limit_ae ensemble sign,
      canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble] with
        omega hjoint hscalar hsimple
    exact ⟨hjoint, hscalar, hsimple⟩
  obtain ⟨omega, hjoint, hscalar, hsimple⟩ := hevent.exists
  have hmapped :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n : Nat => canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble (n + 1) omega)
      (canonicalJointFrequencyMeasureLimit ensemble) hjoint
      (continuous_euclideanFrequencyTripleMismatch sign)
  have hmappedScalar : Tendsto
      (fun n : Nat => ProbabilityMeasure.map
        (canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble (n + 1) omega)
        (measurable_euclideanFrequencyTripleMismatch sign).aemeasurable)
      atTop (nhds (canonicalCollisionMeasureLimit ensemble sign)) := by
    apply hscalar.congr'
    exact Eventually.of_forall fun n =>
      (map_canonicalEuclideanNormalizedJointFrequencyMeasure_eq_collisionNormalized
        ensemble sign n omega (hsimple n)).symm
  exact tendsto_nhds_unique hmapped hmappedScalar

end

end ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit

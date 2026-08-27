import ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
import ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral

/-!
# Canonical per-site joint frequency-triple measures

At the canonical volume `N = n + 2`, this module bundles the exact positive
joint frequency-triple measure as a `FiniteMeasure`, divides it by the site
count, and normalizes its nonzero instances to probability measures.

The joint Fourier integral is exactly the finite three-frequency sum divided
by `N`.  Every joint frequency lies in the common compact box
`[0, sqrt 5]^3`, and signed pushforward recovers the existing scalar
per-site mismatch measure.  Existing simple-spectrum collision-mass bounds
supply nonzero normalization and a volume-independent mass ceiling.  All
results are finite-volume statements.
-/

open scoped Topology

namespace ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenCollisionMassExtensiveLowerBound
open ArchonPhysics.FrozenCollisionMassPositivity
open ArchonPhysics.FrozenCollisionPerSiteNormalization
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The exact weighted joint frequency-triple measure has finite mass at every
finite volume. -/
theorem positiveWeightedFrequencyTripleMeasure_isFinite
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    IsFiniteMeasure (positiveWeightedFrequencyTripleMeasure m) := by
  constructor
  unfold positiveWeightedFrequencyTripleMeasure
  classical
  simp only [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.sum_lt_top,
    Finset.mem_univ, forall_const]
  intro modes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp [hpositive]
  · simp [hpositive]

/-- The exact positive joint frequency-triple measure, bundled with its
finite-mass proof. -/
def positiveWeightedFrequencyTripleFiniteMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    FiniteMeasure (Fin 3 -> Real) :=
  ⟨positiveWeightedFrequencyTripleMeasure m,
    positiveWeightedFrequencyTripleMeasure_isFinite m⟩

/-- Bundled finite-measure pushforward recovers the scalar mismatch finite
measure. -/
theorem map_positiveWeightedFrequencyTripleFiniteMeasure_eq_mismatchFiniteMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) :
    (positiveWeightedFrequencyTripleFiniteMeasure m).map
        (frequencyTripleMismatch sign) =
      positiveWeightedMismatchFiniteMeasure m sign := by
  apply FiniteMeasure.toMeasure_injective
  exact map_positiveWeightedFrequencyTripleMeasure_eq_mismatchMeasure m sign

/-- A measurable pushforward preserves the total mass of a finite measure. -/
theorem finiteMeasure_mass_map_of_measurable
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (mu : FiniteMeasure alpha) (f : alpha -> beta) (hf : Measurable f) :
    (mu.map f).mass = mu.mass := by
  unfold FiniteMeasure.mass
  rw [FiniteMeasure.map_apply mu hf MeasurableSet.univ]
  simp

/-- Hence the joint measure has exactly the same mass as every signed scalar
mismatch pushforward. -/
theorem positiveWeightedFrequencyTripleFiniteMeasure_mass_eq_mismatchFiniteMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) :
    (positiveWeightedFrequencyTripleFiniteMeasure m).mass =
      (positiveWeightedMismatchFiniteMeasure m sign).mass := by
  calc
    (positiveWeightedFrequencyTripleFiniteMeasure m).mass =
        ((positiveWeightedFrequencyTripleFiniteMeasure m).map
          (frequencyTripleMismatch sign)).mass :=
      (finiteMeasure_mass_map_of_measurable
        (positiveWeightedFrequencyTripleFiniteMeasure m)
        (frequencyTripleMismatch sign)
        (measurable_frequencyTripleMismatch sign)).symm
    _ = (positiveWeightedMismatchFiniteMeasure m sign).mass :=
      congrArg FiniteMeasure.mass
        (map_positiveWeightedFrequencyTripleFiniteMeasure_eq_mismatchFiniteMeasure
          m sign)

/-- The joint collision finite measure divided by the site count at canonical
volume `N = n + 2`. -/
def canonicalJointFrequencyPerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) : FiniteMeasure (Fin 3 -> Real) :=
  (((n + 2 : Nat) : NNReal)⁻¹) •
    positiveWeightedFrequencyTripleFiniteMeasure
      (ensemble.restrictPositiveMass (N := n + 2) omega)

/-- The probability normalization of the per-site joint measure.  Subsequent
formulas explicitly discharge its nonzero-mass premise. -/
def canonicalNormalizedJointFrequencyMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) : ProbabilityMeasure (Fin 3 -> Real) :=
  (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).normalize

/-- Joint Fourier integral of the canonical per-site measure. -/
def canonicalJointFrequencyPerSiteFourierIntegral
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (n : Nat) (omega : Omega) : Complex :=
  ∫ frequency : Fin 3 -> Real,
      frequencyTripleFourierCharacter parameter frequency
    ∂(canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega :
      Measure (Fin 3 -> Real))

/-- The per-site joint Fourier integral is exactly the genuine finite joint
Fourier sum divided by the number of sites. -/
theorem canonicalJointFrequencyPerSiteFourierIntegral_eq_fourierSum_div
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (n : Nat) (omega : Omega) :
    canonicalJointFrequencyPerSiteFourierIntegral
        ensemble parameter n omega =
      positiveWeightedFrequencyTripleFourierSum
          (ensemble.restrictPositiveMass (N := n + 2) omega) parameter /
        (((n + 2 : Nat) : Real) : Complex) := by
  unfold canonicalJointFrequencyPerSiteFourierIntegral
    canonicalJointFrequencyPerSiteFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  change ((((n + 2 : Nat) : NNReal)⁻¹) •
      (∫ frequency : Fin 3 -> Real,
        frequencyTripleFourierCharacter parameter frequency
        ∂positiveWeightedFrequencyTripleMeasure
          (ensemble.restrictPositiveMass (N := n + 2) omega))) = _
  rw [integral_positiveWeightedFrequencyTripleMeasure_eq_fourierSum]
  simp only [NNReal.smul_def, NNReal.coe_inv]
  rw [Complex.real_smul, div_eq_mul_inv, mul_comm]
  rw [Complex.ofReal_inv]
  congr 1

/-- Signed pushforward of the canonical joint finite measure is exactly the
existing canonical per-site scalar mismatch finite measure. -/
theorem map_canonicalJointFrequencyPerSiteFiniteMeasure_eq_collisionPerSite
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega) :
    (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).map
        (frequencyTripleMismatch sign) =
      canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega := by
  unfold canonicalJointFrequencyPerSiteFiniteMeasure
    canonicalCollisionPerSiteFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasure
  rw [FiniteMeasure.map_smul,
    map_positiveWeightedFrequencyTripleFiniteMeasure_eq_mismatchFiniteMeasure]

/-- Measure-level form of the exact per-site signed pushforward identity. -/
theorem map_canonicalJointFrequencyPerSiteMeasure_eq_collisionPerSiteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega) :
    (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega :
        Measure (Fin 3 -> Real)).map (frequencyTripleMismatch sign) =
      (canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega :
        Measure Real) := by
  exact congrArg FiniteMeasure.toMeasure
    (map_canonicalJointFrequencyPerSiteFiniteMeasure_eq_collisionPerSite
      ensemble sign n omega)

/-- The common compact frequency box `[0, sqrt 5]^3`. -/
def collisionFrequencyTripleSupport : Set (Fin 3 -> Real) :=
  Set.Icc (fun _ => 0) (fun _ => collisionFrequencyCeiling)

theorem collisionFrequencyTripleSupport_isCompact :
    IsCompact collisionFrequencyTripleSupport := by
  exact isCompact_Icc

/-- Every ordered frequency triple of every frozen iid realization lies in
the common compact box. -/
theorem iid_orderedFrequencyTriple_mem_uniformSupport
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (modes : OrderedModeTriple N) :
    orderedFrequencyTriple
        (ensemble.restrictPositiveMass (N := N) omega) modes ∈
      collisionFrequencyTripleSupport := by
  change
    (∀ r, 0 <= orderedModeFrequency
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)) (modes r)) ∧
    (∀ r, orderedModeFrequency
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)) (modes r) <=
      collisionFrequencyCeiling)
  constructor
  · intro r
    exact (iid_orderedModeFrequency_mem_uniformBand
      ensemble omega (modes r)).1
  · intro r
    exact (iid_orderedModeFrequency_mem_uniformBand
      ensemble omega (modes r)).2

/-- The exact joint measure has no mass outside the common compact frequency
box. -/
theorem iid_positiveWeightedFrequencyTripleMeasure_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    positiveWeightedFrequencyTripleMeasure
        (ensemble.restrictPositiveMass (N := N) omega)
        (collisionFrequencyTripleSupportᶜ) = 0 := by
  classical
  unfold positiveWeightedFrequencyTripleMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple
      (ensemble.restrictPositiveMass (N := N) omega) modes
  · rw [if_pos hpositive, Measure.smul_apply]
    simp [iid_orderedFrequencyTriple_mem_uniformSupport
      ensemble omega modes]
  · rw [if_neg hpositive]
    rfl

/-- Site normalization preserves the common compact frequency box. -/
theorem canonicalJointFrequencyPerSiteFiniteMeasure_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega :
        Measure (Fin 3 -> Real)) (collisionFrequencyTripleSupportᶜ) = 0 := by
  unfold canonicalJointFrequencyPerSiteFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  change _ * positiveWeightedFrequencyTripleMeasure
      (ensemble.restrictPositiveMass (N := n + 2) omega)
      (collisionFrequencyTripleSupportᶜ) = 0
  rw [iid_positiveWeightedFrequencyTripleMeasure_compl_uniformSupport_eq_zero
    ensemble omega]
  simp

/-- The per-site joint mass equals the mass of every signed scalar per-site
pushforward. -/
theorem canonicalJointFrequencyPerSiteFiniteMeasure_mass_eq_collisionPerSite
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega) :
    (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass =
      (canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega).mass := by
  calc
    (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass =
        ((canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).map
          (frequencyTripleMismatch sign)).mass :=
      (finiteMeasure_mass_map_of_measurable
        (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega)
        (frequencyTripleMismatch sign)
        (measurable_frequencyTripleMismatch sign)).symm
    _ = (canonicalCollisionPerSiteFiniteMeasure
          ensemble sign n omega).mass :=
      congrArg FiniteMeasure.mass
        (map_canonicalJointFrequencyPerSiteFiniteMeasure_eq_collisionPerSite
          ensemble sign n omega)

/-- Existing extensive collision-mass control gives the same positive
per-site lower bound to the joint measure. -/
theorem iidCollisionWeightDensityLower_le_canonicalJointFrequencyPerSite_mass
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hN : 3 <= n + 2)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    iidCollisionWeightDensityLower <=
      ((canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass : Real) := by
  rw [canonicalJointFrequencyPerSiteFiniteMeasure_mass_eq_collisionPerSite
    ensemble sign n omega]
  exact iidCollisionWeightDensityLower_le_perSite_mass
    ensemble omega hN hsimple sign

/-- Under simple spectrum and `N >= 3`, the per-site joint measure has
nonzero mass, so probability normalization is genuine. -/
theorem canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hN : 3 <= n + 2)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass ≠ 0 := by
  have hlower :=
    iidCollisionWeightDensityLower_le_canonicalJointFrequencyPerSite_mass
      ensemble sign n omega hN hsimple
  have hpos :
      0 < ((canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass : Real) :=
    iidCollisionWeightDensityLower_pos.trans_le hlower
  exact_mod_cast (ne_of_gt hpos)

/-- The joint per-site mass inherits the existing volume-independent upper
ceiling. -/
theorem canonicalJointFrequencyPerSiteFiniteMeasure_mass_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    ((canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass : Real) <=
      canonicalCollisionPerSiteMassCeiling := by
  rw [canonicalJointFrequencyPerSiteFiniteMeasure_mass_eq_collisionPerSite
    ensemble sign n omega]
  exact canonicalCollisionPerSiteFiniteMeasure_mass_le
    ensemble sign n omega hsimple

/-- Compact lower/upper mass interface for subsequent normalized-family
arguments. -/
theorem canonicalJointFrequencyPerSiteFiniteMeasure_mass_bounds
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hN : 3 <= n + 2)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    iidCollisionWeightDensityLower <=
        ((canonicalJointFrequencyPerSiteFiniteMeasure
          ensemble n omega).mass : Real) ∧
      ((canonicalJointFrequencyPerSiteFiniteMeasure
          ensemble n omega).mass : Real) <=
        canonicalCollisionPerSiteMassCeiling :=
  ⟨iidCollisionWeightDensityLower_le_canonicalJointFrequencyPerSite_mass
      ensemble sign n omega hN hsimple,
    canonicalJointFrequencyPerSiteFiniteMeasure_mass_le
      ensemble sign n omega hsimple⟩

/-- Fourier integral of the genuinely normalized joint measure is inverse
mass times the per-site joint Fourier integral. -/
theorem integral_canonicalNormalizedJointFrequencyMeasure_eq_mass_inv_mul
    (ensemble : IIDMassPhaseEnsemble Omega)
    (parameter : Fin 3 -> Real) (n : Nat) (omega : Omega)
    (hmass :
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass ≠ 0) :
    (∫ frequency : Fin 3 -> Real,
        frequencyTripleFourierCharacter parameter frequency
      ∂(canonicalNormalizedJointFrequencyMeasure ensemble n omega :
        Measure (Fin 3 -> Real))) =
      (((canonicalJointFrequencyPerSiteFiniteMeasure
        ensemble n omega).mass⁻¹ : NNReal) : Real) *
        canonicalJointFrequencyPerSiteFourierIntegral
          ensemble parameter n omega := by
  have hmeasure :
      canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega ≠ 0 :=
    (canonicalJointFrequencyPerSiteFiniteMeasure
      ensemble n omega).mass_nonzero_iff.mp hmass
  unfold canonicalNormalizedJointFrequencyMeasure
    canonicalJointFrequencyPerSiteFourierIntegral
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hmeasure,
    integral_smul_nnreal_measure]
  rfl

/-- Nonzero probability normalization preserves the same compact frequency
box. -/
theorem canonicalNormalizedJointFrequencyMeasure_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega)
    (hmass :
      (canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega).mass ≠ 0) :
    (canonicalNormalizedJointFrequencyMeasure ensemble n omega :
        Measure (Fin 3 -> Real)) (collisionFrequencyTripleSupportᶜ) = 0 := by
  have hmeasure :
      canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega ≠ 0 :=
    (canonicalJointFrequencyPerSiteFiniteMeasure
      ensemble n omega).mass_nonzero_iff.mp hmass
  unfold canonicalNormalizedJointFrequencyMeasure
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hmeasure,
    Measure.smul_apply]
  simp [canonicalJointFrequencyPerSiteFiniteMeasure_compl_uniformSupport_eq_zero
    ensemble n omega]

/-- Any varying canonical-volume family satisfying `N >= 3` and simple
spectrum is tight after probability normalization, witnessed by the single
compact box `[0, sqrt 5]^3`. -/
theorem canonicalNormalizedJointFrequencyMeasure_range_isTight
    (ensemble : IIDMassPhaseEnsemble Omega)
    (size : Nat -> Nat) (omega : Nat -> Omega)
    (sign : Fin 3 -> InteractionSign)
    (hN : ∀ j, 3 <= size j + 2)
    (hsimple : ∀ j, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := size j + 2) (omega j)))) :
    IsTightMeasureSet (Set.range fun j =>
      (canonicalNormalizedJointFrequencyMeasure
        ensemble (size j) (omega j) : Measure (Fin 3 -> Real))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  refine ⟨collisionFrequencyTripleSupport,
    collisionFrequencyTripleSupport_isCompact, ?_⟩
  intro mu hmu
  rcases hmu with ⟨j, rfl⟩
  rw [canonicalNormalizedJointFrequencyMeasure_compl_uniformSupport_eq_zero
    ensemble (size j) (omega j)
      (canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
        ensemble sign (size j) (omega j) (hN j) (hsimple j))]
  exact hepsilon.le

end

end ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure

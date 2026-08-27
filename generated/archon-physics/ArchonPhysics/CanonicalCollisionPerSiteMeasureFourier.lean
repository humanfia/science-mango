import ArchonPhysics.FrozenCollisionPerSiteNormalization
import ArchonPhysics.FrozenCollisionMassPositivityGeneralN
import ArchonPhysics.FrozenUniformCollisionCompactSupport
import ArchonPhysics.HarmonicComplexThreeLegKernelApproximation
import ArchonPhysics.NormalizedPhaseEffectiveWeightBound
import ArchonPhysics.ResonanceKernelLipschitz

/-!
# Canonical per-site collision measures and their Fourier transforms

At volume `N = n + 2`, the genuine positive collision measure is normalized
by the number of sites.  Its Fourier integral is exactly the existing
positive mismatch Fourier sum divided by `N`.

For frozen iid masses, every mismatch lies in the fixed interval
`[-3 * sqrt 5, 3 * sqrt 5]`.  On simple spectrum, the harmonic edge-frame
bound also gives the genuinely per-site mass ceiling `(sqrt 5 / 2)^3`.
Together these facts yield volume-uniform Fourier magnitude and Lipschitz
bounds.  No thermodynamic convergence is asserted here.
-/

namespace ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier

open ArchonPhysics
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenCollisionPerSiteNormalization
open ArchonPhysics.FrozenCollisionMassPositivity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.FrozenUniformCollisionFiniteMeasureBound
open ArchonPhysics.FrozenUniformCollisionMassBound
open ArchonPhysics.HarmonicComplexThreeLegKernelApproximation
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedPhaseEffectiveWeightBound
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveWeightedMismatchFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The positive collision finite measure divided by the site count at the
canonical volume `N = n + 2`. -/
def canonicalCollisionPerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega) : FiniteMeasure Real :=
  perSitePositiveWeightedMismatchFiniteMeasure
    (ensemble.restrictPositiveMass (N := n + 2) omega) sign

/-- Fourier integral of the canonical per-site collision finite measure. -/
def canonicalCollisionPerSiteFourierIntegral
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (time : Real) (n : Nat) (omega : Omega) : Complex :=
  ∫ x : Real, Complex.exp
      (Complex.I * ((time * x : Real) : Complex))
    ∂(canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega :
      Measure Real)

/-- The measure Fourier integral is exactly the positive mismatch Fourier
sum divided by the number of sites. -/
theorem canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (time : Real) (n : Nat) (omega : Omega) :
    canonicalCollisionPerSiteFourierIntegral ensemble sign time n omega =
      positiveWeightedMismatchFourierSum
          (ensemble.restrictPositiveMass (N := n + 2) omega) sign time /
        (((n + 2 : Nat) : Real) : Complex) := by
  unfold canonicalCollisionPerSiteFourierIntegral
    canonicalCollisionPerSiteFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  unfold positiveWeightedMismatchFiniteMeasure
  change (((n + 2 : Nat) : NNReal)⁻¹) •
      (∫ x : Real, Complex.exp
        (Complex.I * ((time * x : Real) : Complex))
        ∂positiveWeightedMismatchMeasure
          (ensemble.restrictPositiveMass (N := n + 2) omega) sign) = _
  rw [integral_positiveWeightedMismatchMeasure_eq_fourierSum]
  simp only [NNReal.smul_def, NNReal.coe_inv]
  rw [Complex.real_smul, div_eq_mul_inv, mul_comm]
  rw [Complex.ofReal_inv]
  congr 1

/-- Site normalization preserves the common frozen mismatch support. -/
theorem canonicalCollisionPerSiteFiniteMeasure_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega) :
    (canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega :
        Measure Real) (collisionMismatchSupportᶜ) = 0 := by
  unfold canonicalCollisionPerSiteFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  simp [iid_positiveWeightedMismatchFiniteMeasure_compl_uniformSupport_eq_zero
    ensemble omega sign]

/-- Fourier characters are integrable against every finite measure. -/
theorem integrable_fourierCharacter_finiteMeasure
    (mu : FiniteMeasure Real) (time : Real) :
    Integrable
      (fun x : Real => Complex.exp
        (Complex.I * ((time * x : Real) : Complex)))
      (mu : Measure Real) := by
  apply Integrable.of_bound (C := 1)
  · fun_prop
  · exact ae_of_all _ fun x => by
      rw [Complex.norm_exp]
      simp [Complex.mul_re]

/-- The norm of a finite-measure Fourier transform is at most its mass. -/
theorem norm_canonicalCollisionPerSiteFourierIntegral_le_mass
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (time : Real) (n : Nat) (omega : Omega) :
    ‖canonicalCollisionPerSiteFourierIntegral
        ensemble sign time n omega‖ <=
      ((canonicalCollisionPerSiteFiniteMeasure
        ensemble sign n omega).mass : Real) := by
  let mu := canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega
  have hbound := norm_integral_le_of_norm_le_const
    (μ := (mu : Measure Real))
    (f := fun x : Real => Complex.exp
      (Complex.I * ((time * x : Real) : Complex))) (C := 1)
    (ae_of_all (mu : Measure Real) fun x => by
      rw [Complex.norm_exp]
      simp [Complex.mul_re])
  have hmass :
      ((mu : Measure Real) Set.univ).toReal = (mu.mass : Real) := by
    calc
      ((mu : Measure Real) Set.univ).toReal =
          (((mu.mass : NNReal) : ENNReal)).toReal :=
        congrArg ENNReal.toReal FiniteMeasure.ennreal_mass.symm
      _ = (mu.mass : Real) := ENNReal.coe_toReal mu.mass
  change ‖∫ x : Real, Complex.exp
      (Complex.I * ((time * x : Real) : Complex)) ∂(mu : Measure Real)‖ <=
    (mu.mass : Real)
  change ‖∫ x : Real, Complex.exp
      (Complex.I * ((time * x : Real) : Complex)) ∂(mu : Measure Real)‖ <=
    1 * ((mu : Measure Real) Set.univ).toReal at hbound
  rw [hmass, one_mul] at hbound
  exact hbound

/-- Compact support controls the Fourier modulus of continuity by radius
times total mass. -/
theorem norm_canonicalCollisionPerSiteFourierIntegral_sub_le_mass
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (time time' : Real) (n : Nat) (omega : Omega) :
    ‖canonicalCollisionPerSiteFourierIntegral ensemble sign time n omega -
        canonicalCollisionPerSiteFourierIntegral
          ensemble sign time' n omega‖ <=
      |time - time'| * (3 * collisionFrequencyCeiling) *
        ((canonicalCollisionPerSiteFiniteMeasure
          ensemble sign n omega).mass : Real) := by
  let mu := canonicalCollisionPerSiteFiniteMeasure ensemble sign n omega
  have htime := integrable_fourierCharacter_finiteMeasure mu time
  have htime' := integrable_fourierCharacter_finiteMeasure mu time'
  have hsupport : ∀ᵐ x ∂(mu : Measure Real), x ∈ collisionMismatchSupport :=
    (mem_ae_iff).2 (by
      simpa [mu] using
        canonicalCollisionPerSiteFiniteMeasure_compl_uniformSupport_eq_zero
          ensemble sign n omega)
  have hpointwise : ∀ᵐ x ∂(mu : Measure Real),
      ‖Complex.exp (Complex.I * ((time * x : Real) : Complex)) -
          Complex.exp (Complex.I * ((time' * x : Real) : Complex))‖ <=
        |time - time'| * (3 * collisionFrequencyCeiling) := by
    filter_upwards [hsupport] with x hx
    have hxabs : |x| <= 3 * collisionFrequencyCeiling :=
      abs_le.mpr hx
    have hphase := norm_exp_phase_sub_le time time' x
    calc
      ‖Complex.exp (Complex.I * ((time * x : Real) : Complex)) -
          Complex.exp (Complex.I * ((time' * x : Real) : Complex))‖ <=
          |time - time'| * |x| := by
        simpa only [← Complex.ofReal_mul, mul_assoc] using hphase
      _ <= |time - time'| * (3 * collisionFrequencyCeiling) :=
        mul_le_mul_of_nonneg_left hxabs (abs_nonneg _)
  have hbound := norm_integral_le_of_norm_le_const
    (μ := (mu : Measure Real))
    (f := fun x : Real =>
      Complex.exp (Complex.I * ((time * x : Real) : Complex)) -
        Complex.exp (Complex.I * ((time' * x : Real) : Complex)))
    hpointwise
  have hmass :
      ((mu : Measure Real) Set.univ).toReal = (mu.mass : Real) := by
    calc
      ((mu : Measure Real) Set.univ).toReal =
          (((mu.mass : NNReal) : ENNReal)).toReal :=
        congrArg ENNReal.toReal FiniteMeasure.ennreal_mass.symm
      _ = (mu.mass : Real) := ENNReal.coe_toReal mu.mass
  change ‖(∫ x : Real, Complex.exp
        (Complex.I * ((time * x : Real) : Complex)) ∂(mu : Measure Real)) -
      (∫ x : Real, Complex.exp
        (Complex.I * ((time' * x : Real) : Complex)) ∂(mu : Measure Real))‖ <=
    |time - time'| * (3 * collisionFrequencyCeiling) * (mu.mass : Real)
  rw [← integral_sub htime htime']
  change ‖∫ x : Real,
      Complex.exp (Complex.I * ((time * x : Real) : Complex)) -
        Complex.exp (Complex.I * ((time' * x : Real) : Complex))
      ∂(mu : Measure Real)‖ <=
    |time - time'| * (3 * collisionFrequencyCeiling) *
      ((mu : Measure Real) Set.univ).toReal at hbound
  rw [hmass] at hbound
  exact hbound

/-- The zero-time Fourier sum is the real positive total interaction
weight, embedded into the complex numbers. -/
theorem positiveWeightedMismatchFourierSum_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) :
    positiveWeightedMismatchFourierSum m sign 0 =
      (positiveOrderedTotalInteractionWeight m : Complex) := by
  classical
  unfold positiveWeightedMismatchFourierSum
    positiveOrderedTotalInteractionWeight
  push_cast
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp [hpositive]
  · simp [hpositive]

/-- At zero time, the per-site Fourier integral is exactly the real mass of
the per-site finite measure, embedded into the complex numbers. -/
theorem canonicalCollisionPerSiteFourierIntegral_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega) :
    canonicalCollisionPerSiteFourierIntegral ensemble sign 0 n omega =
      (((canonicalCollisionPerSiteFiniteMeasure
        ensemble sign n omega).mass : Real) : Complex) := by
  rw [canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div,
    positiveWeightedMismatchFourierSum_zero]
  unfold canonicalCollisionPerSiteFiniteMeasure
  rw [perSitePositiveWeightedMismatchFiniteMeasure_mass_real]
  push_cast
  rw [div_eq_mul_inv]
  ring

/-- For `N = n + 2 >= 3` and simple spectrum, probability normalization is
the ratio of the per-site Fourier integral to its nonzero zero-time value. -/
theorem charFun_normalizedPositiveWeightedMismatchMeasure_eq_perSiteFourier_ratio
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (time : Real) (n : Nat) (omega : Omega)
    (hN : 3 <= n + 2)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    charFun
        (normalizedPositiveWeightedMismatchMeasure
          (ensemble.restrictPositiveMass (N := n + 2) omega) sign :
            Measure Real) time =
      canonicalCollisionPerSiteFourierIntegral
          ensemble sign time n omega /
        canonicalCollisionPerSiteFourierIntegral
          ensemble sign 0 n omega := by
  let m := ensemble.restrictPositiveMass (N := n + 2) omega
  have hmass : (positiveWeightedMismatchFiniteMeasure m sign).mass ≠ 0 :=
    positiveWeightedMismatchFiniteMeasure_mass_ne_zero_of_three_le
        m hsimple sign hN
  have htotalNonneg : 0 <= positiveOrderedTotalInteractionWeight m :=
    positiveOrderedTotalInteractionWeight_nonneg m
  have htotalPos : 0 < positiveOrderedTotalInteractionWeight m :=
    positiveOrderedTotalInteractionWeight_pos_of_three_le m hsimple hN
  have hmassReal :
      ((positiveWeightedMismatchFiniteMeasure m sign).mass : Real) =
        positiveOrderedTotalInteractionWeight m := by
    rw [positiveWeightedMismatchFiniteMeasure_mass_eq_toNNReal,
      Real.coe_toNNReal _ htotalNonneg]
  have hvolume : (((n + 2 : Nat) : Real)) ≠ 0 := by positivity
  have hvolumeComplex :
      (((((n + 2 : Nat) : Real)) : Complex)) ≠ 0 := by
    exact_mod_cast hvolume
  have hvolumeComplex' : (n : Complex) + 2 ≠ 0 := by
    exact_mod_cast (show n + 2 ≠ 0 by omega)
  have htotalComplex :
      (positiveOrderedTotalInteractionWeight m : Complex) ≠ 0 := by
    exact_mod_cast (ne_of_gt htotalPos)
  rw [charFun_normalizedPositiveWeightedMismatchMeasure_eq_fourierSum
      m sign time hmass,
    canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div,
    canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div,
    positiveWeightedMismatchFourierSum_zero]
  rw [hmassReal]
  push_cast
  field_simp [hvolumeComplex, hvolumeComplex', htotalComplex, m]; ring

/-- The natural volume-uniform ceiling for a per-site three-leg collision
mass on the frozen spectral band. -/
def canonicalCollisionPerSiteMassCeiling : Real :=
  (Real.sqrt 5 / 2) ^ 3

theorem canonicalCollisionPerSiteMassCeiling_nonneg :
    0 <= canonicalCollisionPerSiteMassCeiling := by
  unfold canonicalCollisionPerSiteMassCeiling
  positivity

/-- The harmonic edge frame gives a volume-uniform bound on the exact
positive collision Fourier sum per site. -/
theorem norm_iid_positiveWeightedMismatchFourierSum_div_volume_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)))
    (sign : Fin 3 -> InteractionSign) (time : Real) :
    ‖positiveWeightedMismatchFourierSum
        (ensemble.restrictPositiveMass (N := N) omega) sign time /
      (((N : Nat) : Real) : Complex)‖ <=
        canonicalCollisionPerSiteMassCeiling := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  let bound : Real := Real.sqrt 5 / 2
  have hbound : 0 <= bound := by
    dsimp [bound]
    positivity
  have heffective : forall r k,
      ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) *
          orderedNormalizedPhaseLeg m sign time r k‖ <= bound := by
    intro r k
    exact norm_eigenvalue_mul_orderedNormalizedPhaseLeg_le_sqrtFive_div_two
      m (fun q => iid_orderedEigenvalue_harmonic_le_five ensemble omega q)
      sign time r k
  have hkernel :=
    harmonic_threeLeg_complexProjectedKernel_replacementPerSite_norm_le
      m hsimple
      (fun r => orderedNormalizedPhaseLeg m sign time r)
      (fun _r _k => 0)
      (fun _r => bound) (fun _r => bound) (fun _r => 0)
      (fun _r => hbound) (fun _r => hbound) (fun _r => le_rfl)
      (fun r k => by simpa using heffective r k)
      heffective
      (fun _r _k => by simp)
  rw [positiveWeightedMismatchFourierSum_factorization]
  simpa [complexWeightedProjectedBondKernel, Fin.prod_univ_three,
    canonicalCollisionPerSiteMassCeiling, bound, pow_succ] using hkernel

/-- On simple spectrum, the canonical per-site collision measure has the
same realization- and volume-independent mass ceiling. -/
theorem canonicalCollisionPerSiteFiniteMeasure_mass_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    ((canonicalCollisionPerSiteFiniteMeasure
        ensemble sign n omega).mass : Real) <=
      canonicalCollisionPerSiteMassCeiling := by
  let m := ensemble.restrictPositiveMass (N := n + 2) omega
  have hNpos : 0 < (((n + 2 : Nat) : Real)) := by positivity
  have htotal : 0 <= positiveOrderedTotalInteractionWeight m :=
    positiveOrderedTotalInteractionWeight_nonneg m
  have hfourier :=
    norm_iid_positiveWeightedMismatchFourierSum_div_volume_le
      ensemble omega hsimple sign 0
  unfold canonicalCollisionPerSiteFiniteMeasure
  rw [perSitePositiveWeightedMismatchFiniteMeasure_mass_real]
  calc
    (((n + 2 : Nat) : Real))⁻¹ *
        positiveOrderedTotalInteractionWeight m =
      ‖positiveWeightedMismatchFourierSum m sign 0 /
        ((((n + 2 : Nat) : Real)) : Complex)‖ := by
      rw [positiveWeightedMismatchFourierSum_zero, norm_div,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg htotal, abs_of_pos hNpos,
        div_eq_inv_mul]
    _ <= canonicalCollisionPerSiteMassCeiling := by
      simpa [m] using hfourier

/-- Uniform Fourier magnitude bound at every canonical volume. -/
theorem norm_canonicalCollisionPerSiteFourierIntegral_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (time : Real) (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    ‖canonicalCollisionPerSiteFourierIntegral
        ensemble sign time n omega‖ <=
      canonicalCollisionPerSiteMassCeiling :=
  (norm_canonicalCollisionPerSiteFourierIntegral_le_mass
    ensemble sign time n omega).trans
      (canonicalCollisionPerSiteFiniteMeasure_mass_le
        ensemble sign n omega hsimple)

/-- Uniform support-derived Lipschitz bound for the canonical Fourier
transforms. -/
theorem norm_canonicalCollisionPerSiteFourierIntegral_sub_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (time time' : Real) (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    ‖canonicalCollisionPerSiteFourierIntegral ensemble sign time n omega -
        canonicalCollisionPerSiteFourierIntegral
          ensemble sign time' n omega‖ <=
      |time - time'| * (3 * collisionFrequencyCeiling) *
        canonicalCollisionPerSiteMassCeiling := by
  exact (norm_canonicalCollisionPerSiteFourierIntegral_sub_le_mass
    ensemble sign time time' n omega).trans
      (mul_le_mul_of_nonneg_left
        (canonicalCollisionPerSiteFiniteMeasure_mass_le
          ensemble sign n omega hsimple)
        (mul_nonneg (abs_nonneg _)
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))))

end

end ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier

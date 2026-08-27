import ArchonPhysics.RandomMassOrderedProjectorBridge
import ArchonPhysics.TruncatedGaussianMassPhaseEnsemble

/-!
# Almost-sure simple spectrum for truncated-Gaussian random masses

This module supplies the Gaussian analogue of the existing uniform-iid
simple-spectrum bridge.  A finite restriction of a verified
`GaussianIIDMassPhaseEnsemble` has the exact finite product of conditioned
Gaussian coordinate laws.  That finite law is absolutely continuous with
respect to Lebesgue volume, so every nonzero polynomial in the inverse mass
coordinates vanishes with probability zero.

Applying the existing nonzero resultant certificate rules out repeated
positive harmonic eigenvalues.  The deterministic one-dimensional
translation kernel then upgrades positive simplicity to simplicity of the
full ordered harmonic spectrum.

No statement about a kinetic limit or thermalization is made here.
-/

namespace ArchonPhysics.GaussianRandomMassSimpleSpectrum

open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PathLaplacianResultant
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.RandomMassSimpleSpectrum
open ArchonPhysics.TruncatedGaussianMassLaw
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-! ## Absolute continuity of the finite Gaussian product law -/

/-- A conditioned nondegenerate Gaussian on the physical mass interval is
absolutely continuous with respect to Lebesgue measure on the whole line. -/
theorem coordinateLaw_absolutelyContinuous_volume
    (parameters : Parameters) :
    coordinateLaw parameters ≪ (volume : Measure Real) :=
  (TruncatedGaussianMassLaw.coordinateLaw_absolutelyContinuous_volume_restrict
    parameters).trans Measure.restrict_le_self.absolutelyContinuous

/-- Every finite product of conditioned Gaussian mass coordinates is
absolutely continuous with respect to finite-dimensional Lebesgue volume. -/
theorem finiteLaw_absolutelyContinuous_volume (parameters : Parameters) :
    ∀ N : Nat,
      finiteLaw parameters N ≪ (volume : Measure (Fin N → Real))
  | 0 => by
      rw [finiteLaw, Measure.pi_of_empty, Measure.volume_pi_eq_dirac]
  | n + 1 => by
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ Real) 0
      have hMass : MeasurePreserving e (finiteLaw parameters (n + 1))
          ((coordinateLaw parameters).prod (finiteLaw parameters n)) := by
        dsimp [e]
        simpa [finiteLaw] using
          measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) ↦ coordinateLaw parameters) 0
      have hVolume : MeasurePreserving e
          (volume : Measure (Fin (n + 1) → Real))
          (volume : Measure (Real × (Fin n → Real))) := by
        exact volume_preserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ Real) 0
      have hProduct :
          (coordinateLaw parameters).prod (finiteLaw parameters n) ≪
            (volume : Measure (Real × (Fin n → Real))) := by
        rw [Measure.volume_eq_prod]
        exact (coordinateLaw_absolutelyContinuous_volume parameters).prod
          (finiteLaw_absolutelyContinuous_volume parameters n)
      have hMapped := e.symm.measurableEmbedding.absolutelyContinuous_map hProduct
      rw [(MeasurePreserving.symm e hMass).map_eq,
        (MeasurePreserving.symm e hVolume).map_eq] at hMapped
      exact hMapped

/-- A nonzero polynomial evaluated after coordinatewise inversion has a
null zero set under every finite truncated-Gaussian product law. -/
theorem finiteLaw_zeroSet_eval_coordinatewiseInv_eq_zero
    (parameters : Parameters) {N : Nat}
    (P : MvPolynomial (Fin N) Real) (hP : P ≠ 0) :
    finiteLaw parameters N
        {x | MvPolynomial.eval (coordinatewiseInv x) P = 0} = 0 :=
  finiteLaw_absolutelyContinuous_volume parameters N
    (volume_zeroSet_eval_coordinatewiseInv_eq_zero P hP)

/-! ## Exact law of a finite restriction -/

/-- The first `N` mass coordinates of a Gaussian mass-phase ensemble. -/
def restrictMassFin {Omega : Type*} [MeasurableSpace Omega]
    {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega) {N : Nat}
    (omega : Omega) : Fin N → Real :=
  fun i ↦ ensemble.mass i.val omega

theorem measurable_restrictMassFin
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega) {N : Nat} :
    Measurable (restrictMassFin ensemble (N := N)) := by
  exact measurable_pi_lambda _ fun i ↦ ensemble.mass_measurable i.val

/-- Independence and the one-coordinate laws identify the finite restriction
with the exact finite truncated-Gaussian product law. -/
theorem restrictMassFin_hasLaw
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega) {N : Nat} :
    HasLaw (restrictMassFin ensemble (N := N))
      (finiteLaw parameters N) ensemble.probability := by
  have hIndep : iIndepFun
      (fun i : Fin N ↦ ensemble.mass i.val) ensemble.probability :=
    ensemble.mass_iIndep.precomp
      (g := fun i : Fin N ↦ i.val) Fin.val_injective
  have hLaw := hIndep.hasLaw_pi fun i : Fin N ↦ ensemble.mass_hasLaw i.val
  change HasLaw (fun (omega : Omega) (i : Fin N) ↦
      ensemble.mass i.val omega)
    (finiteLaw parameters N) ensemble.probability
  simpa [finiteLaw] using hLaw

/-- Any nonzero inverse-mass polynomial has zero event probability under a
verified Gaussian mass-phase ensemble. -/
theorem probability_eval_inverse_restrictMassFin_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega) {N : Nat}
    (P : MvPolynomial (Fin N) Real) (hP : P ≠ 0) :
    ensemble.probability
        {omega |
          MvPolynomial.eval
            (coordinatewiseInv (restrictMassFin ensemble omega)) P = 0} = 0 := by
  have hLaw := restrictMassFin_hasLaw ensemble (N := N)
  have hMeasurable : MeasurableSet
      {x : Fin N → Real |
        MvPolynomial.eval (coordinatewiseInv x) P = 0} := by
    apply MeasurableSet.preimage (isClosed_singleton.measurableSet)
    exact P.continuous_eval.measurable.comp
      (measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).inv)
  exact (hLaw.measure_eq hMeasurable).trans
    (finiteLaw_zeroSet_eval_coordinatewiseInv_eq_zero parameters P hP)

/-! ## The resultant certificate and full ordered simplicity -/

/-- The inverse masses of the finite periodic positive-mass restriction are
the coordinatewise inverses of the finite Gaussian mass vector. -/
theorem inverseMassCoordinates_restrictPositiveMass
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    inverseMassCoordinates
        (ensemble.restrictPositiveMass (N := N) omega) =
      coordinatewiseInv (restrictMassFin ensemble (N := N) omega) := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    ext k
    simp only [coordinatewiseInv_apply]
    change (ensemble.mass ((ZMod.finEquiv (n + 1)) k).val omega)⁻¹ =
      (ensemble.mass k.val omega)⁻¹
    change (ensemble.mass k.val omega)⁻¹ =
      (ensemble.mass k.val omega)⁻¹
    rfl

/-- The event of a repeated strictly positive harmonic eigenvalue is null for
every finite Gaussian chain of length at least two. -/
theorem probability_repeatedPositiveHarmonicEigenvalue_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ensemble.probability
        {omega |
          HasRepeatedPositiveHarmonicEigenvalue
            (ensemble.restrictPositiveMass (N := N) omega)} = 0 := by
  apply measure_mono_null (t :=
    {omega |
      MvPolynomial.eval
        (coordinatewiseInv (restrictMassFin ensemble (N := N) omega))
        (symbolicRepeatedRootCertificate (N := N)) = 0})
  · intro omega homega
    have hcertificate := certificate_vanishes_of_repeatedPositiveHarmonic
      (ensemble.restrictPositiveMass (N := N) omega) homega
    rwa [inverseMassCoordinates_restrictPositiveMass] at hcertificate
  · exact probability_eval_inverse_restrictMassFin_eq_zero ensemble
      (symbolicRepeatedRootCertificate (N := N))
      (symbolicRepeatedRootCertificate_ne_zero hN)

/-- The event of a duplicated positive ordered eigenvalue is null. -/
theorem probability_orderedPositiveDuplicate_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ensemble.probability
        {omega |
          HasOrderedPositiveDuplicate
            (ensemble.restrictPositiveMass (N := N) omega)} = 0 := by
  apply measure_mono_null (t :=
    {omega |
      HasRepeatedPositiveHarmonicEigenvalue
        (ensemble.restrictPositiveMass (N := N) omega)})
  · intro omega homega
    exact repeatedPositiveHarmonic_of_orderedPositiveDuplicate _ homega
  · exact probability_repeatedPositiveHarmonicEigenvalue_eq_zero ensemble hN

/-- The complete ordered harmonic spectrum, including the unique translation
zero mode, is almost surely simple for Gaussian iid masses. -/
theorem simpleOrderedSpectrum_ae
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ensemble.probability,
      SimpleOrderedSpectrum
        (harmonicHermitianSample
          (ensemble.restrictPositiveMass (N := N)) omega) := by
  have hnot : ∀ᵐ omega ∂ensemble.probability,
      ¬ HasOrderedPositiveDuplicate
        (ensemble.restrictPositiveMass (N := N) omega) :=
    measure_eq_zero_iff_ae_notMem.mp
      (probability_orderedPositiveDuplicate_eq_zero ensemble hN)
  filter_upwards [hnot] with omega homega
  exact simpleOrderedSpectrum_of_not_orderedPositiveDuplicate _ homega

end

end ArchonPhysics.GaussianRandomMassSimpleSpectrum

import ArchonPhysics.ConcreteGaussianTwoBandPhysicalInitialData
import ArchonPhysics.TruncatedGaussianCoordinateUpperDomination
import ArchonPhysics.FiniteMassPolynomialAvoidance
import ArchonPhysics.FiniteHarmonicHaarPhasePropagation
import ArchonPhysics.GaussianRandomMassSimpleSpectrum
import ArchonPhysics.TruncatedGaussianFiniteDomination

/-!
# Finite-volume event transfer between uniform and truncated-Gaussian ensembles

The frozen thermalization reduction is currently stated on the canonical iid
uniform-mass / Haar-phase ensemble, whereas the concrete physical initial data
use iid truncated-Gaussian masses and the same Haar phase law.  This file gives
the finite-volume change-of-law adapter between those two choices.

The comparison is deliberately made on the complete first-`N` mass/phase
block.  Thus every measurable finite-volume observable can be inserted by
precomposition.  The one-site domination coefficient tensorizes as its
`N`-th power.  In the reverse direction an RN upper bound `Gaussian <= C *
uniform` therefore costs `C ^ N`; transferring a high-probability statement
requires a uniform-ensemble failure probability that beats that exponential
factor.  No thermodynamic-uniform comparison of the two product laws is
claimed.

This is an ensemble-law adapter only.  It does not supply nonlinear RPA
propagation or the microscopic-to-kinetic estimate required by F3.
-/

namespace ArchonPhysics.TruncatedGaussianFiniteEventTransfer

open ArchonPhysics
open ArchonPhysics.GaussianRandomMassSimpleSpectrum
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TruncatedGaussianFiniteDomination
open ArchonPhysics.TruncatedGaussianCoordinateUpperDomination
open ArchonPhysics.TruncatedGaussianMassLaw
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The first `N` phase coordinates, indexed compatibly with the finite mass
vector. -/
def firstNPhase
    {Omega : Type*} [MeasurableSpace Omega]
    (phase : Nat -> Omega -> UnitAddCircle) (N : Nat) (omega : Omega) :
    Fin N -> UnitAddCircle :=
  fun i => phase i.val omega

/-- Product Haar law of the first `N` phase coordinates. -/
def finitePhaseLaw (N : Nat) : Measure (Fin N -> UnitAddCircle) :=
  Measure.pi fun _ : Fin N => RandomEnsemble.phaseCoordinateLaw

noncomputable instance finitePhaseLaw.instIsProbabilityMeasure (N : Nat) :
    IsProbabilityMeasure (finitePhaseLaw N) := by
  unfold finitePhaseLaw
  infer_instance

/-- Complete finite block used for every change-of-law statement. -/
abbrev FiniteBlock (N : Nat) :=
  (Fin N -> Real) × (Fin N -> UnitAddCircle)

/-- Uniform-mass / Haar-phase law of a complete finite block. -/
def uniformBlockLaw (N : Nat) : Measure (FiniteBlock N) :=
  (finiteMassLaw N).prod (finitePhaseLaw N)

/-- Truncated-Gaussian-mass / Haar-phase law of a complete finite block. -/
def gaussianBlockLaw (parameters : Parameters) (N : Nat) :
    Measure (FiniteBlock N) :=
  (finiteLaw parameters N).prod (finitePhaseLaw N)

noncomputable instance uniformBlockLaw.instIsProbabilityMeasure (N : Nat) :
    IsProbabilityMeasure (uniformBlockLaw N) := by
  unfold uniformBlockLaw
  infer_instance

noncomputable instance gaussianBlockLaw.instIsProbabilityMeasure
    (parameters : Parameters) (N : Nat) :
    IsProbabilityMeasure (gaussianBlockLaw parameters N) := by
  unfold gaussianBlockLaw
  infer_instance

/-- The complete first-`N` block of a verified uniform ensemble. -/
def uniformFiniteBlock
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) (N : Nat) (omega : Omega) :
    FiniteBlock N :=
  (ensemble.restrictMassFin omega, firstNPhase ensemble.phase N omega)

/-- The complete first-`N` block of a verified truncated-Gaussian ensemble. -/
def gaussianFiniteBlock
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    (N : Nat) (omega : Omega) : FiniteBlock N :=
  (restrictMassFin ensemble omega, firstNPhase ensemble.phase N omega)

/-- The first `N` phase coordinates of a verified uniform ensemble have the
finite product Haar law. -/
theorem uniform_firstNPhase_hasLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) (N : Nat) :
    HasLaw (firstNPhase ensemble.phase N) (finitePhaseLaw N)
      ensemble.probability := by
  have hindep : iIndepFun
      (fun i : Fin N => ensemble.phase i.val) ensemble.probability :=
    ensemble.phase_iIndep.precomp
      (g := fun i : Fin N => i.val) Fin.val_injective
  have hlaw := hindep.hasLaw_pi fun i : Fin N => ensemble.phase_hasLaw i.val
  change HasLaw (fun (omega : Omega) (i : Fin N) =>
      ensemble.phase i.val omega) (finitePhaseLaw N) ensemble.probability
  simpa [finitePhaseLaw] using hlaw

/-- The first `N` phase coordinates of a verified Gaussian ensemble have the
same finite product Haar law. -/
theorem gaussian_firstNPhase_hasLaw
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega) (N : Nat) :
    HasLaw (firstNPhase ensemble.phase N) (finitePhaseLaw N)
      ensemble.probability := by
  have hindep : iIndepFun
      (fun i : Fin N => ensemble.phase i.val) ensemble.probability :=
    ensemble.phase_iIndep.precomp
      (g := fun i : Fin N => i.val) Fin.val_injective
  have hlaw := hindep.hasLaw_pi fun i : Fin N => ensemble.phase_hasLaw i.val
  change HasLaw (fun (omega : Omega) (i : Fin N) =>
      ensemble.phase i.val omega) (finitePhaseLaw N) ensemble.probability
  simpa [finitePhaseLaw] using hlaw

/-- The uniform ensemble's complete first-`N` block has exactly the declared
product law. -/
theorem uniformFiniteBlock_hasLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) (N : Nat) :
    HasLaw (uniformFiniteBlock ensemble N) (uniformBlockLaw N)
      ensemble.probability := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hmass := ensemble.restrictMassFin_hasLaw (N := N)
  have hphase := uniform_firstNPhase_hasLaw ensemble N
  have hMassRestrict : Measurable
      (fun mass : Nat -> Real => fun i : Fin N => mass i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hPhaseRestrict : Measurable
      (fun phase : Nat -> UnitAddCircle =>
        fun i : Fin N => phase i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hindep := ensemble.mass_phase_indep.comp hMassRestrict hPhaseRestrict
  change HasLaw (fun omega : Omega =>
    (ensemble.restrictMassFin omega, firstNPhase ensemble.phase N omega))
    ((finiteMassLaw N).prod (finitePhaseLaw N)) ensemble.probability
  exact hindep.hasLaw_prod hmass hphase

/-- The Gaussian ensemble's complete first-`N` block has exactly the declared
product law. -/
theorem gaussianFiniteBlock_hasLaw
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega) (N : Nat) :
    HasLaw (gaussianFiniteBlock ensemble N) (gaussianBlockLaw parameters N)
      ensemble.probability := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hmass := restrictMassFin_hasLaw ensemble (N := N)
  have hphase := gaussian_firstNPhase_hasLaw ensemble N
  have hMassRestrict : Measurable
      (fun mass : Nat -> Real => fun i : Fin N => mass i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hPhaseRestrict : Measurable
      (fun phase : Nat -> UnitAddCircle =>
        fun i : Fin N => phase i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hindep := ensemble.mass_phase_indep.comp hMassRestrict hPhaseRestrict
  change HasLaw (fun omega : Omega =>
    (restrictMassFin ensemble omega, firstNPhase ensemble.phase N omega))
    ((finiteLaw parameters N).prod (finitePhaseLaw N)) ensemble.probability
  exact hindep.hasLaw_prod hmass hphase

/-! ## Tensorized law comparison -/

/-- A one-coordinate upper RN comparison tensorizes with the exact power
`constant ^ N`. -/
theorem finitePi_le_pow_smul_finitePi_of_le_smul
    (source target : Measure Real) [SigmaFinite source] [SigmaFinite target]
    (constant : ENNReal) (hone : source <= constant • target) :
    forall N : Nat,
      Measure.pi (fun _ : Fin N => source) <=
        constant ^ N • Measure.pi (fun _ : Fin N => target)
  | 0 => by
      simp only [pow_zero, one_smul]
      rw [Measure.pi_of_empty (fun _ : Fin 0 => source),
        Measure.pi_of_empty (fun _ : Fin 0 => target)]
  | n + 1 => by
      let splitEquiv := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Real) 0
      have hsourceSplit : MeasurePreserving splitEquiv
          (Measure.pi (fun _ : Fin (n + 1) => source))
          (source.prod (Measure.pi (fun _ : Fin n => source))) := by
        dsimp [splitEquiv]
        exact measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => source) 0
      have htargetSplit : MeasurePreserving splitEquiv
          (Measure.pi (fun _ : Fin (n + 1) => target))
          (target.prod (Measure.pi (fun _ : Fin n => target))) := by
        dsimp [splitEquiv]
        exact measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => target) 0
      have htail :=
        finitePi_le_pow_smul_finitePi_of_le_smul source target constant hone n
      have hproductRaw := Measure.prod_mono hone htail
      have hproduct :
          source.prod (Measure.pi (fun _ : Fin n => source)) <=
            constant ^ (n + 1) •
              (target.prod (Measure.pi (fun _ : Fin n => target))) := by
        convert hproductRaw using 1
        simp [Measure.prod_smul_left, Measure.prod_smul_right,
          smul_smul, pow_succ, mul_comm]
      have hmapped := Measure.map_mono hproduct splitEquiv.symm.measurable
      rw [(MeasurePreserving.symm splitEquiv hsourceSplit).map_eq,
        Measure.map_smul,
        (MeasurePreserving.symm splitEquiv htargetSplit).map_eq] at hmapped
      exact hmapped

/-- The already-proved compact-support lower density comparison extends to
the complete mass/Haar-phase block.  Its coefficient is an exact `N`-th
power. -/
theorem exists_uniformBlock_smul_le_gaussianBlock
    (parameters : Parameters) (N : Nat) :
    exists density : NNReal, 0 < density /\
      (density : ENNReal) • uniformBlockLaw N <=
        gaussianBlockLaw parameters N := by
  obtain ⟨oneDensity, honeDensity, hone⟩ :=
    exists_coordinateLaw_domination parameters
  refine ⟨oneDensity ^ N, pow_pos honeDensity _, ?_⟩
  have hmass := finitePi_smul_le_finitePi_of_smul_le
    massCoordinateLaw (coordinateLaw parameters)
    (oneDensity : ENNReal) hone N
  have hjoint := Measure.prod_mono hmass
    (show finitePhaseLaw N <= finitePhaseLaw N from le_rfl)
  simpa [uniformBlockLaw, gaussianBlockLaw, finiteMassLaw, finiteLaw,
    Measure.prod_smul_left, ENNReal.coe_pow] using hjoint

/-- A reverse one-site RN upper bound gives the finite-block estimate with
the unavoidable tensor factor `constant ^ N`. -/
theorem gaussianBlock_le_pow_smul_uniformBlock_of_coordinate_le
    (parameters : Parameters) (constant : ENNReal)
    (hone : coordinateLaw parameters <= constant • massCoordinateLaw)
    (N : Nat) :
    gaussianBlockLaw parameters N <=
      constant ^ N • uniformBlockLaw N := by
  have hmass := finitePi_le_pow_smul_finitePi_of_le_smul
    (coordinateLaw parameters) massCoordinateLaw constant hone N
  have hjoint := Measure.prod_mono hmass
    (show finitePhaseLaw N <= finitePhaseLaw N from le_rfl)
  simpa [uniformBlockLaw, gaussianBlockLaw, finiteMassLaw, finiteLaw,
    Measure.prod_smul_left] using hjoint
/-- The compact Gaussian density and positive conditioning normalization
construct the reverse finite-block comparison without any additional RN
hypothesis.  The witness remains finite and positive, but its tensor cost is
`constant ^ N`. -/
theorem exists_gaussianBlock_le_pow_smul_uniformBlock
    (parameters : Parameters) (N : Nat) :
    ∃ constant : ENNReal, 0 < constant ∧ constant ≠ ∞ ∧
      gaussianBlockLaw parameters N <=
        constant ^ N • uniformBlockLaw N := by
  obtain ⟨constant, hconstantPositive, hconstantFinite, hone⟩ :=
    exists_coordinateLaw_le_smul_massCoordinateLaw parameters
  exact ⟨constant, hconstantPositive, hconstantFinite,
    gaussianBlock_le_pow_smul_uniformBlock_of_coordinate_le
      parameters constant hone N⟩


/-! ## Event and observable adapters -/

/-- Every measurable finite-block event inherits the lower comparison from
the existing truncated-Gaussian density theorem. -/
theorem exists_uniform_event_scaled_le_gaussian_event
    (parameters : Parameters) (N : Nat) (event : Set (FiniteBlock N)) :
    exists density : NNReal, 0 < density /\
      (density : ENNReal) * uniformBlockLaw N event <=
        gaussianBlockLaw parameters N event := by
  obtain ⟨density, hdensity, hmeasure⟩ :=
    exists_uniformBlock_smul_le_gaussianBlock parameters N
  refine ⟨density, hdensity, ?_⟩
  simpa [Measure.smul_apply, smul_eq_mul] using Measure.le_iff'.1 hmeasure event

/-- Under an explicit reverse RN upper bound, every finite-block event costs
at most `constant ^ N`. -/
theorem gaussian_event_le_pow_mul_uniform_event_of_coordinate_le
    (parameters : Parameters) (constant : ENNReal)
    (hone : coordinateLaw parameters <= constant • massCoordinateLaw)
    (N : Nat) (event : Set (FiniteBlock N)) :
    gaussianBlockLaw parameters N event <=
      constant ^ N * uniformBlockLaw N event := by
  have hmeasure := gaussianBlock_le_pow_smul_uniformBlock_of_coordinate_le
    parameters constant hone N
  simpa [Measure.smul_apply, smul_eq_mul] using Measure.le_iff'.1 hmeasure event

/-- Observable form of the reverse transfer: the event may be defined after
any common measurable finite-volume observable. -/
theorem gaussian_observable_event_le_pow_mul_uniform
    {Alpha : Type*} [MeasurableSpace Alpha]
    (parameters : Parameters) (constant : ENNReal)
    (hone : coordinateLaw parameters <= constant • massCoordinateLaw)
    (N : Nat) (observable : FiniteBlock N -> Alpha)
    (event : Set Alpha) :
    gaussianBlockLaw parameters N (observable ⁻¹' event) <=
      constant ^ N *
        uniformBlockLaw N (observable ⁻¹' event) :=
  gaussian_event_le_pow_mul_uniform_event_of_coordinate_le
    parameters constant hone N (observable ⁻¹' event)

/-- Quantitative high-probability adapter at one finite volume.  To make the
Gaussian failure probability at most `epsilon`, the uniform failure bound
must already be at most `epsilon / constant ^ N`; this hypothesis is written
without division so the exponential cost remains visible. -/
theorem gaussian_failure_le_of_uniform_failure_beats_exponential
    (parameters : Parameters) (constant : ENNReal)
    (hone : coordinateLaw parameters <= constant • massCoordinateLaw)
    (N : Nat) (failure : Set (FiniteBlock N)) (epsilon : ENNReal)
    (hrate : constant ^ N * uniformBlockLaw N failure <= epsilon) :
    gaussianBlockLaw parameters N failure <= epsilon := by
  exact (gaussian_event_le_pow_mul_uniform_event_of_coordinate_le
    parameters constant hone N failure).trans hrate

/-- Sample-space version for any pair of verified ensembles and every common
finite-block event.  This is the form needed to compare a uniform canonical
finite-volume estimate with the concrete truncated-Gaussian ensemble. -/
theorem gaussian_sample_failure_le_of_uniform_sample_failure_beats_exponential
    {OmegaU OmegaG : Type*} [MeasurableSpace OmegaU] [MeasurableSpace OmegaG]
    (uniformEnsemble : IIDMassPhaseEnsemble OmegaU)
    {parameters : Parameters}
    (gaussianEnsemble : GaussianIIDMassPhaseEnsemble parameters OmegaG)
    (constant : ENNReal)
    (hone : coordinateLaw parameters <= constant • massCoordinateLaw)
    (N : Nat) (failure : Set (FiniteBlock N))
    (hfailure : MeasurableSet failure) (epsilon : ENNReal)
    (hrate : constant ^ N *
        uniformEnsemble.probability
          ((uniformFiniteBlock uniformEnsemble N) ⁻¹' failure) <= epsilon) :
    gaussianEnsemble.probability
        ((gaussianFiniteBlock gaussianEnsemble N) ⁻¹' failure) <= epsilon := by
  have huniform :=
    (uniformFiniteBlock_hasLaw uniformEnsemble N).measure_eq hfailure
  have hgaussian :=
    (gaussianFiniteBlock_hasLaw gaussianEnsemble N).measure_eq hfailure
  change uniformEnsemble.probability
    ((uniformFiniteBlock uniformEnsemble N) ⁻¹' failure) =
      uniformBlockLaw N failure at huniform
  change gaussianEnsemble.probability
    ((gaussianFiniteBlock gaussianEnsemble N) ⁻¹' failure) =
      gaussianBlockLaw parameters N failure at hgaussian
  rw [huniform] at hrate
  rw [hgaussian]
  exact gaussian_failure_le_of_uniform_failure_beats_exponential
    parameters constant hone N failure epsilon hrate

end

end ArchonPhysics.TruncatedGaussianFiniteEventTransfer

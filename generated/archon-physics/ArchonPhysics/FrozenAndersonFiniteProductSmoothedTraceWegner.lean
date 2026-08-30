import ArchonPhysics.FrozenAndersonOneSitePoissonAveraging
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Instances.Matrix

/-!
# Finite-product eta-smoothed Wegner bound for frozen iid Anderson masses

This module reconstructs the full canonical finite iid mass law from the
one-site Poisson estimate.  The measure-theoretic core splits an arbitrary
coordinate of `Fin (n + 1)` by `piFinSuccAbove`, proves integrability from
uniformly integrable nonnegative sections, and applies Fubini without a
conditional-expectation premise.

For a finite real Hermitian background and iid
`Uniform[4/5, 6/5]` masses, the actual Anderson resolvent is shown continuous
in the complete mass vector.  Freezing every coordinate except one gives
exactly the one-site rank-one family proved in
`FrozenAndersonOneSitePoissonAveraging`.  Summing the reconstructed local
Green estimates yields

`E[-Im trace ((E + i eta) I - H)⁻¹] <=
  card * (5 / 2) * |lambda|⁻¹ * pi`

for `eta > 0` and `lambda != 0`.

This is the finite-volume eta-smoothed trace Wegner endpoint.  No Markov
inequality, Stone formula, spectral-projector limit, localization estimate,
or unsmoothed Wegner premise is used.
-/

namespace ArchonPhysics.FrozenAndersonFiniteProductSmoothedTraceWegner

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.FrozenAndersonOneSitePoissonAveraging
open MeasureTheory
open scoped BigOperators ENNReal Matrix

noncomputable section

/-! ## Coordinate conditioning on a finite product probability law -/

/-- Split any selected coordinate of a finite product probability law.

If a nonnegative measurable observable has integrable selected-coordinate
sections, all bounded by the same real constant, then the observable is
integrable under the full product law and its integral has the same bound.
This is the explicit finite-product Fubini replacement for an abstract
conditional-expectation premise. -/
theorem finitePi_coordinate_integrable_and_integral_le
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    {n : Nat} (i : Fin (n + 1))
    {f : (Fin (n + 1) -> alpha) -> Real} {C : Real}
    (hf : Measurable f) (_hC : 0 <= C)
    (hnonneg : forall x, 0 <= f x)
    (hsection_integrable : forall rest : Fin n -> alpha,
      Integrable
        (fun x => f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => alpha) i).symm (x, rest))) mu)
    (hsection_le : forall rest : Fin n -> alpha,
      (integral mu fun x => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => alpha) i).symm (x, rest))) <= C) :
    Integrable f (Measure.pi fun _ : Fin (n + 1) => mu) /\
      (integral (Measure.pi fun _ : Fin (n + 1) => mu) f <= C) := by
  let tailMeasure : Measure (Fin n -> alpha) :=
    Measure.pi fun _ : Fin n => mu
  let splitEquiv : (Fin (n + 1) -> alpha) ≃ᵐ
      alpha × (Fin n -> alpha) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => alpha) i
  let F : alpha × (Fin n -> alpha) -> Real :=
    fun state => f (splitEquiv.symm state)
  let g : (Fin n -> alpha) -> Real :=
    fun rest => integral mu fun x => F (x, rest)
  let _ : IsProbabilityMeasure tailMeasure := by
    dsimp [tailMeasure]
    infer_instance
  have hsplit : MeasurePreserving splitEquiv
      (Measure.pi fun _ : Fin (n + 1) => mu)
      (mu.prod tailMeasure) := by
    dsimp [splitEquiv, tailMeasure]
    exact measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => mu) i
  have hF : Measurable F := by
    exact hf.comp splitEquiv.symm.measurable
  have hg_measurable : Measurable g := by
    exact hF.stronglyMeasurable.integral_prod_left'.measurable
  have hg_nonneg : forall rest, 0 <= g rest := by
    intro rest
    apply integral_nonneg
    intro x
    exact hnonneg _
  have hg_le : forall rest, g rest <= C := hsection_le
  have hg_integrable : Integrable g tailMeasure := by
    apply Integrable.of_mem_Icc 0 C hg_measurable.aemeasurable
    exact Filter.Eventually.of_forall fun rest =>
      ⟨hg_nonneg rest, hg_le rest⟩
  have hF_integrable : Integrable F (mu.prod tailMeasure) := by
    apply (integrable_prod_iff' hF.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall hsection_integrable
    · have hnorm : (fun rest => integral mu fun x => ‖F (x, rest)‖) = g := by
        funext rest
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
      simpa only [hnorm] using hg_integrable
  have hf_integrable :
      Integrable f (Measure.pi fun _ : Fin (n + 1) => mu) := by
    exact (hsplit.symm.integrable_comp_emb
      splitEquiv.symm.measurableEmbedding).mp hF_integrable
  refine ⟨hf_integrable, ?_⟩
  calc
    integral (Measure.pi fun _ : Fin (n + 1) => mu) f =
        integral (mu.prod tailMeasure) F := by
      exact (hsplit.symm.integral_comp' f).symm
    _ = integral tailMeasure g := by
      exact integral_prod_symm F hF_integrable
    _ <= integral tailMeasure (fun _ => C) := by
      exact integral_mono hg_integrable (integrable_const C) hg_le
    _ = C := by simp

/-! ## The actual finite Anderson matrix and its frozen sections -/

/-- The canonical finite iid law of the frozen mass coordinates. -/
def canonicalFiniteIIDMassLaw (N : Nat) : Measure (Fin N -> Real) :=
  Measure.pi fun _ : Fin N => massCoordinateLaw

/-- A finite real Hermitian background with diagonal Anderson masses. -/
def finiteAndersonHamiltonian
    {index : Type*} [DecidableEq index]
    (background : Matrix index index Real) (lambda : Real)
    (mass : index -> Real) : Matrix index index Real :=
  background + Matrix.diagonal (fun i => lambda * mass i)

theorem finiteAndersonHamiltonian_isHermitian
    {index : Type*} [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda : Real) (mass : index -> Real) :
    (finiteAndersonHamiltonian background lambda mass).IsHermitian := by
  exact hbackground.add (Matrix.isHermitian_diagonal _)

/-- The upper-half-plane shifted finite Anderson matrix. -/
def finiteAndersonShiftedMatrix
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (lambda : Real)
    (mass : index -> Real) (z : Complex) : Matrix index index Complex :=
  complexHermitianResolventMatrix
    ((finiteAndersonHamiltonian background lambda mass).map Complex.ofReal) z

/-- The diagonal local Green element of the finite Anderson resolvent. -/
def finiteAndersonLocalGreen
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (lambda : Real)
    (mass : index -> Real) (i : index) (z : Complex) : Complex :=
  (finiteAndersonShiftedMatrix background lambda mass z)⁻¹ i i

/-- The eta-smoothed finite-volume trace at a complex spectral parameter. -/
def finiteAndersonSmoothedTrace
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (lambda : Real)
    (mass : index -> Real) (z : Complex) : Real :=
  -(Matrix.trace (finiteAndersonShiftedMatrix background lambda mass z)⁻¹).im

/-- Freeze every coordinate except `i`, using zero at the selected diagonal. -/
def finiteAndersonFrozenBackground
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (lambda : Real) (i : Fin (n + 1)) (rest : Fin n -> Real) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  finiteAndersonHamiltonian background lambda
    ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => Real) i).symm (0, rest))

theorem finiteAndersonFrozenBackground_isHermitian
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (i : Fin (n + 1)) (rest : Fin n -> Real) :
    (finiteAndersonFrozenBackground background lambda i rest).IsHermitian := by
  exact finiteAndersonHamiltonian_isHermitian background hbackground lambda _

/-- Inserting the selected mass into the zeroed frozen background is exactly
the full Anderson Hamiltonian reconstructed by `piFinSuccAbove`. -/
theorem oneSiteAndersonMatrix_finiteAndersonFrozenBackground
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (lambda mass : Real) (i : Fin (n + 1)) (rest : Fin n -> Real) :
    oneSiteAndersonMatrix
        (finiteAndersonFrozenBackground background lambda i rest)
        i (andersonDiagonalPotential lambda mass) =
      finiteAndersonHamiltonian background lambda
        ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Real) i).symm (mass, rest)) := by
  apply Matrix.ext
  intro p q
  simp only [finiteAndersonFrozenBackground, finiteAndersonHamiltonian,
    oneSiteAndersonMatrix, andersonDiagonalPotential, Matrix.add_apply,
    Matrix.diagonal_apply, Matrix.smul_apply, Matrix.vecMulVec,
    realSiteVector, smul_eq_mul,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk]
  by_cases hpq : p = q
  · subst q
    rcases i.eq_self_or_eq_succAbove p with hp | ⟨j, rfl⟩
    · subst p
      simp
    · simp
  · by_cases hp : p = i
    · subst p
      have hq : q ≠ i := by
        intro hqi
        exact hpq hqi.symm
      simp [hpq, hq]
    · by_cases hq : q = i
      · subst q
        simp [hpq]
      · simp [hpq, hp, hq]

/-! ## Continuity, positivity, and the trace identity -/

theorem continuous_finiteAndersonHamiltonian
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (lambda : Real) :
    Continuous (finiteAndersonHamiltonian background lambda) := by
  unfold finiteAndersonHamiltonian
  fun_prop

theorem continuous_finiteAndersonShiftedMatrix
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (lambda : Real) (z : Complex) :
    Continuous fun mass : index -> Real =>
      finiteAndersonShiftedMatrix background lambda mass z := by
  unfold finiteAndersonShiftedMatrix complexHermitianResolventMatrix
  apply Continuous.sub
  · have hzcont : Continuous fun _ : (index -> Real) => z := continuous_const
    have hone : Continuous fun _ : (index -> Real) =>
        (1 : Matrix index index Complex) := continuous_const
    exact hzcont.smul hone
  · exact (continuous_finiteAndersonHamiltonian background lambda).matrix_map
      Complex.continuous_ofReal

/-- The full resolvent is continuous in all masses.  The determinant never
vanishes in the upper or lower half-plane, so the nonsingular inverse is the
continuous adjugate divided by the determinant. -/
theorem continuous_finiteAndersonShiftedMatrix_inv
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda : Real) (z : Complex) (hz : z.im ≠ 0) :
    Continuous fun mass : index -> Real =>
      (finiteAndersonShiftedMatrix background lambda mass z)⁻¹ := by
  let A : (index -> Real) -> Matrix index index Complex :=
    fun mass => finiteAndersonShiftedMatrix background lambda mass z
  have hA : Continuous A :=
    continuous_finiteAndersonShiftedMatrix background lambda z
  have hdet : forall mass, (A mass).det ≠ 0 := by
    intro mass
    exact (complexHermitianResolventMatrix_det_isUnit _
      (isHermitian_map_ofReal
        (finiteAndersonHamiltonian_isHermitian
          background hbackground lambda mass)) z hz).ne_zero
  have hformula : (fun mass => (A mass)⁻¹) =
      fun mass => (A mass).det⁻¹ • (A mass).adjugate := by
    funext mass
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [show (fun mass => (finiteAndersonShiftedMatrix
      background lambda mass z)⁻¹) = fun mass => (A mass)⁻¹ by rfl]
  rw [hformula]
  exact (hA.matrix_det.inv₀ hdet).smul hA.matrix_adjugate

theorem continuous_finiteAndersonLocalGreen
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda : Real) (i : index) (z : Complex) (hz : z.im ≠ 0) :
    Continuous fun mass : index -> Real =>
      finiteAndersonLocalGreen background lambda mass i z := by
  unfold finiteAndersonLocalGreen
  exact (continuous_apply i).comp ((continuous_apply i).comp
    (continuous_finiteAndersonShiftedMatrix_inv
      background hbackground lambda z hz))

theorem measurable_finiteAndersonLocalGreen_neg_im
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda : Real) (i : index) (z : Complex) (hz : z.im ≠ 0) :
    Measurable fun mass : index -> Real =>
      -(finiteAndersonLocalGreen background lambda mass i z).im := by
  exact ((Complex.continuous_im.comp
    (continuous_finiteAndersonLocalGreen
      background hbackground lambda i z hz)).neg).measurable

/-- The full local Green section is definitionally the frozen one-site Green
family after the coordinate reconstruction. -/
theorem finiteAndersonLocalGreen_eq_finiteFrozenOneSiteGreen
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (lambda mass : Real) (i : Fin (n + 1)) (rest : Fin n -> Real)
    (z : Complex) :
    finiteAndersonLocalGreen background lambda
        ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Real) i).symm (mass, rest)) i z =
      finiteFrozenOneSiteGreen
        (finiteAndersonFrozenBackground background lambda i rest)
        i z lambda mass := by
  unfold finiteFrozenOneSiteGreen
  rw [finiteHermitianOneSiteGreen_eq_resolventQuadraticElement]
  rw [oneSiteAndersonMatrix_finiteAndersonFrozenBackground]
  unfold finiteAndersonLocalGreen finiteAndersonShiftedMatrix
  unfold resolventQuadraticElement
  rw [star_complexSiteVector]
  exact (bilinearResolventElement_complexSiteVector_eq_apply _ i).symm

theorem finiteAndersonLocalGreen_neg_im_pos
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (lambda : Real) (mass : index -> Real) (i : index)
    (z : Complex) (hz : 0 < z.im) :
    0 < -(finiteAndersonLocalGreen background lambda mass i z).im := by
  have hpos := resolventQuadraticElement_neg_im_pos
    ((finiteAndersonHamiltonian background lambda mass).map Complex.ofReal)
    (isHermitian_map_ofReal
      (finiteAndersonHamiltonian_isHermitian background hbackground lambda mass))
    z hz (complexSiteVector i) (complexSiteVector_ne_zero i)
  unfold finiteAndersonLocalGreen finiteAndersonShiftedMatrix
  unfold resolventQuadraticElement at hpos
  rw [star_complexSiteVector] at hpos
  have heq := bilinearResolventElement_complexSiteVector_eq_apply
    (complexHermitianResolventMatrix
      ((finiteAndersonHamiltonian background lambda mass).map Complex.ofReal) z) i
  unfold bilinearResolventElement at heq
  rw [heq] at hpos
  exact hpos

theorem finiteAndersonSmoothedTrace_eq_sum_localGreen_neg_im
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (lambda : Real)
    (mass : index -> Real) (z : Complex) :
    finiteAndersonSmoothedTrace background lambda mass z =
      ∑ i : index, -(finiteAndersonLocalGreen background lambda mass i z).im := by
  let A := finiteAndersonShiftedMatrix background lambda mass z
  change -(Matrix.trace A⁻¹).im = ∑ i : index, -(A⁻¹ i i).im
  rw [trace_nonsing_inv_eq_sum_bilinearResolventElement_complexSiteVector]
  simp_rw [bilinearResolventElement_complexSiteVector_eq_apply]
  simp

/-! ## One-site sections and full finite-product estimates -/

/-- Integrability of the frozen one-site Green section.  This makes explicit
the integrability fact used when upgrading the Bochner one-site estimate to
finite-product Fubini. -/
theorem integrable_finiteFrozenOneSiteGreen_neg_im_massCoordinateLaw
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im)
    (reference lambda : Real) (hlambda : lambda ≠ 0) :
    Integrable
      (fun mass : Real =>
        -(finiteFrozenOneSiteGreen background i z lambda mass).im)
      massCoordinateLaw := by
  let alpha := oneSiteEffectiveHerglotzParameter background i z reference
  have halpha : 0 < alpha.im :=
    oneSiteEffectiveHerglotzParameter_im_pos
      background hbackground i z hz reference
  have hscaled : Integrable (realLinePoissonKernel alpha.re alpha.im)
      (((5 / 2 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) •
        (volume : Measure Real)) :=
    (integrable_realLinePoissonKernel alpha.re alpha.im halpha.ne').smul_measure
      (by finiteness)
  have hpotential : Integrable (realLinePoissonKernel alpha.re alpha.im)
      (andersonDiagonalPotentialLaw lambda) :=
    hscaled.mono_measure
      (andersonDiagonalPotentialLaw_le_fiveHalves_smul_volume hlambda)
  have hmass : Integrable
      (fun mass : Real => realLinePoissonKernel alpha.re alpha.im
        (andersonDiagonalPotential lambda mass)) massCoordinateLaw := by
    unfold andersonDiagonalPotentialLaw at hpotential
    exact hpotential.comp_measurable (measurable_const.mul measurable_id)
  apply hmass.congr
  filter_upwards [] with mass
  unfold finiteFrozenOneSiteGreen
  rw [finiteHermitianOneSiteGreen_eq_inv_sub
    background hbackground i z hz reference]
  exact (neg_im_inv_sub_real_eq_realLinePoissonKernel alpha
    (andersonDiagonalPotential lambda mass)).symm

/-- The sharp one-site Poisson bound after reconstructing the selected
coordinate inside the complete canonical iid finite product law. -/
theorem integrable_and_integral_finiteAndersonLocalGreen_neg_im_canonicalFiniteIIDMassLaw
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (i : Fin (n + 1)) (z : Complex) (hz : 0 < z.im) :
    Integrable
        (fun mass => -(finiteAndersonLocalGreen
          background lambda mass i z).im)
        (canonicalFiniteIIDMassLaw (n + 1)) /\
      (integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => -(finiteAndersonLocalGreen
          background lambda mass i z).im) <=
        (5 / 2 : Real) * |lambda|⁻¹ * Real.pi) := by
  unfold canonicalFiniteIIDMassLaw
  apply finitePi_coordinate_integrable_and_integral_le
    massCoordinateLaw i
  · exact measurable_finiteAndersonLocalGreen_neg_im
      background hbackground lambda i z hz.ne'
  · positivity
  · intro mass
    exact (finiteAndersonLocalGreen_neg_im_pos
      background hbackground lambda mass i z hz).le
  · intro rest
    simpa only [finiteAndersonLocalGreen_eq_finiteFrozenOneSiteGreen] using
      integrable_finiteFrozenOneSiteGreen_neg_im_massCoordinateLaw
        (finiteAndersonFrozenBackground background lambda i rest)
        (finiteAndersonFrozenBackground_isHermitian
          background hbackground lambda i rest)
        i z hz 0 lambda hlambda
  · intro rest
    simpa only [finiteAndersonLocalGreen_eq_finiteFrozenOneSiteGreen] using
      integral_finiteFrozenOneSiteGreen_neg_im_massCoordinateLaw_le
        (finiteAndersonFrozenBackground background lambda i rest)
        (finiteAndersonFrozenBackground_isHermitian
          background hbackground lambda i rest)
        i z hz 0 lambda hlambda

theorem integrable_finiteAndersonSmoothedTrace_canonicalFiniteIIDMassLaw
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (z : Complex) (hz : 0 < z.im) :
    Integrable (fun mass => finiteAndersonSmoothedTrace
      background lambda mass z) (canonicalFiniteIIDMassLaw (n + 1)) := by
  have hsum : Integrable
      (fun mass => ∑ i : Fin (n + 1),
        -(finiteAndersonLocalGreen background lambda mass i z).im)
      (canonicalFiniteIIDMassLaw (n + 1)) := by
    exact integrable_finsetSum Finset.univ fun i _ =>
      (integrable_and_integral_finiteAndersonLocalGreen_neg_im_canonicalFiniteIIDMassLaw
        background hbackground lambda hlambda i z hz).1
  exact hsum.congr (Filter.Eventually.of_forall fun mass =>
    (finiteAndersonSmoothedTrace_eq_sum_localGreen_neg_im
      background lambda mass z).symm)

/-- Finite-volume eta-smoothed trace Wegner bound under the complete
canonical iid `Uniform[4/5, 6/5]` mass law. -/
theorem integral_finiteAndersonSmoothedTrace_canonicalFiniteIIDMassLaw_le
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (z : Complex) (hz : 0 < z.im) :
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => finiteAndersonSmoothedTrace background lambda mass z) <=
      (n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi) := by
  calc
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => finiteAndersonSmoothedTrace background lambda mass z) =
      integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => ∑ i : Fin (n + 1),
          -(finiteAndersonLocalGreen background lambda mass i z).im) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun mass =>
        finiteAndersonSmoothedTrace_eq_sum_localGreen_neg_im
          background lambda mass z
    _ = ∑ i : Fin (n + 1),
        integral (canonicalFiniteIIDMassLaw (n + 1))
          (fun mass => -(finiteAndersonLocalGreen
            background lambda mass i z).im) := by
      rw [integral_finsetSum Finset.univ]
      intro i _
      exact
        (integrable_and_integral_finiteAndersonLocalGreen_neg_im_canonicalFiniteIIDMassLaw
          background hbackground lambda hlambda i z hz).1
    _ <= ∑ _i : Fin (n + 1),
        (5 / 2 : Real) * |lambda|⁻¹ * Real.pi := by
      apply Finset.sum_le_sum
      intro i _
      exact
        (integrable_and_integral_finiteAndersonLocalGreen_neg_im_canonicalFiniteIIDMassLaw
          background hbackground lambda hlambda i z hz).2
    _ = (n + 1 : Real) *
        ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi) := by simp

/-! ## Explicit energy and eta parameterization -/

def finiteAndersonEtaSmoothedTrace
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (lambda energy eta : Real)
    (mass : index -> Real) : Real :=
  finiteAndersonSmoothedTrace background lambda mass
    ((energy : Complex) + (eta : Complex) * Complex.I)

theorem integrable_finiteAndersonEtaSmoothedTrace_canonicalFiniteIIDMassLaw
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (energy eta : Real) (heta : 0 < eta) :
    Integrable (finiteAndersonEtaSmoothedTrace
      background lambda energy eta) (canonicalFiniteIIDMassLaw (n + 1)) := by
  unfold finiteAndersonEtaSmoothedTrace
  apply integrable_finiteAndersonSmoothedTrace_canonicalFiniteIIDMassLaw
    background hbackground lambda hlambda
  simpa using heta

/-- Explicit `eta > 0` form of the no-axiom finite-volume smoothed Wegner
estimate. -/
theorem integral_finiteAndersonEtaSmoothedTrace_canonicalFiniteIIDMassLaw_le
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (energy eta : Real) (heta : 0 < eta) :
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (finiteAndersonEtaSmoothedTrace background lambda energy eta) <=
      (n + 1 : Real) * ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi) := by
  unfold finiteAndersonEtaSmoothedTrace
  apply integral_finiteAndersonSmoothedTrace_canonicalFiniteIIDMassLaw_le
    background hbackground lambda hlambda
  simpa using heta

end

end ArchonPhysics.FrozenAndersonFiniteProductSmoothedTraceWegner

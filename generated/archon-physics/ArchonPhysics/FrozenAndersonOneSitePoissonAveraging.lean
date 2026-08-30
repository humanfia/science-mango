import ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Poisson spectral averaging for a frozen Anderson site

This module closes the eta-smoothed one-site spectral-averaging step for a
finite real Hermitian Anderson Hamiltonian.  It evaluates the real-line
Poisson kernel exactly, transfers a bounded Lebesgue-density ceiling to the
sharp `pi * densityBound` integral estimate, proves upper-half-plane
invertibility and strict Herglotz sign directly for finite Hermitian
resolvents, and connects those facts to the existing one-site
Sherman--Morrison Mobius law.

For the frozen `Uniform[4/5, 6/5]` mass coordinate and nonzero diagonal scale
`lambda`, the resulting local Green expectation is at most
`5 * pi / (2 * |lambda|)`.  A finite sum records the corresponding collection
of frozen-environment conditional estimates, and a trace identity identifies
the deterministic sum of coordinate Green elements.

No boundary-value or Stone limit is used.  The remaining step to an
unsmoothed finite-volume Wegner projector bound is precisely a formal
conditional-Fubini reconstruction under the full finite iid product law,
followed by a proved Stone/projector limit; neither is asserted here.
-/

namespace ArchonPhysics.FrozenAndersonOneSitePoissonAveraging

open ArchonPhysics
open ArchonPhysics.FrozenAndersonDiagonalPotentialDensity
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open MeasureTheory
open scoped ENNReal Matrix ComplexOrder

noncomputable section

def realLinePoissonKernel (center eta x : Real) : Real :=
  eta / ((x - center) ^ 2 + eta ^ 2)

theorem realLinePoissonKernel_nonneg
    (center x : Real) {eta : Real} (heta : 0 ≤ eta) :
    0 ≤ realLinePoissonKernel center eta x := by
  unfold realLinePoissonKernel
  positivity

theorem realLinePoissonKernel_eq_scaled_standard
    (center eta x : Real) (heta : eta ≠ 0) :
    realLinePoissonKernel center eta (x + center) =
      eta⁻¹ * (1 + (x / eta) ^ 2)⁻¹ := by
  unfold realLinePoissonKernel
  field_simp
  ring

theorem realLinePoissonKernel_eq_scaled_standard_sub
    (center eta x : Real) (heta : eta ≠ 0) :
    realLinePoissonKernel center eta x =
      eta⁻¹ * (1 + ((x - center) / eta) ^ 2)⁻¹ := by
  simpa using realLinePoissonKernel_eq_scaled_standard
    center eta (x - center) heta

theorem continuous_realLinePoissonKernel
    (center eta : Real) (heta : eta ≠ 0) :
    Continuous (realLinePoissonKernel center eta) := by
  unfold realLinePoissonKernel
  apply Continuous.div continuous_const
    ((continuous_id.sub continuous_const).pow 2 |>.add continuous_const)
  intro x
  have : 0 < (x - center) ^ 2 + eta ^ 2 := by positivity
  exact this.ne'

theorem integrable_realLinePoissonKernel
    (center eta : Real) (heta : eta ≠ 0) :
    Integrable (realLinePoissonKernel center eta) := by
  have hscaled : Integrable (fun x : Real => (1 + (x / eta) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div heta
  have htranslated := hscaled.comp_add_right (-center)
  have htarget : Integrable
      (fun x : Real => eta⁻¹ * (1 + ((x - center) / eta) ^ 2)⁻¹) := by
    simpa [sub_eq_add_neg] using htranslated.const_mul eta⁻¹
  exact htarget.congr (Filter.Eventually.of_forall fun x =>
    (realLinePoissonKernel_eq_scaled_standard_sub center eta x heta).symm)

theorem integral_realLinePoissonKernel (center eta : Real) (heta : 0 < eta) :
    ∫ x : Real, realLinePoissonKernel center eta x = Real.pi := by
  rw [← integral_add_right_eq_self (realLinePoissonKernel center eta) center]
  simp_rw [realLinePoissonKernel_eq_scaled_standard center eta _ heta.ne']
  rw [integral_const_mul]
  rw [Measure.integral_comp_div (fun x : Real => (1 + x ^ 2)⁻¹) eta]
  simp [smul_eq_mul, abs_of_pos heta, heta.ne']

theorem integral_realLinePoissonKernel_le_of_measure_le
    {mu : Measure Real} {densityBound : ENNReal}
    (hdensityBound : densityBound ≠ ∞)
    (hmu : mu ≤ densityBound • (volume : Measure Real))
    (center eta : Real) (heta : 0 < eta) :
    ∫ x : Real, realLinePoissonKernel center eta x ∂mu ≤
      densityBound.toReal * Real.pi := by
  calc
    ∫ x : Real, realLinePoissonKernel center eta x ∂mu ≤
        ∫ x : Real, realLinePoissonKernel center eta x
          ∂(densityBound • (volume : Measure Real)) := by
      exact integral_mono_measure hmu
        (Filter.Eventually.of_forall fun x =>
          realLinePoissonKernel_nonneg center x heta.le)
        ((integrable_realLinePoissonKernel center eta heta.ne').smul_measure
          hdensityBound)
    _ = densityBound.toReal *
        ∫ x : Real, realLinePoissonKernel center eta x := by
      rw [integral_smul_measure]
      rfl
    _ = densityBound.toReal * Real.pi := by
      rw [integral_realLinePoissonKernel center eta heta]

theorem neg_im_inv_sub_real_eq_realLinePoissonKernel
    (alpha : Complex) (x : Real) :
    -((alpha - (x : Complex))⁻¹).im =
      realLinePoissonKernel alpha.re alpha.im x := by
  rw [Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero,
    Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re]
  unfold realLinePoissonKernel
  ring

theorem integral_neg_im_inv_sub_real_le_of_measure_le
    {mu : Measure Real} {densityBound : ENNReal}
    (hdensityBound : densityBound ≠ ∞)
    (hmu : mu ≤ densityBound • (volume : Measure Real))
    (alpha : Complex) (halpha : 0 < alpha.im) :
    ∫ x : Real, -((alpha - (x : Complex))⁻¹).im ∂mu ≤
      densityBound.toReal * Real.pi := by
  simpa only [neg_im_inv_sub_real_eq_realLinePoissonKernel] using
    integral_realLinePoissonKernel_le_of_measure_le
      hdensityBound hmu alpha.re alpha.im halpha

def complexHermitianResolventMatrix
    {index : Type*} [Fintype index] [DecidableEq index]
    (H : Matrix index index Complex) (z : Complex) :
    Matrix index index Complex :=
  z • (1 : Matrix index index Complex) - H

def resolventQuadraticElement
    {index : Type*} [Fintype index] [DecidableEq index]
    (H : Matrix index index Complex) (z : Complex)
    (u : index → Complex) : Complex :=
  star u ⬝ᵥ ((complexHermitianResolventMatrix H z)⁻¹ *ᵥ u)

theorem complexHermitianResolventMatrix_det_isUnit
    {index : Type*} [Fintype index] [DecidableEq index]
    (H : Matrix index index Complex) (hH : H.IsHermitian)
    (z : Complex) (hz : z.im ≠ 0) :
    IsUnit (complexHermitianResolventMatrix H z).det := by
  have hznot : z ∉ spectrum Complex H := by
    rw [hH.spectrum_eq_image_range]
    rintro ⟨_, ⟨_, rfl⟩, rfl⟩
    exact hz (by simp)
  have hunit : IsUnit (z • (1 : Matrix index index Complex) - H) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (spectrum.notMem_iff.mp hznot)
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit

theorem resolventQuadraticElement_neg_im_pos
    {index : Type*} [Fintype index] [DecidableEq index]
    (H : Matrix index index Complex) (hH : H.IsHermitian)
    (z : Complex) (hz : 0 < z.im)
    (u : index → Complex) (hu : u ≠ 0) :
    0 < -(resolventQuadraticElement H z u).im := by
  let M := complexHermitianResolventMatrix H z
  let w := M⁻¹ *ᵥ u
  have hM : IsUnit M.det :=
    complexHermitianResolventMatrix_det_isUnit H hH z hz.ne'
  have hMw : M *ᵥ w = u := by
    simp [w, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM]
  have hw : w ≠ 0 := by
    intro hwzero
    apply hu
    rw [← hMw, hwzero, Matrix.mulVec_zero]
  have hselfpos : 0 < star w ⬝ᵥ w :=
    Matrix.dotProduct_star_self_pos_iff.mpr hw
  have hselfre : 0 < (star w ⬝ᵥ w).re :=
    (Complex.pos_iff.mp hselfpos).1
  have hselfim : (star w ⬝ᵥ w).im = 0 :=
    (Complex.pos_iff.mp hselfpos).2.symm
  have hHermitianIm : (star w ⬝ᵥ (H *ᵥ w)).im = 0 :=
    hH.im_star_dotProduct_mulVec_self w
  have hquadratic :
      (star w ⬝ᵥ (M *ᵥ w)).im =
        z.im * (star w ⬝ᵥ w).re := by
    change (star w ⬝ᵥ
      ((z • (1 : Matrix index index Complex) - H) *ᵥ w)).im = _
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [Complex.sub_im, Complex.mul_im, hHermitianIm, hselfim]
    ring
  have hconjugate :
      star w ⬝ᵥ (M *ᵥ w) =
        star (resolventQuadraticElement H z u) := by
    rw [hMw]
    exact Matrix.star_dotProduct w u
  calc
    0 < z.im * (star w ⬝ᵥ w).re := mul_pos hz hselfre
    _ = (star w ⬝ᵥ (M *ᵥ w)).im := hquadratic.symm
    _ = -(resolventQuadraticElement H z u).im := by
      rw [hconjugate, Complex.star_def, Complex.conj_im]

theorem inv_im_pos_of_neg_im_pos {g : Complex} (hg : 0 < -g.im) :
    0 < g⁻¹.im := by
  rw [Complex.inv_im]
  exact div_pos hg (Complex.normSq_pos.mpr fun hzero => by
    rw [hzero] at hg
    simp at hg)

theorem isHermitian_map_ofReal
    {index : Type*}
    {A : Matrix index index Real} (hA : A.IsHermitian) :
    (A.map Complex.ofReal).IsHermitian := by
  exact hA.map Complex.ofReal (fun x => by simp)

theorem complexHermitianResolventMatrix_oneSiteAndersonMatrix
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (i : index)
    (z : Complex) (potential : Real) :
    complexHermitianResolventMatrix
        ((oneSiteAndersonMatrix background i potential).map Complex.ofReal) z =
      oneSiteAndersonShiftedMatrix
        (complexHermitianResolventMatrix (background.map Complex.ofReal) z)
        i potential := by
  ext p q
  simp only [complexHermitianResolventMatrix, oneSiteAndersonMatrix,
    oneSiteAndersonShiftedMatrix, realSiteVector, complexSiteVector,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.map_apply, Matrix.add_apply, Matrix.vecMulVec, smul_eq_mul]
  by_cases hp : p = i
  · subst p
    by_cases hq : q = i
    · subst q
      simp
      ring
    · simp [hq]
  · by_cases hq : q = i
    · subst q
      simp [hp]
    · simp [hp, hq]

theorem star_complexSiteVector
    {index : Type*} [DecidableEq index] (i : index) :
    star (complexSiteVector i) = complexSiteVector i := by
  funext p
  by_cases hp : p = i
  · subst p
    simp [complexSiteVector]
  · simp [complexSiteVector, hp]

theorem complexSiteVector_ne_zero
    {index : Type*} [DecidableEq index] (i : index) :
    complexSiteVector i ≠ 0 := by
  intro hzero
  have hi := congrFun hzero i
  simp [complexSiteVector] at hi

def finiteHermitianOneSiteGreen
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (i : index)
    (z : Complex) (potential : Real) : Complex :=
  oneSiteAndersonLocalGreen
    (complexHermitianResolventMatrix (background.map Complex.ofReal) z)
    i potential

theorem finiteHermitianOneSiteGreen_eq_resolventQuadraticElement
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (i : index)
    (z : Complex) (potential : Real) :
    finiteHermitianOneSiteGreen background i z potential =
      resolventQuadraticElement
        ((oneSiteAndersonMatrix background i potential).map Complex.ofReal)
        z (complexSiteVector i) := by
  unfold finiteHermitianOneSiteGreen oneSiteAndersonLocalGreen
    bilinearResolventElement resolventQuadraticElement
  rw [complexHermitianResolventMatrix_oneSiteAndersonMatrix]
  rw [star_complexSiteVector]

theorem finiteHermitianOneSiteShiftedMatrix_det_isUnit
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : z.im ≠ 0) (potential : Real) :
    IsUnit
      (oneSiteAndersonShiftedMatrix
        (complexHermitianResolventMatrix (background.map Complex.ofReal) z)
        i potential).det := by
  rw [← complexHermitianResolventMatrix_oneSiteAndersonMatrix]
  exact complexHermitianResolventMatrix_det_isUnit _
    (isHermitian_map_ofReal
      (oneSiteAndersonMatrix_isHermitian background hbackground i potential))
    z hz

theorem finiteHermitianOneSiteGreen_neg_im_pos
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im) (potential : Real) :
    0 < -(finiteHermitianOneSiteGreen background i z potential).im := by
  rw [finiteHermitianOneSiteGreen_eq_resolventQuadraticElement]
  exact resolventQuadraticElement_neg_im_pos _
    (isHermitian_map_ofReal
      (oneSiteAndersonMatrix_isHermitian background hbackground i potential))
    z hz (complexSiteVector i) (complexSiteVector_ne_zero i)

theorem finiteHermitianOneSiteGreen_ne_zero
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im) (potential : Real) :
    finiteHermitianOneSiteGreen background i z potential ≠ 0 := by
  intro hzero
  have hpos := finiteHermitianOneSiteGreen_neg_im_pos
    background hbackground i z hz potential
  rw [hzero] at hpos
  simp at hpos

def oneSiteEffectiveHerglotzParameter
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (i : index)
    (z : Complex) (reference : Real) : Complex :=
  (finiteHermitianOneSiteGreen background i z reference)⁻¹ +
    (reference : Complex)

theorem oneSiteEffectiveHerglotzParameter_im_pos
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im) (reference : Real) :
    0 < (oneSiteEffectiveHerglotzParameter background i z reference).im := by
  unfold oneSiteEffectiveHerglotzParameter
  simp only [Complex.add_im, Complex.ofReal_im, add_zero]
  exact inv_im_pos_of_neg_im_pos
    (finiteHermitianOneSiteGreen_neg_im_pos
      background hbackground i z hz reference)

theorem finiteHermitianOneSiteGreen_eq_inv_sub
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im)
    (reference potential : Real) :
    finiteHermitianOneSiteGreen background i z potential =
      (oneSiteEffectiveHerglotzParameter background i z reference -
        (potential : Complex))⁻¹ := by
  have hinv := oneSiteAndersonLocalGreen_inv_eq
    (complexHermitianResolventMatrix (background.map Complex.ofReal) z)
    i reference potential
    (finiteHermitianOneSiteShiftedMatrix_det_isUnit
      background hbackground i z hz.ne' reference)
    (finiteHermitianOneSiteShiftedMatrix_det_isUnit
      background hbackground i z hz.ne' potential)
    (finiteHermitianOneSiteGreen_ne_zero
      background hbackground i z hz reference)
  change (finiteHermitianOneSiteGreen background i z potential)⁻¹ =
    (finiteHermitianOneSiteGreen background i z reference)⁻¹ -
      ((potential - reference : Real) : Complex) at hinv
  calc
    finiteHermitianOneSiteGreen background i z potential =
        ((finiteHermitianOneSiteGreen background i z potential)⁻¹)⁻¹ :=
      (inv_inv _).symm
    _ = ((finiteHermitianOneSiteGreen background i z reference)⁻¹ -
        ((potential - reference : Real) : Complex))⁻¹ :=
      congrArg (fun q : Complex => q⁻¹) hinv
    _ = (oneSiteEffectiveHerglotzParameter background i z reference -
        (potential : Complex))⁻¹ := by
      congr 1
      unfold oneSiteEffectiveHerglotzParameter
      push_cast
      ring

end

end ArchonPhysics.FrozenAndersonOneSitePoissonAveraging

namespace ArchonPhysics.FrozenAndersonOneSitePoissonAveraging

open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open scoped BigOperators Matrix

noncomputable section

theorem bilinearResolventElement_complexSiteVector_eq_apply
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : Matrix index index Complex) (i : index) :
    bilinearResolventElement A (complexSiteVector i) (complexSiteVector i) =
      A⁻¹ i i := by
  simp [bilinearResolventElement, complexSiteVector, single_dotProduct]

theorem trace_nonsing_inv_eq_sum_bilinearResolventElement_complexSiteVector
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : Matrix index index Complex) :
    Matrix.trace A⁻¹ =
      ∑ i : index,
        bilinearResolventElement A (complexSiteVector i) (complexSiteVector i) := by
  simp [Matrix.trace, bilinearResolventElement_complexSiteVector_eq_apply]

end

end ArchonPhysics.FrozenAndersonOneSitePoissonAveraging

namespace ArchonPhysics.FrozenAndersonOneSitePoissonAveraging

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.FrozenAndersonDiagonalPotentialDensity
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open MeasureTheory
open scoped ENNReal Matrix

noncomputable section

theorem integral_finiteHermitianOneSiteGreen_neg_im_le_of_measure_le
    {index : Type*} [Fintype index] [DecidableEq index]
    {mu : Measure Real} {densityBound : ENNReal}
    (hdensityBound : densityBound ≠ ∞)
    (hmu : mu ≤ densityBound • (volume : Measure Real))
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im) (reference : Real) :
    ∫ potential : Real,
        -(finiteHermitianOneSiteGreen background i z potential).im ∂mu ≤
      densityBound.toReal * Real.pi := by
  simp_rw [finiteHermitianOneSiteGreen_eq_inv_sub
    background hbackground i z hz reference]
  exact integral_neg_im_inv_sub_real_le_of_measure_le
    hdensityBound hmu
    (oneSiteEffectiveHerglotzParameter background i z reference)
    (oneSiteEffectiveHerglotzParameter_im_pos
      background hbackground i z hz reference)

theorem integral_finiteHermitianOneSiteGreen_neg_im_andersonLaw_le
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im)
    (reference lambda : Real) (hlambda : lambda ≠ 0) :
    ∫ potential : Real,
        -(finiteHermitianOneSiteGreen background i z potential).im
          ∂andersonDiagonalPotentialLaw lambda ≤
      (5 / 2 : Real) * |lambda|⁻¹ * Real.pi := by
  have hbound := integral_finiteHermitianOneSiteGreen_neg_im_le_of_measure_le
    (densityBound :=
      (5 / 2 : ENNReal) * ENNReal.ofReal |lambda|⁻¹)
    (by finiteness)
    (andersonDiagonalPotentialLaw_le_fiveHalves_smul_volume hlambda)
    background hbackground i z hz reference
  simpa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg lambda))] using hbound

def finiteFrozenOneSiteGreen
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (i : index)
    (z : Complex) (lambda mass : Real) : Complex :=
  finiteHermitianOneSiteGreen background i z
    (andersonDiagonalPotential lambda mass)

theorem integral_finiteFrozenOneSiteGreen_neg_im_massCoordinateLaw_le
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im)
    (reference lambda : Real) (hlambda : lambda ≠ 0) :
    ∫ mass : Real,
        -(finiteFrozenOneSiteGreen background i z lambda mass).im
          ∂massCoordinateLaw ≤
      (5 / 2 : Real) * |lambda|⁻¹ * Real.pi := by
  let alpha := oneSiteEffectiveHerglotzParameter background i z reference
  have halpha : 0 < alpha.im :=
    oneSiteEffectiveHerglotzParameter_im_pos
      background hbackground i z hz reference
  calc
    ∫ mass : Real,
        -(finiteFrozenOneSiteGreen background i z lambda mass).im
          ∂massCoordinateLaw =
        ∫ mass : Real,
          realLinePoissonKernel alpha.re alpha.im
            (andersonDiagonalPotential lambda mass) ∂massCoordinateLaw := by
      apply integral_congr_ae
      filter_upwards [] with mass
      unfold finiteFrozenOneSiteGreen
      rw [finiteHermitianOneSiteGreen_eq_inv_sub
        background hbackground i z hz reference]
      exact neg_im_inv_sub_real_eq_realLinePoissonKernel alpha
        (andersonDiagonalPotential lambda mass)
    _ = ∫ potential : Real,
          realLinePoissonKernel alpha.re alpha.im potential
            ∂andersonDiagonalPotentialLaw lambda := by
      unfold andersonDiagonalPotentialLaw
      symm
      apply integral_map
      · exact (measurable_const.mul measurable_id).aemeasurable
      · exact (continuous_realLinePoissonKernel alpha.re alpha.im
          halpha.ne').measurable.aestronglyMeasurable
    _ ≤ (5 / 2 : Real) * |lambda|⁻¹ * Real.pi := by
      have hbound := integral_realLinePoissonKernel_le_of_measure_le
        (densityBound :=
          (5 / 2 : ENNReal) * ENNReal.ofReal |lambda|⁻¹)
        (by finiteness)
        (andersonDiagonalPotentialLaw_le_fiveHalves_smul_volume hlambda)
        alpha.re alpha.im halpha
      simpa [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg lambda))] using hbound

end

end ArchonPhysics.FrozenAndersonOneSitePoissonAveraging

namespace ArchonPhysics.FrozenAndersonOneSitePoissonAveraging

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open MeasureTheory
open scoped BigOperators Matrix

noncomputable section

theorem sum_integral_finiteFrozenOneSiteGreen_neg_im_massCoordinateLaw_le
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : index → Matrix index index Real)
    (hbackground : ∀ i, (background i).IsHermitian)
    (z : Complex) (hz : 0 < z.im)
    (reference : index → Real) (lambda : Real) (hlambda : lambda ≠ 0) :
    ∑ i : index, ∫ mass : Real,
        -(finiteFrozenOneSiteGreen (background i) i z lambda mass).im
          ∂massCoordinateLaw ≤
      (Fintype.card index : Real) *
        ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi) := by
  calc
    ∑ i : index, ∫ mass : Real,
        -(finiteFrozenOneSiteGreen (background i) i z lambda mass).im
          ∂massCoordinateLaw ≤
        ∑ _i : index, (5 / 2 : Real) * |lambda|⁻¹ * Real.pi := by
      apply Finset.sum_le_sum
      intro i _hi
      exact integral_finiteFrozenOneSiteGreen_neg_im_massCoordinateLaw_le
        (background i) (hbackground i) i z hz (reference i) lambda hlambda
    _ = (Fintype.card index : Real) *
        ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi) := by
      simp

end

end ArchonPhysics.FrozenAndersonOneSitePoissonAveraging

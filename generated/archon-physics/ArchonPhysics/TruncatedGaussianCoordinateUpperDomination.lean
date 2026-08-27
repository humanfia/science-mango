import ArchonPhysics.TruncatedGaussianFiniteDomination

/-!
# Reverse one-coordinate domination for a truncated Gaussian

On the frozen compact support, the Gaussian density also has a finite positive
maximum.  After retaining the conditioning normalization explicitly, this
gives the reverse quantitative comparison

`coordinateLaw parameters <= C * massCoordinateLaw`

for some finite positive `C`.  A separate finite-event module tensorizes this
one-site comparison and keeps the resulting `C ^ N` cost visible.
-/

namespace ArchonPhysics.TruncatedGaussianCoordinateUpperDomination

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TruncatedGaussianFiniteDomination
open ArchonPhysics.TruncatedGaussianMassLaw
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- The continuous Gaussian density has a strictly positive finite maximum on
the physical mass interval. -/
theorem exists_gaussianPDFReal_uniform_upper (parameters : Parameters) :
    ∃ upper : NNReal,
      0 < upper ∧
        ∀ mass ∈ massSupport,
          ProbabilityTheory.gaussianPDFReal
              parameters.mean parameters.variance mass <= (upper : Real) := by
  have hnonempty : massSupport.Nonempty := by
    refine ⟨1, ?_⟩
    norm_num [massSupport, massLower, massUpper]
  obtain ⟨point, hpoint, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn hnonempty
      (continuous_gaussianPDFReal parameters).continuousOn
  let upper : NNReal :=
    ⟨ProbabilityTheory.gaussianPDFReal
        parameters.mean parameters.variance point,
      (ProbabilityTheory.gaussianPDFReal_nonneg
        parameters.mean parameters.variance point)⟩
  refine ⟨upper, ?_, ?_⟩
  · exact ProbabilityTheory.gaussianPDFReal_pos
      parameters.mean parameters.variance point parameters.variance_ne_zero
  · intro mass hmass
    exact hmax hmass

/-- An upper bound for the real density yields an upper measure comparison on
the restricted support. -/
theorem restricted_gaussianReal_le_smul_restricted_volume
    (parameters : Parameters) (upper : NNReal)
    (hupper : ∀ mass ∈ massSupport,
      ProbabilityTheory.gaussianPDFReal
          parameters.mean parameters.variance mass <= (upper : Real)) :
    (ProbabilityTheory.gaussianReal
        parameters.mean parameters.variance).restrict massSupport <=
      (upper : ENNReal) • (volume : Measure Real).restrict massSupport := by
  have hpointwise :
      ProbabilityTheory.gaussianPDF parameters.mean parameters.variance ≤ᵐ[
        (volume : Measure Real).restrict massSupport]
        (fun _mass : Real => (upper : ENNReal)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with mass hmass
    rw [ProbabilityTheory.gaussianPDF]
    simpa only [ENNReal.coe_nnreal_eq] using
      ENNReal.ofReal_le_ofReal (hupper mass hmass)
  have h := withDensity_mono hpointwise
  rw [withDensity_const] at h
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero
    parameters.mean parameters.variance_ne_zero]
  rwa [restrict_withDensity
    (μ := (volume : Measure Real))
    (show MeasurableSet massSupport from measurableSet_Icc)
    (ProbabilityTheory.gaussianPDF parameters.mean parameters.variance)]

/-- Reverse normalized-law comparison.  The witness is exactly

`C = Gaussian(massSupport)⁻¹ * upper * (2 / 5)`.

It is strictly positive and finite. -/
theorem exists_coordinateLaw_le_smul_massCoordinateLaw
    (parameters : Parameters) :
    ∃ constant : ENNReal,
      0 < constant ∧ constant ≠ ∞ ∧
        coordinateLaw parameters <= constant • massCoordinateLaw := by
  obtain ⟨upper, hupperPositive, hupper⟩ :=
    exists_gaussianPDFReal_uniform_upper parameters
  let normalization : ENNReal :=
    ProbabilityTheory.gaussianReal
      parameters.mean parameters.variance massSupport
  let supportLength : ENNReal := 2 / 5
  let constant : ENNReal :=
    normalization⁻¹ * (upper : ENNReal) * supportLength
  have hnormalizationPositive : 0 < normalization := by
    exact gaussianReal_massSupport_pos parameters
  have hnormalizationFinite : normalization ≠ ∞ := by
    exact measure_ne_top _ _
  have hsupportLengthPositive : 0 < supportLength := by
    norm_num [supportLength]
  have hsupportLengthFinite : supportLength ≠ ∞ := by
    unfold supportLength
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hconstantPositive : 0 < constant := by
    unfold constant
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.inv_ne_zero.mpr hnormalizationFinite)
        (ENNReal.coe_pos.mpr hupperPositive).ne').ne'
      hsupportLengthPositive.ne'
  have hconstantFinite : constant ≠ ∞ := by
    unfold constant
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.inv_ne_top.mpr hnormalizationPositive.ne')
        ENNReal.coe_ne_top)
      hsupportLengthFinite
  have hrestricted :=
    restricted_gaussianReal_le_smul_restricted_volume
      parameters upper hupper
  have hscaled :
      normalization⁻¹ •
          (ProbabilityTheory.gaussianReal
            parameters.mean parameters.variance).restrict massSupport <=
        normalization⁻¹ •
          ((upper : ENNReal) •
            (volume : Measure Real).restrict massSupport) := by
    gcongr
  refine ⟨constant, hconstantPositive, hconstantFinite, ?_⟩
  have hvolume : (volume : Measure Real) massSupport = (2 / 5 : ENNReal) := by
    simp [massSupport, massLower, massUpper, Real.volume_Icc]
    norm_num [ENNReal.ofReal_div_of_pos]
  unfold coordinateLaw massCoordinateLaw ProbabilityTheory.cond
  change normalization⁻¹ •
      (ProbabilityTheory.gaussianReal
        parameters.mean parameters.variance).restrict massSupport <= _
  convert hscaled using 1
  simp only [constant, supportLength, hvolume, smul_smul]
  congr 1
  rw [mul_assoc, mul_assoc]
  have hlengthFinite : (2 / 5 : ENNReal) ≠ ∞ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  rw [ENNReal.mul_inv_cancel (by norm_num) hlengthFinite, mul_one]
/-- Any reverse domination constant between the two probability laws is at
least one.  Thus its tensor power never improves a probability estimate; when
it is strictly larger than one the finite-volume cost is genuinely
exponential. -/
theorem one_le_of_coordinateLaw_le_smul_massCoordinateLaw
    (parameters : Parameters) (constant : ENNReal)
    (hdomination : coordinateLaw parameters <=
      constant • massCoordinateLaw) :
    1 <= constant := by
  have huniv := Measure.le_iff'.1 hdomination Set.univ
  simpa [Measure.smul_apply, smul_eq_mul] using huniv

/-- A finite reverse RN witness, normalized to expose the unavoidable lower
bound `1 <= constant`. -/
theorem exists_finite_coordinateUpperConstant (parameters : Parameters) :
    ∃ constant : ENNReal, 1 <= constant ∧ constant ≠ ∞ ∧
      coordinateLaw parameters <= constant • massCoordinateLaw := by
  obtain ⟨constant, _hpositive, hfinite, hdomination⟩ :=
    exists_coordinateLaw_le_smul_massCoordinateLaw parameters
  exact ⟨constant,
    one_le_of_coordinateLaw_le_smul_massCoordinateLaw
      parameters constant hdomination,
    hfinite, hdomination⟩


end

end ArchonPhysics.TruncatedGaussianCoordinateUpperDomination

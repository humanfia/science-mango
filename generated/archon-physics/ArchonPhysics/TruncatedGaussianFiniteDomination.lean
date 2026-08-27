import ArchonPhysics.TruncatedGaussianMassLaw
import ArchonPhysics.ActualChildRepeatedExactResonanceKernelBridge

/-!
# Quantitative finite-dimensional domination for truncated-Gaussian masses

On the frozen compact mass interval, a nondegenerate Gaussian density has a
strictly positive uniform lower bound.  This file turns that elementary
compactness fact into quantitative domination of the normalized uniform mass
law by the conditioned Gaussian law, and then tensors the estimate in finite
dimension.

Only finite-dimensional laws occur below.  No comparison of infinite product
measures is asserted.
-/

namespace ArchonPhysics.TruncatedGaussianFiniteDomination

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

open RandomEnsemble TruncatedGaussianMassLaw
open TwoParameterSpectralAveragingAtlas
open ActualChildRepeatedExactResonanceKernelBridge
open ActualTwoMassChildRepeatedMismatchLowerBound
open ActualTwoMassSpectralChart

/-- The real Gaussian density is continuous in its mass argument. -/
theorem continuous_gaussianPDFReal (parameters : Parameters) :
    Continuous
      (ProbabilityTheory.gaussianPDFReal parameters.mean parameters.variance) := by
  unfold ProbabilityTheory.gaussianPDFReal
  fun_prop

/-- Compactness of the physical mass interval upgrades pointwise positivity of
the Gaussian density to a strictly positive uniform lower bound. -/
theorem exists_gaussianPDFReal_uniform_lower (parameters : Parameters) :
    ∃ density : NNReal,
      0 < density ∧
        ∀ mass ∈ massSupport,
          (density : Real) ≤
            ProbabilityTheory.gaussianPDFReal
              parameters.mean parameters.variance mass := by
  obtain ⟨density, hdensity, hlower⟩ :=
    isCompact_Icc.exists_forall_le'
      (continuous_gaussianPDFReal parameters).continuousOn
      (a := (0 : Real))
      (fun mass _hmass ↦ ProbabilityTheory.gaussianPDFReal_pos
        parameters.mean parameters.variance mass parameters.variance_ne_zero)
  exact ⟨⟨density, hdensity.le⟩, hdensity, hlower⟩

/-- A positive lower bound for the unconditioned Gaussian density dominates
the corresponding multiple of Lebesgue measure after both laws are restricted
to the mass interval. -/
theorem restricted_volume_smul_le_restricted_gaussianReal
    (parameters : Parameters) (density : NNReal)
    (hlower : ∀ mass ∈ massSupport,
      (density : Real) ≤
        ProbabilityTheory.gaussianPDFReal
          parameters.mean parameters.variance mass) :
    (density : ENNReal) • (volume : Measure Real).restrict massSupport ≤
      (ProbabilityTheory.gaussianReal parameters.mean parameters.variance).restrict
        massSupport := by
  have hpointwise :
      (fun _mass : Real ↦ (density : ENNReal)) ≤ᵐ[
        (volume : Measure Real).restrict massSupport]
        ProbabilityTheory.gaussianPDF parameters.mean parameters.variance := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with mass hmass
    rw [ProbabilityTheory.gaussianPDF]
    simpa only [ENNReal.coe_nnreal_eq] using
      ENNReal.ofReal_le_ofReal (hlower mass hmass)
  have h := withDensity_mono hpointwise
  rw [withDensity_const] at h
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero
    parameters.mean parameters.variance_ne_zero]
  rwa [restrict_withDensity
    (μ := (volume : Measure Real))
    (show MeasurableSet massSupport from measurableSet_Icc)
    (ProbabilityTheory.gaussianPDF parameters.mean parameters.variance)]

/-- One-dimensional quantitative adapter from the frozen normalized-uniform
mass law to a nondegenerate Gaussian conditioned on the same support.

The coefficient is existential because only positivity, rather than a sharp
closed form, is needed by the resonance small-ball bridge. -/
theorem exists_coordinateLaw_domination (parameters : Parameters) :
    ∃ density : NNReal,
      0 < density ∧
        (density : ENNReal) • massCoordinateLaw ≤ coordinateLaw parameters := by
  obtain ⟨lower, hlowerPositive, hlower⟩ :=
    exists_gaussianPDFReal_uniform_lower parameters
  let supportLength : NNReal := 2 / 5
  let density : NNReal := lower * supportLength
  have hsupportLength : 0 < supportLength := by
    norm_num [supportLength]
  have hdensity : 0 < density := mul_pos hlowerPositive hsupportLength
  have hrestricted :=
    restricted_volume_smul_le_restricted_gaussianReal parameters lower hlower
  have hvolume : (volume : Measure Real) massSupport = (2 / 5 : ENNReal) := by
    simp [massSupport, massLower, massUpper, Real.volume_Icc]
    norm_num [ENNReal.ofReal_div_of_pos]
  have huniform :
      (density : ENNReal) • massCoordinateLaw =
        (lower : ENNReal) • (volume : Measure Real).restrict massSupport := by
    unfold massCoordinateLaw ProbabilityTheory.cond
    rw [smul_smul, hvolume]
    congr 1
    change (((lower * (2 / 5 : NNReal) : NNReal) : ENNReal) *
      (2 / 5 : ENNReal)⁻¹) = (lower : ENNReal)
    rw [ENNReal.coe_mul]
    norm_num
    rw [mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by finiteness),
      mul_one]
  have hgaussianProbability :
      ProbabilityTheory.gaussianReal parameters.mean parameters.variance massSupport ≤ 1 := by
    calc
      ProbabilityTheory.gaussianReal parameters.mean parameters.variance massSupport ≤
          ProbabilityTheory.gaussianReal parameters.mean parameters.variance Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have hnormalization :
      (ProbabilityTheory.gaussianReal parameters.mean parameters.variance).restrict
          massSupport ≤
        coordinateLaw parameters := by
    unfold coordinateLaw ProbabilityTheory.cond
    have hone :
        (1 : ENNReal) ≤
          (ProbabilityTheory.gaussianReal parameters.mean parameters.variance
            massSupport)⁻¹ :=
      ENNReal.one_le_inv.mpr hgaussianProbability
    rw [Measure.le_iff']
    intro target
    simp only [Measure.smul_apply, smul_eq_mul]
    calc
      (ProbabilityTheory.gaussianReal parameters.mean parameters.variance).restrict
          massSupport target =
          1 * (ProbabilityTheory.gaussianReal parameters.mean parameters.variance).restrict
            massSupport target := (one_mul _).symm
      _ ≤ _ := mul_le_mul hone le_rfl (by positivity) (by positivity)
  exact ⟨density, hdensity, huniform.le.trans (hrestricted.trans hnormalization)⟩

/-- Pair-law adapter used directly by the two-mass reverse-coarea theorem. -/
theorem exists_iidMassPairLaw_domination (parameters : Parameters) :
    ∃ density : NNReal,
      0 < density ∧
        (density : ENNReal) • iidMassPairLaw ≤
          (coordinateLaw parameters).prod (coordinateLaw parameters) := by
  obtain ⟨oneDensity, honeDensity, hone⟩ :=
    exists_coordinateLaw_domination parameters
  refine ⟨oneDensity ^ 2, pow_pos honeDensity _, ?_⟩
  have hpair := Measure.prod_mono hone hone
  have hscale :
      ((oneDensity ^ 2 : NNReal) : ENNReal) • iidMassPairLaw =
        ((oneDensity : ENNReal) • massCoordinateLaw).prod
          ((oneDensity : ENNReal) • massCoordinateLaw) := by
    simp only [iidMassPairLaw, Measure.prod_smul_left, Measure.prod_smul_right,
      smul_smul, ENNReal.coe_pow]
    rw [pow_two, mul_comm]
  exact hscale.le.trans hpair

/-! ## Finite tensorization -/

/-- Coordinatewise quantitative domination tensorizes over every finite
product.  The coefficient is the corresponding finite power. -/
theorem finitePi_smul_le_finitePi_of_smul_le
    (source target : Measure Real) [SigmaFinite source] [SigmaFinite target]
    (density : ENNReal) (hone : density • source ≤ target) :
    ∀ N : Nat,
      density ^ N • Measure.pi (fun _ : Fin N ↦ source) ≤
        Measure.pi (fun _ : Fin N ↦ target)
  | 0 => by
      simp only [pow_zero, one_smul]
      rw [Measure.pi_of_empty (fun _ : Fin 0 ↦ source),
        Measure.pi_of_empty (fun _ : Fin 0 ↦ target)]
  | n + 1 => by
      let splitEquiv := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ Real) 0
      have hsourceSplit : MeasurePreserving splitEquiv
          (Measure.pi (fun _ : Fin (n + 1) ↦ source))
          (source.prod (Measure.pi (fun _ : Fin n ↦ source))) := by
        dsimp [splitEquiv]
        exact measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ source) 0
      have htargetSplit : MeasurePreserving splitEquiv
          (Measure.pi (fun _ : Fin (n + 1) ↦ target))
          (target.prod (Measure.pi (fun _ : Fin n ↦ target))) := by
        dsimp [splitEquiv]
        exact measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ target) 0
      have htail :=
        finitePi_smul_le_finitePi_of_smul_le source target density hone n
      have hproductRaw := Measure.prod_mono hone htail
      have hproduct :
          density ^ (n + 1) •
              (source.prod (Measure.pi (fun _ : Fin n ↦ source))) ≤
            target.prod (Measure.pi (fun _ : Fin n ↦ target)) := by
        convert hproductRaw using 1 ;
          simp [Measure.prod_smul_left, Measure.prod_smul_right,
            smul_smul, pow_succ, mul_comm]
      have hmapped := Measure.map_mono hproduct splitEquiv.symm.measurable
      rw [Measure.map_smul,
        (MeasurePreserving.symm splitEquiv hsourceSplit).map_eq,
        (MeasurePreserving.symm splitEquiv htargetSplit).map_eq] at hmapped
      exact hmapped

/-- Every finite iid uniform mass vector is quantitatively dominated by the
truncated-Gaussian iid vector. -/
theorem exists_finiteLaw_domination (parameters : Parameters) (N : Nat) :
    ∃ density : NNReal,
      0 < density ∧
        (density : ENNReal) • finiteMassLaw N ≤ finiteLaw parameters N := by
  obtain ⟨oneDensity, honeDensity, hone⟩ :=
    exists_coordinateLaw_domination parameters
  refine ⟨oneDensity ^ N, pow_pos honeDensity _, ?_⟩
  simpa [finiteMassLaw, finiteLaw, ENNReal.coe_pow] using
    (finitePi_smul_le_finitePi_of_smul_le
      massCoordinateLaw (coordinateLaw parameters)
      (oneDensity : ENNReal) hone N)

/-- The two-coordinate finite-vector specialization. -/
theorem exists_finiteLaw_two_domination (parameters : Parameters) :
    ∃ density : NNReal,
      0 < density ∧
        (density : ENNReal) • finiteMassLaw 2 ≤ finiteLaw parameters 2 :=
  exists_finiteLaw_domination parameters 2

/-- The six-coordinate finite-vector specialization used by the genuine iid
six-site resonance patch. -/
theorem exists_finiteLaw_six_domination (parameters : Parameters) :
    ∃ density : NNReal,
      0 < density ∧
        (density : ENNReal) • finiteMassLaw 6 ≤ finiteLaw parameters 6 :=
  exists_finiteLaw_domination parameters 6

/-! ## Direct two-mass small-ball consumer -/

/-- The conditioned Gaussian pair, bundled as a finite measure for the
reverse-coarea consumer. -/
def pairFiniteLaw (parameters : Parameters) :
    FiniteMeasure (Real × Real) :=
  ⟨(coordinateLaw parameters).prod (coordinateLaw parameters), by
    infer_instance⟩

@[simp]
theorem coe_pairFiniteLaw (parameters : Parameters) :
    ((pairFiniteLaw parameters : FiniteMeasure (Real × Real)) :
      Measure (Real × Real)) =
        (coordinateLaw parameters).prod (coordinateLaw parameters) :=
  rfl

/-- The exact two-mass patch linear small-ball lower bound, specialized to
truncated-Gaussian masses.  The only probabilistic input is the finite pair
domination proved above. -/
theorem exists_truncatedGaussian_linearSmallBallLower
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N}
    {parent child : Fin (Fintype.card (Lattice.Site N))}
    {pair : Real × Real}
    (data : ActualTwoMassChildRepeatedExactPatchData
      fixed site₁ site₂ parent child pair)
    {detUpper : Real} (hdetUpper : 0 < detUpper)
    (hdet : ∀ point ∈ data.patch,
      |(actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child point).det| ≤ detUpper)
    (parameters : Parameters) :
    ∃ constant : Real, 0 < constant ∧
      ∀ delta : Real, 0 < delta → delta ≤ data.radius →
        constant * delta ≤
          (Measure.map childRepeatedDecayMismatch
            (Measure.map
              (actualTwoMassChildFrequencyChart
                fixed site₁ site₂ parent child)
              (pairFiniteLaw parameters))
            (absoluteMismatchSublevel delta)).toReal := by
  obtain ⟨density, hdensity, hdomination⟩ :=
    exists_iidMassPairLaw_domination parameters
  exact data.exists_linearSmallBallLower_of_law
    hdetUpper hdet (pairFiniteLaw parameters) density hdensity
      (by simpa using hdomination)

end

end ArchonPhysics.TruncatedGaussianFiniteDomination

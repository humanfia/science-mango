import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Measure.Hausdorff
import ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart
import ArchonPhysics.FiniteMassPolynomialAvoidance
import ArchonPhysics.SelectedFirstPartialJacobianChart

/-!
# A quantitative full-eight-IID linear mismatch small ball

The five environment masses are retained in an augmented local chart and
the selected `(2,5,7)` masses are mapped to the two child frequencies and
their mismatch.  The preceding joint differentiability and certified
partial Jacobian give an invertible strict derivative of a square chart on
the original eight-mass vector space.  A local upper volume-distortion bound,
an explicit seven-dimensional transverse box, and the exact finite-product
uniform mass density then give a genuine `c * delta` lower bound under the
full eight-coordinate iid law.

No environment-stability or small-ball hypothesis occurs in the theorem.
Both are consequences of the strict inverse-function chart.  This remains a
fixed eight-site statement, not a volume-uniform theorem for a larger chain.
-/

open scoped Matrix Topology ENNReal

namespace ArchonPhysics.ActualEightSiteFullIIDLinearSmallBall

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualEightSiteFullJointSpectralDifferentiability
open ArchonPhysics.ParametricPartialJacobianAugmentedLocalChart
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.SelectedFirstPartialJacobianChart
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function MeasureTheory Set

noncomputable section

@[simp] theorem eightMassVector_eta (x : EightMassVector) :
    ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] = x := by
  funext i
  fin_cases i <;> rfl


/-- Conjugate the parameter-retaining augmented chart back to the original
eight raw-mass coordinates.  Coordinates `(2,5,7)` become respectively the
two child frequencies and mismatch; all other coordinates are retained. -/
def fullEightAugmentedSpectralChart (x : EightMassVector) : EightMassVector :=
  splitEightMass.symm
    ((splitEightMass x).1, actualEightSiteFullLiftedFrequencyChart x)

@[simp] theorem fullEightAugmentedSpectralChart_seven
    (x : EightMassVector) :
    fullEightAugmentedSpectralChart x 7 =
      actualEightSiteSelectedMismatch x := by
  rfl

/-- The parameter-retaining derivative, conjugated by coordinate
permutations, is a genuine continuous linear equivalence of the original
eight-dimensional mass space. -/
theorem exists_hasStrictFDerivAt_fullEightAugmentedSpectralChart
    {x : EightMassVector} {D :
      (EightMassEnvironment × MassTriple) →L[Real] MassTriple}
    (hD : HasStrictFDerivAt fullEightLiftedFamily D (splitEightMass x))
    (hpartial : (D ∘L ContinuousLinearMap.inr Real
      EightMassEnvironment MassTriple).IsInvertible) :
    ∃ e : EightMassVector ≃L[Real] EightMassVector,
      HasStrictFDerivAt fullEightAugmentedSpectralChart
        (e : EightMassVector →L[Real] EightMassVector) x := by
  obtain ⟨augmentedDerivative, haugmented, hinvertible⟩ :=
    exists_strictDerivative_isInvertible_selectedFirstAugmentedMap
      hD hpartial
  have hker : augmentedDerivative.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinvertible.injective
  have hrange : augmentedDerivative.range = ⊤ :=
    LinearMap.range_eq_top.mpr hinvertible.surjective
  let augmentedEquiv :
      (MassTriple × EightMassEnvironment) ≃L[Real]
        (MassTriple × EightMassEnvironment) :=
    ContinuousLinearEquiv.ofBijective augmentedDerivative hker hrange
  have haugmentedEquiv : HasStrictFDerivAt
      (selectedFirstAugmentedMap fullEightLiftedFamily)
      (augmentedEquiv : (MassTriple × EightMassEnvironment) →L[Real]
        (MassTriple × EightMassEnvironment))
      ((splitEightMass x).2, (splitEightMass x).1) := by
    rw [ContinuousLinearEquiv.coe_ofBijective augmentedDerivative hker hrange]
    exact haugmented
  let sourceEquiv : EightMassVector ≃L[Real]
      (MassTriple × EightMassEnvironment) :=
    splitEightMass.trans
      (ContinuousLinearEquiv.prodComm Real EightMassEnvironment MassTriple)
  let targetEquiv : (MassTriple × EightMassEnvironment) ≃L[Real]
      EightMassVector :=
    (ContinuousLinearEquiv.prodComm Real MassTriple EightMassEnvironment).trans
      splitEightMass.symm
  let e : EightMassVector ≃L[Real] EightMassVector :=
    (sourceEquiv.trans augmentedEquiv).trans targetEquiv
  have hinput := haugmentedEquiv.comp x sourceEquiv.hasStrictFDerivAt
  have houtput := targetEquiv.hasStrictFDerivAt.comp x hinput
  refine ⟨e, ?_⟩
  simpa [fullEightAugmentedSpectralChart, fullEightLiftedFamily,
    selectedFirstAugmentedMap, sourceEquiv, targetEquiv, e,
    Function.comp_def, eightMassVector_eta] using houtput

/-- An explicit target box: seven transverse coordinates have fixed positive
width, while coordinate `7` is the shrinking mismatch interval. -/
def fullEightAugmentedTargetBox
    (center : EightMassVector) (halfWidth delta : Real) :
    Set EightMassVector :=
  Set.univ.pi fun i =>
    if i = 7 then Ioo (-delta) delta
    else Ioo (center i - halfWidth) (center i + halfWidth)

theorem volume_fullEightAugmentedTargetBox
    {center : EightMassVector} {halfWidth delta : Real}
    (hhalf : 0 ≤ halfWidth) (hdelta : 0 ≤ delta) :
    (volume : Measure EightMassVector)
        (fullEightAugmentedTargetBox center halfWidth delta) =
      ENNReal.ofReal (2 * halfWidth) ^ 7 *
        ENNReal.ofReal (2 * delta) := by
  unfold fullEightAugmentedTargetBox
  rw [show (Set.univ.pi fun i =>
        if i = 7 then Ioo (-delta) delta
        else Ioo (center i - halfWidth) (center i + halfWidth)) =
      Set.univ.pi fun i =>
        Ioo (if i = 7 then -delta else center i - halfWidth)
          (if i = 7 then delta else center i + halfWidth) by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      by_cases h7 : i = 7 <;> simpa [h7] using h i
    · intro h i
      by_cases h7 : i = 7 <;> simpa [h7] using h i]
  rw [Real.volume_pi_Ioo]
  simp only [ite_sub, ite_add]
  have hnonneg : 0 ≤ 2 * halfWidth := mul_nonneg (by norm_num) hhalf
  have hdnonneg : 0 ≤ 2 * delta := mul_nonneg (by norm_num) hdelta
  simp (config := { decide := true })
    [Fin.prod_univ_succ, sub_neg_eq_add, hnonneg, hdnonneg]
  simp_rw [ENNReal.ofReal_add hhalf hhalf,
    ENNReal.ofReal_add hdelta hdelta]
  ring

theorem fullEightAugmentedTargetBox_subset_ball
    {center : EightMassVector} {outer halfWidth delta : Real}
    (houter : 0 < outer) (hhalf : halfWidth < outer)
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ halfWidth)
    (hcenter : center 7 = 0) :
    fullEightAugmentedTargetBox center halfWidth delta ⊆
      Metric.ball center outer := by
  intro y hy
  rw [Metric.mem_ball, dist_pi_lt_iff houter]
  intro i
  have hi := hy i (by simp)
  by_cases h7 : i = 7
  · subst i
    simp only [fullEightAugmentedTargetBox, if_pos, mem_Ioo] at hi
    rw [Real.dist_eq, hcenter]
    have : |y 7| < outer := by
      rw [abs_lt]
      constructor <;> linarith [hi.1, hi.2]
    simpa using this
  · simp only [fullEightAugmentedTargetBox, if_neg h7, mem_Ioo] at hi
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hi.1, hi.2]

/-- Closed support cube of the full eight-coordinate iid law. -/
def fullEightMassSupportCube : Set EightMassVector :=
  Set.univ.pi fun _ => massSupport

theorem measurableSet_fullEightMassSupportCube :
    MeasurableSet fullEightMassSupportCube :=
  MeasurableSet.univ_pi fun _ => by
    simpa [massSupport] using (measurableSet_Icc : MeasurableSet (Icc massLower massUpper))

/-- Exact normalized-volume formula for the eightfold iid mass law. -/
theorem finiteMassLaw_eight_eq_smul_restrict_volume :
    finiteMassLaw 8 =
      ((volume : Measure Real) massSupport)⁻¹ ^ 8 •
        (volume : Measure EightMassVector).restrict
          fullEightMassSupportCube := by
  unfold finiteMassLaw
  apply Measure.pi_eq
  intro sets hsets
  rw [Measure.smul_apply, Measure.restrict_apply]
  · rw [show Set.univ.pi sets ∩ fullEightMassSupportCube =
        Set.univ.pi (fun i => sets i ∩ massSupport) by
      unfold fullEightMassSupportCube
      ext x
      constructor
      · rintro ⟨hxsets, hxsupport⟩ i hi
        exact ⟨hxsets i hi, hxsupport i hi⟩
      · intro h
        exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩]
    rw [MeasureTheory.volume_pi_pi]
    simp_rw [show massCoordinateLaw =
        ((volume : Measure Real) massSupport)⁻¹ •
          (volume : Measure Real).restrict massSupport by rfl,
      Measure.smul_apply, Measure.restrict_apply (hsets _)]
    simp only [smul_eq_mul]
    rw [Finset.prod_mul_distrib]
    simp
  · exact MeasurableSet.univ_pi hsets

/-- Since the one-coordinate normalization density is greater than one,
the full iid law dominates ordinary volume restricted to its support cube. -/
theorem volume_restrict_fullEightMassSupportCube_le_finiteMassLaw :
    (volume : Measure EightMassVector).restrict
        fullEightMassSupportCube ≤ finiteMassLaw 8 := by
  rw [finiteMassLaw_eight_eq_smul_restrict_volume, Measure.le_iff']
  intro s
  rw [Measure.smul_apply]
  have hone : 1 ≤ ((volume : Measure Real) massSupport)⁻¹ := by
    simp [massSupport, massLower, massUpper, Real.volume_Icc]
    norm_num
  have hpow : 1 ≤ ((volume : Measure Real) massSupport)⁻¹ ^ 8 :=
    one_le_pow₀ hone
  calc
    (volume : Measure EightMassVector).restrict
        fullEightMassSupportCube s = 1 *
          (volume : Measure EightMassVector).restrict
            fullEightMassSupportCube s := by rw [one_mul]
    _ ≤ ((volume : Measure Real) massSupport)⁻¹ ^ 8 *
          (volume : Measure EightMassVector).restrict
            fullEightMassSupportCube s := by gcongr

/-- A true quantitative full-eight iid lower small-ball bound at the
certified all-distinct decay resonance.  `constant` is a positive finite
`ENNReal`, so the conclusion is exactly linear in the mismatch width. -/
theorem exists_actualEightSite_fullIID_exactAllDistinct_linearSmallBallLower :
    ∃ constant : ENNReal, constant ≠ 0 ∧ constant ≠ ∞ ∧
      ∃ radius : Real, 0 < radius ∧
        ∀ delta : Real, 0 < delta → delta ≤ radius →
          constant * ENNReal.ofReal delta ≤
            finiteMassLaw 8
              {x | |actualEightSiteSelectedMismatch x| ≤ delta} := by
  obtain ⟨t, _ht, D, hxSupport, hxResonance, hD, hpartial⟩ :=
    exists_fullEightLiftedFamily_strictDerivative_partial_isInvertible
  let x := actualEightSiteRationalMassPath t
  obtain ⟨e, hstrict⟩ :=
    exists_hasStrictFDerivAt_fullEightAugmentedSpectralChart hD hpartial
  let chart := fullEightAugmentedSpectralChart
  have hstrictChart : HasStrictFDerivAt chart
      (e : EightMassVector →L[Real] EightMassVector) x := by
    simpa [chart, x] using hstrict
  let center := chart x
  have hcenterMismatch : center 7 = 0 := by
    simpa [center, chart] using hxResonance
  let detValue : Real :=
    |(e : EightMassVector →L[Real] EightMassVector).det|
  let detCeiling : NNReal := ⟨detValue + 1, by
    dsimp [detValue]
    positivity⟩
  have hdetCeiling : ENNReal.ofReal detValue <
      (detCeiling : ENNReal) := by
    rw [ENNReal.ofReal_lt_coe_iff (by dsimp [detValue]; positivity)]
    change detValue < detValue + 1
    linarith
  have hdistEventually :=
    addHaar_image_le_mul_of_det_lt
      (μ := (volume : Measure EightMassVector))
      (e : EightMassVector →L[Real] EightMassVector) hdetCeiling
  obtain ⟨approximationError, hdistortion, herrorPos⟩ :=
    (hdistEventually.and self_mem_nhdsWithin).exists
  obtain ⟨approxSet, happroxNhds, happrox⟩ :=
    hstrictChart.approximates_deriv_on_nhds (Or.inr herrorPos)
  obtain ⟨regular, hregularSubset, hregularOpen, hxRegular⟩ :=
    mem_nhds_iff.mp happroxNhds
  let localChart := hstrictChart.toOpenPartialHomeomorph chart
  let patch : Set EightMassVector :=
    localChart.source ∩ regular ∩ fullEightMassSupportInterior
  have hpatchOpen : IsOpen patch :=
    (localChart.open_source.inter hregularOpen).inter
      isOpen_fullEightMassSupportInterior
  have hxPatch : x ∈ patch := by
    exact ⟨⟨hstrictChart.mem_toOpenPartialHomeomorph_source, hxRegular⟩,
      hxSupport⟩
  have hpatchSource : patch ⊆ localChart.source := by
    intro y hy
    exact hy.1.1
  have hpatchApprox : patch ⊆ approxSet := by
    intro y hy
    exact hregularSubset hy.1.2
  have hpatchSupport : patch ⊆ fullEightMassSupportInterior := by
    intro y hy
    exact hy.2
  have hpatchInjective : InjOn chart patch := by
    rw [← hstrictChart.toOpenPartialHomeomorph_coe]
    exact localChart.injOn.mono hpatchSource
  have hpatchImageOpen : IsOpen (chart '' patch) := by
    rw [← hstrictChart.toOpenPartialHomeomorph_coe]
    exact localChart.isOpen_image_of_subset_source hpatchOpen hpatchSource
  have hcenterImage : center ∈ chart '' patch := ⟨x, hxPatch, rfl⟩
  obtain ⟨outerRadius, houterRadius, hballSubset⟩ :=
    Metric.mem_nhds_iff.mp (hpatchImageOpen.mem_nhds hcenterImage)
  let radius : Real := outerRadius / 2
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  let transverse : ENNReal := ENNReal.ofReal (2 * radius) ^ 7
  let constant : ENNReal :=
    (detCeiling : ENNReal)⁻¹ * transverse * ENNReal.ofReal 2
  have hdetCeilingZero : (detCeiling : ENNReal) ≠ 0 := by
    have hnonnegDet : (0 : ENNReal) ≤ ENNReal.ofReal detValue := bot_le
    exact ne_of_gt (hnonnegDet.trans_lt hdetCeiling)
  have hdetCeilingTop : (detCeiling : ENNReal) ≠ ∞ := by finiteness
  have htransverseZero : transverse ≠ 0 := by
    dsimp [transverse]
    have htwoRadius : 0 < 2 * radius := by linarith
    exact pow_ne_zero 7 (ne_of_gt (ENNReal.ofReal_pos.mpr htwoRadius))
  have hconstantZero : constant ≠ 0 := by
    dsimp [constant]
    exact mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hdetCeilingTop)
      htransverseZero) (by norm_num)
  have hconstantTop : constant ≠ ∞ := by
    dsimp [constant, transverse]
    finiteness
  refine ⟨constant, hconstantZero, hconstantTop, radius, hradius, ?_⟩
  intro delta hdelta hdeltaRadius
  let target := fullEightAugmentedTargetBox center radius delta
  let source : Set EightMassVector := patch ∩ chart ⁻¹' target
  have htargetSubset : target ⊆ chart '' patch := by
    have hboxBall : target ⊆ Metric.ball center outerRadius := by
      apply fullEightAugmentedTargetBox_subset_ball houterRadius
      · dsimp [radius]
        linarith
      · exact hdelta.le
      · exact hdeltaRadius
      · exact hcenterMismatch
    exact hboxBall.trans hballSubset
  have himageSource : chart '' source = target := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzPatch, hzTarget⟩, rfl⟩
      exact hzTarget
    · intro hy
      obtain ⟨z, hzPatch, hzChart⟩ := htargetSubset hy
      have hzTarget : chart z ∈ target := hzChart.symm ▸ hy
      exact ⟨z, ⟨hzPatch, hzTarget⟩, hzChart⟩
  have hsourceApprox : source ⊆ approxSet := by
    intro y hy
    exact hpatchApprox hy.1
  have hvolumeDistortion :
      (volume : Measure EightMassVector) target ≤
        (detCeiling : ENNReal) *
          (volume : Measure EightMassVector) source := by
    rw [← himageSource]
    exact hdistortion source chart (happrox.mono_set hsourceApprox)
  have hsourceCube : source ⊆ fullEightMassSupportCube := by
    intro y hy
    intro i _hi
    exact ⟨(hpatchSupport hy.1 i).1.le,
      (hpatchSupport hy.1 i).2.le⟩
  have hsourceVolumeLeLaw :
      (volume : Measure EightMassVector) source ≤ finiteMassLaw 8 source := by
    calc
      (volume : Measure EightMassVector) source =
          (volume : Measure EightMassVector).restrict
            fullEightMassSupportCube source := by
        rw [Measure.restrict_apply₀'
          (t := source)
          measurableSet_fullEightMassSupportCube.nullMeasurableSet]
        exact congrArg (fun s : Set EightMassVector =>
          (volume : Measure EightMassVector) s)
            (inter_eq_left.2 hsourceCube).symm
      _ ≤ finiteMassLaw 8 source :=
        volume_restrict_fullEightMassSupportCube_le_finiteMassLaw source
  have hsourceEvent : source ⊆
      {y | |actualEightSiteSelectedMismatch y| ≤ delta} := by
    intro y hy
    have hout := hy.2 (7 : Fin 8) (by simp)
    simp only [target, fullEightAugmentedTargetBox, if_pos, mem_Ioo] at hout
    change -delta < fullEightAugmentedSpectralChart y 7 ∧
      fullEightAugmentedSpectralChart y 7 < delta at hout
    rw [fullEightAugmentedSpectralChart_seven] at hout
    change |actualEightSiteSelectedMismatch y| ≤ delta
    rw [abs_le]
    exact ⟨hout.1.le, hout.2.le⟩
  have hvolumeToEvent :
      (volume : Measure EightMassVector) source ≤
        finiteMassLaw 8
          {y | |actualEightSiteSelectedMismatch y| ≤ delta} :=
    hsourceVolumeLeLaw.trans (measure_mono hsourceEvent)
  have htargetToEvent :
      (volume : Measure EightMassVector) target ≤
        (detCeiling : ENNReal) * finiteMassLaw 8
          {y | |actualEightSiteSelectedMismatch y| ≤ delta} :=
    hvolumeDistortion.trans (by
      gcongr)
  have htargetVolume :
      (volume : Measure EightMassVector) target =
        transverse * (ENNReal.ofReal 2 * ENNReal.ofReal delta) := by
    rw [volume_fullEightAugmentedTargetBox hradius.le hdelta.le]
    dsimp [target, transverse]
    simp only [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
  have hinv : (detCeiling : ENNReal)⁻¹ *
      (volume : Measure EightMassVector) target ≤
        (detCeiling : ENNReal)⁻¹ *
          ((detCeiling : ENNReal) * finiteMassLaw 8
            {y | |actualEightSiteSelectedMismatch y| ≤ delta}) := by
    gcongr
  calc
    constant * ENNReal.ofReal delta =
        (detCeiling : ENNReal)⁻¹ *
          (volume : Measure EightMassVector) target := by
      rw [htargetVolume]
      dsimp [constant]
      ring
    _ ≤ (detCeiling : ENNReal)⁻¹ *
        ((detCeiling : ENNReal) * finiteMassLaw 8
          {y | |actualEightSiteSelectedMismatch y| ≤ delta}) := hinv
    _ = finiteMassLaw 8
        {y | |actualEightSiteSelectedMismatch y| ≤ delta} := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hdetCeilingZero hdetCeilingTop,
        one_mul]

end

end ArchonPhysics.ActualEightSiteFullIIDLinearSmallBall

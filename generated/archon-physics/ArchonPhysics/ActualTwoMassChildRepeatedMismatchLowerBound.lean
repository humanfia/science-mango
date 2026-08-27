import ArchonPhysics.ActualTwoMassSpectralChart
import ArchonPhysics.QuantitativeJacobianReversePushforward

/-!
# Reverse coarea for the actual two-mass child-repeated chart

This is the lower-bound counterpart of the existing two-mass atlas upper
estimates.  On an injective differentiable patch, an *upper* bound for the
true frequency Jacobian transports planar target volume into a lower bound
for the iid two-mass frequency law.

For child-repeated decay, the exact linear equivalence
`(parent, child) ↦ (child, parent - 2 * child)` preserves planar Lebesgue
measure.  Consequently, a resonance-centred product rectangle in the chart
image gives a genuine `c * delta` lower bound for the scalar mismatch law.
No quenched block-additivity premise is used here.
-/

namespace ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.QuantitativeJacobianReversePushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Scalar child-repeated decay mismatch. -/
def childRepeatedDecayMismatch (frequency : Real × Real) : Real :=
  frequency.1 - 2 * frequency.2

theorem measurable_childRepeatedDecayMismatch :
    Measurable childRepeatedDecayMismatch := by
  unfold childRepeatedDecayMismatch
  fun_prop

/-- Symmetric closed scalar mismatch window. -/
def absoluteMismatchSublevel (delta : Real) : Set Real :=
  {mismatch | |mismatch| ≤ delta}

theorem measurableSet_absoluteMismatchSublevel (delta : Real) :
    MeasurableSet (absoluteMismatchSublevel delta) := by
  exact (isClosed_le continuous_abs continuous_const).measurableSet

theorem volume_absoluteMismatchSublevel (delta : Real) :
    (volume : Measure Real) (absoluteMismatchSublevel delta) =
      ENNReal.ofReal (2 * delta) := by
  rw [show absoluteMismatchSublevel delta = Set.Icc (-delta) delta by
    ext x
    simp [absoluteMismatchSublevel, abs_le]]
  rw [Real.volume_Icc]
  congr 1
  ring

/-- Exact child-frequency and mismatch coordinates. -/
def childFrequencyMismatchLinearEquiv :
    (Real × Real) ≃ₗ[Real] (Real × Real) where
  toFun frequency := (frequency.2, frequency.1 - 2 * frequency.2)
  invFun joint := (joint.2 + 2 * joint.1, joint.1)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  left_inv x := by
    apply Prod.ext
    · dsimp
      ring
    · rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · dsimp
      ring

theorem continuous_childFrequencyMismatchLinearEquiv :
    Continuous childFrequencyMismatchLinearEquiv := by
  change Continuous fun frequency : Real × Real =>
    (frequency.2, frequency.1 - 2 * frequency.2)
  fun_prop

theorem toMatrix_childFrequencyMismatchLinearEquiv :
    LinearMap.toMatrix (Module.Basis.finTwoProd Real)
      (Module.Basis.finTwoProd Real)
      (childFrequencyMismatchLinearEquiv :
        (Real × Real) →ₗ[Real] (Real × Real)) =
      !![(0 : Real), 1; 1, -2] := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [childFrequencyMismatchLinearEquiv]

theorem det_childFrequencyMismatchLinearEquiv :
    LinearMap.det (childFrequencyMismatchLinearEquiv :
      (Real × Real) →ₗ[Real] (Real × Real)) = -1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd Real)
    (childFrequencyMismatchLinearEquiv :
      (Real × Real) →ₗ[Real] (Real × Real))]
  rw [toMatrix_childFrequencyMismatchLinearEquiv]
  norm_num [Matrix.det_fin_two]

/-- This coordinate change preserves planar Lebesgue measure. -/
theorem map_childFrequencyMismatchLinearEquiv_volume :
    Measure.map
        (childFrequencyMismatchLinearEquiv :
          (Real × Real) → (Real × Real))
        (volume : Measure (Real × Real)) =
      (volume : Measure (Real × Real)) := by
  change Measure.map
      (childFrequencyMismatchLinearEquiv :
        (Real × Real) →ₗ[Real] (Real × Real)) volume = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Real × Real)) (by
      rw [det_childFrequencyMismatchLinearEquiv]
      norm_num)]
  rw [det_childFrequencyMismatchLinearEquiv]
  norm_num

/-- Normalized uniform mass sampling dominates Lebesgue measure on the frozen support. -/
theorem volume_restrict_massSupport_le_massCoordinateLaw :
    (volume : Measure Real).restrict massSupport ≤ massCoordinateLaw := by
  unfold massCoordinateLaw ProbabilityTheory.cond
  have hnormalization :
      1 ≤ ((volume : Measure Real) massSupport)⁻¹ := by
    simp [massSupport, massLower, massUpper, Real.volume_Icc]
    norm_num
  rw [Measure.le_iff']
  intro target
  rw [Measure.smul_apply]
  simpa only [one_mul, smul_eq_mul] using
    (mul_le_mul_left hnormalization
      ((volume : Measure Real).restrict massSupport target))

/-- The iid two-mass law quantitatively dominates planar Lebesgue measure on
its support square. -/
theorem volume_restrict_iidMassPairSupport_le_iidMassPairLaw :
    (volume : Measure (Real × Real)).restrict iidMassPairSupport ≤
      iidMassPairLaw := by
  have hone := volume_restrict_massSupport_le_massCoordinateLaw
  have hpair := Measure.prod_mono hone hone
  simpa [iidMassPairSupport, iidMassPairLaw, Measure.volume_eq_prod,
    Measure.prod_restrict] using hpair

/-- Reverse area formula for one measurable target contained in the image of
an actual injective two-frequency patch. -/
theorem targetVolume_le_actualTwoMassFrequencyPair
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    {patch : Set (Real × Real)} (hpatch : MeasurableSet patch)
    (hpatchSupport : patch ⊆ iidMassPairSupport)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ parent child)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child point) patch point)
    (hinjective : InjOn
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child) patch)
    (detUpper : Real)
    (hdet : ∀ point ∈ patch,
      |(actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child point).det| ≤ detUpper)
    {target : Set (Real × Real)} (htarget : MeasurableSet target)
    (htargetImage : target ⊆
      actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child '' patch) :
    (volume : Measure (Real × Real)) target ≤
      ENNReal.ofReal detUpper *
        Measure.map
          (actualTwoMassChildFrequencyChart
            fixed site₁ site₂ parent child) iidMassPairLaw target := by
  let chart := actualTwoMassChildFrequencyChart
    fixed site₁ site₂ parent child
  have hsource :
      (1 : ENNReal) • (volume : Measure (Real × Real)).restrict patch ≤
        iidMassPairLaw := by
    have h := Measure.restrict_mono_measure
      volume_restrict_iidMassPairSupport_le_iidMassPairLaw patch
    rw [Measure.restrict_restrict_of_subset hpatchSupport] at h
    simpa using h.trans Measure.restrict_le_self
  have hreverse :=
    sourceDensity_smul_volume_restrict_image_le_detUpper_smul_map
      (volume : Measure (Real × Real)) hpatch chart
      (continuous_actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child).measurable
      (fun point => actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child point)
      hderivative hinjective detUpper hdet iidMassPairLaw 1 hsource
  have happly := hreverse target
  rw [Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply htarget] at happly
  have hinter : target ∩ chart '' patch = target :=
    inter_eq_left.mpr htargetImage
  simpa only [one_mul, smul_eq_mul, hinter] using happly

/-- A product rectangle in the exact `(child frequency, mismatch)`
coordinates yields a positive linear scalar small-ball lower bound.  The
coefficient is explicit: twice the child-interval length divided by the
Jacobian upper bound. -/
theorem exists_positive_actualTwoMass_childRepeated_linearSmallBallLower
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    {patch : Set (Real × Real)} (hpatch : MeasurableSet patch)
    (hpatchSupport : patch ⊆ iidMassPairSupport)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ parent child)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child point) patch point)
    (hinjective : InjOn
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child) patch)
    {detUpper : Real} (hdetUpper : 0 < detUpper)
    (hdet : ∀ point ∈ patch,
      |(actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child point).det| ≤ detUpper)
    {childSet : Set Real} (hchild : MeasurableSet childSet)
    (hchildPos : 0 < (volume : Measure Real) childSet)
    (hchildFinite : (volume : Measure Real) childSet ≠ ∞)
    {radius : Real} (_hradius : 0 < radius)
    (hrectangle : childSet ×ˢ absoluteMismatchSublevel radius ⊆
      childFrequencyMismatchLinearEquiv ''
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ parent child '' patch)) :
    ∃ constant : Real, 0 < constant ∧
      ∀ delta : Real, 0 < delta → delta ≤ radius →
        constant * delta ≤
          (Measure.map childRepeatedDecayMismatch
            (Measure.map
              (actualTwoMassChildFrequencyChart
                fixed site₁ site₂ parent child) iidMassPairLaw)
            (absoluteMismatchSublevel delta)).toReal := by
  let coordinateEquiv :=
    childFrequencyMismatchLinearEquiv
  let chart := actualTwoMassChildFrequencyChart
    fixed site₁ site₂ parent child
  let childVolume : Real := (volume : Measure Real).real childSet
  let constant : Real := 2 * childVolume / detUpper
  have hchildVolumePos : 0 < childVolume := by
    dsimp [childVolume, Measure.real]
    exact ENNReal.toReal_pos hchildPos.ne' hchildFinite
  have hconstant : 0 < constant := by
    dsimp [constant]
    positivity
  refine ⟨constant, hconstant, ?_⟩
  intro delta hdelta hdeltaRadius
  let rectangle : Set (Real × Real) :=
    childSet ×ˢ absoluteMismatchSublevel delta
  let frequencyTarget : Set (Real × Real) :=
    coordinateEquiv ⁻¹' rectangle
  have hcoordinateMeasurable : Measurable coordinateEquiv :=
    continuous_childFrequencyMismatchLinearEquiv.measurable
  have hrectangleMeasurable : MeasurableSet rectangle :=
    hchild.prod (measurableSet_absoluteMismatchSublevel delta)
  have hfrequencyTargetMeasurable : MeasurableSet frequencyTarget :=
    hrectangleMeasurable.preimage hcoordinateMeasurable
  have hwindowSubset :
      absoluteMismatchSublevel delta ⊆
        absoluteMismatchSublevel radius := by
    intro mismatch hmismatch
    exact le_trans hmismatch hdeltaRadius
  have hfrequencyTargetImage : frequencyTarget ⊆ chart '' patch := by
    intro frequency hfrequency
    have hlargeRectangle : coordinateEquiv frequency ∈
        childSet ×ˢ absoluteMismatchSublevel radius :=
      ⟨hfrequency.1, hwindowSubset hfrequency.2⟩
    obtain ⟨imageFrequency, himageFrequency, heq⟩ :=
      hrectangle hlargeRectangle
    have hsame : frequency = imageFrequency :=
      coordinateEquiv.injective heq.symm
    simpa [hsame] using himageFrequency
  have htargetBound := targetVolume_le_actualTwoMassFrequencyPair
    fixed site₁ site₂ parent child hpatch hpatchSupport hderivative
      hinjective detUpper hdet hfrequencyTargetMeasurable
      hfrequencyTargetImage
  have hmapVolume :
      Measure.map coordinateEquiv (volume : Measure (Real × Real)) =
        (volume : Measure (Real × Real)) := by
    simpa [coordinateEquiv, Measure.volume_eq_prod] using
      map_childFrequencyMismatchLinearEquiv_volume
  have hfrequencyTargetVolume :
      (volume : Measure (Real × Real)) frequencyTarget =
        (volume : Measure Real) childSet *
          ENNReal.ofReal (2 * delta) := by
    calc
      (volume : Measure (Real × Real)) frequencyTarget =
          Measure.map coordinateEquiv
            (volume : Measure (Real × Real)) rectangle := by
        rw [Measure.map_apply hcoordinateMeasurable hrectangleMeasurable]
      _ = (volume : Measure (Real × Real)) rectangle := by
        rw [hmapVolume]
      _ = (volume : Measure Real) childSet *
          (volume : Measure Real) (absoluteMismatchSublevel delta) := by
        change ((volume : Measure Real).prod (volume : Measure Real))
            rectangle = _
        rw [Measure.prod_prod]
      _ = _ := by
        rw [
          volume_absoluteMismatchSublevel]
  have hfrequencyTargetSubsetMismatch :
      frequencyTarget ⊆
        childRepeatedDecayMismatch ⁻¹'
          absoluteMismatchSublevel delta := by
    intro frequency hfrequency
    have hmismatch := hfrequency.2
    change childRepeatedDecayMismatch frequency ∈
      absoluteMismatchSublevel delta
    simpa [coordinateEquiv,
      childFrequencyMismatchLinearEquiv, childRepeatedDecayMismatch] using hmismatch
  have hmismatchMono :
      Measure.map chart iidMassPairLaw frequencyTarget ≤
        Measure.map childRepeatedDecayMismatch
          (Measure.map chart iidMassPairLaw)
          (absoluteMismatchSublevel delta) := by
    rw [Measure.map_apply measurable_childRepeatedDecayMismatch
      (measurableSet_absoluteMismatchSublevel delta)]
    exact measure_mono hfrequencyTargetSubsetMismatch
  rw [hfrequencyTargetVolume] at htargetBound
  have hENN :
      (volume : Measure Real) childSet * ENNReal.ofReal (2 * delta) ≤
        ENNReal.ofReal detUpper *
          Measure.map childRepeatedDecayMismatch
            (Measure.map chart iidMassPairLaw)
            (absoluteMismatchSublevel delta) :=
    htargetBound.trans (mul_le_mul_right hmismatchMono _)
  have hmismatchFinite :
      Measure.map childRepeatedDecayMismatch
          (Measure.map chart iidMassPairLaw)
          (absoluteMismatchSublevel delta) ≠ ∞ := by
    rw [Measure.map_apply measurable_childRepeatedDecayMismatch
      (measurableSet_absoluteMismatchSublevel delta)]
    rw [Measure.map_apply
      (continuous_actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child).measurable
      ((measurableSet_absoluteMismatchSublevel delta).preimage
        measurable_childRepeatedDecayMismatch)]
    have huniv : iidMassPairLaw Set.univ = 1 := by
      simp [iidMassPairLaw]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      ((measure_mono (subset_univ _)).trans_eq huniv)
  have hupperFinite :
      ENNReal.ofReal detUpper *
          Measure.map childRepeatedDecayMismatch
            (Measure.map chart iidMassPairLaw)
            (absoluteMismatchSublevel delta) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmismatchFinite
  have hreal := ENNReal.toReal_mono hupperFinite hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hdetUpper.le,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hdelta.le)] at hreal
  rw [show (2 * childVolume / detUpper) * delta =
    (childVolume * (2 * delta)) / detUpper by ring]
  apply (div_le_iff₀ hdetUpper).2
  simpa [childVolume, Measure.real, mul_comm] using hreal

end

end ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound

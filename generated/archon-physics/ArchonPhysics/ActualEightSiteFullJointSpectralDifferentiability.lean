import ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
import ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability

/-!
# Joint differentiability of the full eight-mass spectral chart

This module removes the frozen-environment restriction from the analytic
part of the eight-site small-ball argument.  At every point in the interior
of the eight-fold mass support with simple spectrum, every ordered
eigenvalue is a strict differentiable function of all eight raw masses.
The same is true of the three selected positive frequencies and of the
lifted `(child₁, child₂, mismatch)` chart.

No quantitative small-ball estimate is asserted here: invertibility of an
appropriate augmented eight-dimensional chart and the ensuing measure
distortion estimate are separate geometric steps.
-/

open scoped Matrix

namespace ArchonPhysics.ActualEightSiteFullJointSpectralDifferentiability

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function Set

noncomputable section

/-- In the support interior the clipped mass is locally the corresponding
raw coordinate, jointly for all eight coordinates. -/
theorem contDiffAt_one_fullEightMassConfig_mass_of_mem_interior
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (i : Lattice.Site 8) :
    ContDiffAt Real 1 (fun y => (fullEightMassConfig y).mass i) x := by
  have hnearInterior : ∀ᶠ y in nhds x, y ∈ fullEightMassSupportInterior :=
    isOpen_fullEightMassSupportInterior.mem_nhds hx
  have hcoordinate : ContDiffAt Real 1
      (fun y : EightMassVector => y ⟨i.val, i.val_lt⟩) x := by
    fun_prop
  apply hcoordinate.congr_of_eventuallyEq
  filter_upwards [hnearInterior] with y hy
  change clippedMass (y ⟨i.val, i.val_lt⟩) = y ⟨i.val, i.val_lt⟩
  apply clippedMass_eq_self
  exact ⟨(hy ⟨i.val, i.val_lt⟩).1.le, (hy ⟨i.val, i.val_lt⟩).2.le⟩

theorem contDiffAt_one_fullEightBondMatrix_apply_of_mem_interior
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (i j : Lattice.Site 8) :
    ContDiffAt Real 1 (fun y => fullEightBondMatrix y i j) x := by
  unfold fullEightBondMatrix massWeightedDifferenceMatrix
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  apply ContDiffAt.sum
  intro k _hk
  by_cases hkj : k = j
  · subst k
    simp only [ite_true]
    have hmass := contDiffAt_one_fullEightMassConfig_mass_of_mem_interior hx j
    have hsqrt : ContDiffAt Real 1
        (fun y => Real.sqrt ((fullEightMassConfig y).mass j)) x :=
      hmass.sqrt (ne_of_gt ((fullEightMassConfig x).mass_pos j))
    exact contDiffAt_const.mul
      (hsqrt.inv (Real.sqrt_ne_zero'.2 ((fullEightMassConfig x).mass_pos j)))
  · simpa [hkj] using
      (contDiffAt_const : ContDiffAt Real 1
        (fun _ : EightMassVector => (0 : Real)) x)

theorem contDiffAt_one_fullEightHarmonic_apply_of_mem_interior
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (i j : Lattice.Site 8) :
    ContDiffAt Real 1 (fun y => (fullEightHarmonic y).1 i j) x := by
  unfold fullEightHarmonic harmonicHermitian
    massWeightedHarmonicMatrix
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro k _hk
  exact (contDiffAt_one_fullEightBondMatrix_apply_of_mem_interior hx k i).mul
    (contDiffAt_one_fullEightBondMatrix_apply_of_mem_interior hx k j)

/-- Characteristic equation jointly in all eight raw masses and energy. -/
def actualFullEightCharacteristicEquation
    (parameterEnergy : EightMassVector × Real) : Real :=
  (Matrix.charpoly (fullEightHarmonic parameterEnergy.1).1).eval
    parameterEnergy.2

theorem contDiffAt_one_actualFullEightCharacteristicEquation
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (energy : Real) :
    ContDiffAt Real 1 actualFullEightCharacteristicEquation (x, energy) := by
  rw [show actualFullEightCharacteristicEquation =
      fun parameterEnergy =>
        ((Matrix.scalar (Lattice.Site 8) parameterEnergy.2 :
            Matrix (Lattice.Site 8) (Lattice.Site 8) Real) -
          Matrix.of ((fullEightHarmonic parameterEnergy.1).val)).det by
    funext parameterEnergy
    exact Matrix.eval_charpoly _ _]
  refine contDiffAt_one_det_of_entries
    (matrix := fun parameterEnergy : EightMassVector × Real =>
      (Matrix.scalar (Lattice.Site 8) parameterEnergy.2 :
          Matrix (Lattice.Site 8) (Lattice.Site 8) Real) -
        Matrix.of ((fullEightHarmonic parameterEnergy.1).val))
    (x := (x, energy)) ?_
  intro i j
  simp only [Matrix.sub_apply, Matrix.scalar_apply]
  have hmatrix : ContDiffAt Real 1
      (fun parameterEnergy : EightMassVector × Real =>
        (fullEightHarmonic parameterEnergy.1).1 i j) (x, energy) :=
    (contDiffAt_one_fullEightHarmonic_apply_of_mem_interior hx i j).fst'
  by_cases hij : i = j
  · subst j
    simpa [Matrix.diagonal_apply] using contDiffAt_snd.sub hmatrix
  · simpa [Matrix.diagonal_apply, hij] using hmatrix.neg

/-- At an interior simple-spectrum point, an ordered eigenvalue is strictly
differentiable jointly in all eight raw masses. -/
theorem exists_hasStrictFDerivAt_fullEightOrderedEigenvalue
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x))
    (k : Fin (Fintype.card (Lattice.Site 8))) :
    ∃ derivative : EightMassVector →L[Real] Real,
      HasStrictFDerivAt
        (fun y => orderedEigenvalue (fullEightHarmonic y) k)
        derivative x := by
  let A := fullEightHarmonic x
  let lambda := orderedEigenvalue A k
  let characteristic := actualFullEightCharacteristicEquation
  let Dcharacteristic := fderiv Real characteristic (x, lambda)
  have hcharacteristicC1 :
      ContDiffAt Real 1 characteristic (x, lambda) :=
    contDiffAt_one_actualFullEightCharacteristicEquation hx lambda
  have hcharacteristicDeriv :
      HasFDerivAt characteristic Dcharacteristic (x, lambda) :=
    hcharacteristicC1.differentiableAt_one.hasFDerivAt
  have hcharacteristicStrict :
      HasStrictFDerivAt characteristic Dcharacteristic (x, lambda) :=
    hcharacteristicC1.hasStrictFDerivAt' hcharacteristicDeriv (by norm_num)
  have hinclusion : HasFDerivAt (fun energy : Real => (x, energy))
      (ContinuousLinearMap.inr Real EightMassVector Real) lambda :=
    hasFDerivAt_prodMk_right x lambda
  have hslice : HasFDerivAt
      (fun energy : Real => characteristic (x, energy))
      (Dcharacteristic ∘L ContinuousLinearMap.inr Real EightMassVector Real)
      lambda := by
    simpa [Function.comp_def] using
      hcharacteristicDeriv.comp lambda hinclusion
  have hpolynomial : HasFDerivAt
      (fun energy : Real => characteristic (x, energy))
      (ContinuousLinearMap.toSpanSingleton Real
        ((Matrix.charpoly A.1).derivative.eval lambda)) lambda := by
    simpa [characteristic, actualFullEightCharacteristicEquation, A, lambda] using
      ((Matrix.charpoly A.1).hasDerivAt lambda).hasFDerivAt
  have hpartial :
      Dcharacteristic ∘L ContinuousLinearMap.inr Real EightMassVector Real =
        ContinuousLinearMap.toSpanSingleton Real
          ((Matrix.charpoly A.1).derivative.eval lambda) :=
    hslice.unique hpolynomial
  have hrootDerivative :
      (Matrix.charpoly A.1).derivative.eval lambda ≠ 0 :=
    charpoly_derivative_eval_orderedEigenvalue_ne_zero A hsimple k
  let scalarEquiv : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 ((Matrix.charpoly A.1).derivative.eval lambda)
        hrootDerivative)
  have hscalarEquiv : (scalarEquiv : Real →L[Real] Real) =
      ContinuousLinearMap.toSpanSingleton Real
        ((Matrix.charpoly A.1).derivative.eval lambda) := by
    apply ContinuousLinearMap.ext
    intro z
    simp [scalarEquiv, mul_comm]
  have hpartialInvertible :
      (Dcharacteristic ∘L
        ContinuousLinearMap.inr Real EightMassVector Real).IsInvertible := by
    rw [hpartial]
    exact ⟨scalarEquiv, hscalarEquiv⟩
  let branch := hcharacteristicStrict.implicitFunctionOfProdDomain
    hpartialInvertible
  have hbranchDerivative : HasStrictFDerivAt branch
      (-(Dcharacteristic ∘L
            ContinuousLinearMap.inr Real EightMassVector Real).inverse ∘L
        (Dcharacteristic ∘L
          ContinuousLinearMap.inl Real EightMassVector Real)) x :=
    hcharacteristicStrict.hasStrictFDerivAt_implicitFunctionOfProdDomain
      hpartialInvertible
  let orderedBranch : EightMassVector → Real := fun y =>
    orderedEigenvalue (fullEightHarmonic y) k
  have horderedContinuous : Continuous orderedBranch :=
    (continuous_orderedEigenvalue k).comp continuous_fullEightHarmonic
  have horderedTendsto : Tendsto (fun y => (y, orderedBranch y))
      (nhds x) (nhds (x, lambda)) :=
    tendsto_id.prodMk_nhds horderedContinuous.continuousAt
  have hrootBase : characteristic (x, lambda) = 0 :=
    charpoly_eval_orderedEigenvalue_eq_zero A k
  have hbranchEq : branch =ᶠ[nhds x] orderedBranch := by
    have hiff :=
      hcharacteristicStrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        hpartialInvertible
    filter_upwards [horderedTendsto.eventually hiff] with y hnear
    have hrootNearby : characteristic (y, orderedBranch y) = 0 :=
      charpoly_eval_orderedEigenvalue_eq_zero (fullEightHarmonic y) k
    exact hnear.mp (hrootNearby.trans hrootBase.symm)
  refine ⟨
    -(Dcharacteristic ∘L
          ContinuousLinearMap.inr Real EightMassVector Real).inverse ∘L
      (Dcharacteristic ∘L
        ContinuousLinearMap.inl Real EightMassVector Real), ?_⟩
  exact hbranchDerivative.congr_of_eventuallyEq hbranchEq

theorem exists_hasStrictFDerivAt_fullEightOrderedModeFrequency
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x))
    (k : Fin (Fintype.card (Lattice.Site 8)))
    (hpositive : 0 < orderedEigenvalue (fullEightHarmonic x) k) :
    ∃ derivative : EightMassVector →L[Real] Real,
      HasStrictFDerivAt
        (fun y => orderedModeFrequency (fullEightHarmonic y) k)
        derivative x := by
  obtain ⟨derivative, hderivative⟩ :=
    exists_hasStrictFDerivAt_fullEightOrderedEigenvalue hx hsimple k
  refine ⟨(1 / (2 * Real.sqrt
    (orderedEigenvalue (fullEightHarmonic x) k))) • derivative, ?_⟩
  simpa [orderedModeFrequency] using hderivative.sqrt (ne_of_gt hpositive)

/-- The full-eight lifted chart keeps the two child frequencies and replaces
the parent frequency by the signed three-wave mismatch. -/
def actualEightSiteFullLiftedFrequencyChart
    (x : EightMassVector) : MassTriple :=
  ((orderedModeFrequency (fullEightHarmonic x)
      (actualEightSiteDecayModes 1),
    orderedModeFrequency (fullEightHarmonic x)
      (actualEightSiteDecayModes 2)),
    actualEightSiteSelectedMismatch x)

/-- The full-eight lifted chart is strictly differentiable jointly in all
eight raw masses at every interior simple-spectrum point. -/
theorem exists_hasStrictFDerivAt_actualEightSiteFullLiftedFrequencyChart
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x)) :
    ∃ derivative : EightMassVector →L[Real] MassTriple,
      HasStrictFDerivAt actualEightSiteFullLiftedFrequencyChart derivative x := by
  have hpositive : ∀ r, 0 < orderedEigenvalue
      (fullEightHarmonic x) (actualEightSiteDecayModes r) := by
    intro r
    exact Real.sqrt_pos.1 (actualEightSiteSelectedFrequency_pos x r)
  choose derivative hderivative using fun r =>
    exists_hasStrictFDerivAt_fullEightOrderedModeFrequency hx hsimple
      (actualEightSiteDecayModes r) (hpositive r)
  let mismatchDerivative : EightMassVector →L[Real] Real :=
    ∑ r, (actualEightSiteDecaySign r).coefficient • derivative r
  have hmismatch : HasStrictFDerivAt
      (fun y => ∑ r, (actualEightSiteDecaySign r).coefficient *
        orderedModeFrequency (fullEightHarmonic y)
          (actualEightSiteDecayModes r)) mismatchDerivative x := by
    change HasStrictFDerivAt
      (∑ r, fun y : EightMassVector =>
        (actualEightSiteDecaySign r).coefficient *
          orderedModeFrequency (fullEightHarmonic y)
            (actualEightSiteDecayModes r)) mismatchDerivative x
    simpa only [mismatchDerivative] using
      HasStrictFDerivAt.sum (u := Finset.univ)
        (fun r _hr =>
          (hderivative r).const_mul (actualEightSiteDecaySign r).coefficient)
  refine ⟨(derivative 1).prod (derivative 2) |>.prod mismatchDerivative, ?_⟩
  convert ((hderivative 1).prodMk (hderivative 2)).prodMk hmismatch using 1 <;>
    rfl

end

end ArchonPhysics.ActualEightSiteFullJointSpectralDifferentiability

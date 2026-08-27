import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
import ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
import ArchonPhysics.FrequencyMismatchKernelMarginalDomination
import ArchonPhysics.ThreeParameterProjectorWeightJacobian

/-!
# All-distinct leg--mismatch domination

The actual three-mass coarea chart uses coordinates
`(omega_child1, omega_child2, mismatch)`.  This file changes those coordinates
to `(omega_leg, mismatch, omega_fibre)` for each leg of the decay channel.
The change of variables has determinant of absolute value one.  The remaining
fibre frequency lies in `[0, sqrt 5]`, so a three-dimensional good coarea
bound gives a two-dimensional `(omega_leg, mismatch)` bound with the explicit
factor `sqrt 5`.

Only the good lifted law is claimed to have this density.  The bad law is
handled after resonance broadening by its pre-existing kernel-weighted budget.
-/

open scoped ENNReal Matrix

namespace ArchonPhysics.ActualThreeMassAllDistinctLegMismatchDomination

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
open ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.FrequencyMismatchKernelMarginalDomination
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

local instance massTripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-! ## Exact decay-channel coordinate changes -/

/-- Recover the frequency on a marked decay leg from the lifted chart
coordinates `((omega1, omega2), mismatch)`. -/
def decayLiftedLegFrequency (leg : Fin 3) (point : MassTriple) : Real :=
  if leg = 0 then point.1.1 + point.1.2 + point.2
  else if leg = 1 then point.1.1
  else point.1.2

theorem continuous_decayLiftedLegFrequency (leg : Fin 3) :
    Continuous (decayLiftedLegFrequency leg) := by
  unfold decayLiftedLegFrequency
  split_ifs <;> fun_prop

theorem measurable_decayLiftedLegFrequency (leg : Fin 3) :
    Measurable (decayLiftedLegFrequency leg) :=
  (continuous_decayLiftedLegFrequency leg).measurable

/-- Parent coordinates
`((omega1, omega2), delta) -> ((omega1 + omega2 + delta, delta), omega2)`.
The last coordinate is the bounded fibre. -/
def decayParentLegMismatchFiberLinearEquiv : MassTriple ≃ₗ[Real] MassTriple where
  toFun point := ((point.1.1 + point.1.2 + point.2, point.2), point.1.2)
  invFun point := ((point.1.1 - point.2 - point.1.2, point.2), point.1.2)
  map_add' x y := by
    ext
    all_goals dsimp
    all_goals ring
  map_smul' c x := by
    ext
    all_goals dsimp
    all_goals ring
  left_inv x := by
    ext
    all_goals dsimp
    all_goals ring
  right_inv x := by
    ext
    all_goals dsimp
    all_goals ring

/-- First-child coordinates
`((omega1, omega2), delta) -> ((omega1, delta), omega2)`. -/
def decayChildOneLegMismatchFiberLinearEquiv : MassTriple ≃ₗ[Real] MassTriple where
  toFun point := ((point.1.1, point.2), point.1.2)
  invFun point := ((point.1.1, point.2), point.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Second-child coordinates
`((omega1, omega2), delta) -> ((omega2, delta), omega1)`. -/
def decayChildTwoLegMismatchFiberLinearEquiv : MassTriple ≃ₗ[Real] MassTriple where
  toFun point := ((point.1.2, point.2), point.1.1)
  invFun point := ((point.2, point.1.1), point.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- For every decay leg, retain `(omega_leg, mismatch)` in the first pair and
put one physical child frequency in the last coordinate. -/
def decayLegMismatchFiberLinearEquiv (leg : Fin 3) :
    MassTriple ≃ₗ[Real] MassTriple :=
  if leg = 0 then decayParentLegMismatchFiberLinearEquiv
  else if leg = 1 then decayChildOneLegMismatchFiberLinearEquiv
  else decayChildTwoLegMismatchFiberLinearEquiv

theorem decayLegMismatchFiberLinearEquiv_fst
    (leg : Fin 3) (point : MassTriple) :
    (decayLegMismatchFiberLinearEquiv leg point).1 =
      frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd
        point := by
  fin_cases leg <;>
    simp [decayLegMismatchFiberLinearEquiv,
      decayParentLegMismatchFiberLinearEquiv,
      decayChildOneLegMismatchFiberLinearEquiv,
      decayChildTwoLegMismatchFiberLinearEquiv,
      decayLiftedLegFrequency, frequencyMismatchCoordinates]

theorem continuous_decayLegMismatchFiberLinearEquiv (leg : Fin 3) :
    Continuous (decayLegMismatchFiberLinearEquiv leg) :=
  (decayLegMismatchFiberLinearEquiv leg).toLinearMap
    |>.continuous_of_finiteDimensional

theorem measurable_decayLegMismatchFiberLinearEquiv (leg : Fin 3) :
    Measurable (decayLegMismatchFiberLinearEquiv leg) :=
  (continuous_decayLegMismatchFiberLinearEquiv leg).measurable

theorem toMatrix_decayParentLegMismatchFiberLinearEquiv :
    LinearMap.toMatrix massTripleBasis massTripleBasis
      (decayParentLegMismatchFiberLinearEquiv : MassTriple →ₗ[Real] MassTriple) =
      !![(1 : Real), 1, 1; 0, 0, 1; 0, 1, 0] := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [decayParentLegMismatchFiberLinearEquiv]

theorem toMatrix_decayChildOneLegMismatchFiberLinearEquiv :
    LinearMap.toMatrix massTripleBasis massTripleBasis
      (decayChildOneLegMismatchFiberLinearEquiv :
        MassTriple →ₗ[Real] MassTriple) =
      !![(1 : Real), 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [decayChildOneLegMismatchFiberLinearEquiv]

theorem toMatrix_decayChildTwoLegMismatchFiberLinearEquiv :
    LinearMap.toMatrix massTripleBasis massTripleBasis
      (decayChildTwoLegMismatchFiberLinearEquiv :
        MassTriple →ₗ[Real] MassTriple) =
      !![(0 : Real), 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [decayChildTwoLegMismatchFiberLinearEquiv]

theorem det_decayParentLegMismatchFiberLinearEquiv :
    LinearMap.det (decayParentLegMismatchFiberLinearEquiv :
      MassTriple →ₗ[Real] MassTriple) = -1 := by
  rw [← LinearMap.det_toMatrix massTripleBasis
    (decayParentLegMismatchFiberLinearEquiv :
      MassTriple →ₗ[Real] MassTriple),
    toMatrix_decayParentLegMismatchFiberLinearEquiv]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

theorem det_decayChildOneLegMismatchFiberLinearEquiv :
    LinearMap.det (decayChildOneLegMismatchFiberLinearEquiv :
      MassTriple →ₗ[Real] MassTriple) = -1 := by
  rw [← LinearMap.det_toMatrix massTripleBasis
    (decayChildOneLegMismatchFiberLinearEquiv :
      MassTriple →ₗ[Real] MassTriple),
    toMatrix_decayChildOneLegMismatchFiberLinearEquiv]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

theorem det_decayChildTwoLegMismatchFiberLinearEquiv :
    LinearMap.det (decayChildTwoLegMismatchFiberLinearEquiv :
      MassTriple →ₗ[Real] MassTriple) = 1 := by
  rw [← LinearMap.det_toMatrix massTripleBasis
    (decayChildTwoLegMismatchFiberLinearEquiv :
      MassTriple →ₗ[Real] MassTriple),
    toMatrix_decayChildTwoLegMismatchFiberLinearEquiv]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

theorem det_decayLegMismatchFiberLinearEquiv (leg : Fin 3) :
    LinearMap.det (decayLegMismatchFiberLinearEquiv leg :
      MassTriple →ₗ[Real] MassTriple) = if leg = 2 then 1 else -1 := by
  fin_cases leg
  · simpa [decayLegMismatchFiberLinearEquiv] using
      det_decayParentLegMismatchFiberLinearEquiv
  · simpa [decayLegMismatchFiberLinearEquiv] using
      det_decayChildOneLegMismatchFiberLinearEquiv
  · simpa [decayLegMismatchFiberLinearEquiv] using
      det_decayChildTwoLegMismatchFiberLinearEquiv

theorem volume_preimage_decayLegMismatchFiberLinearEquiv
    (leg : Fin 3) (target : Set MassTriple) :
    (volume : Measure MassTriple)
        (decayLegMismatchFiberLinearEquiv leg ⁻¹' target) =
      (volume : Measure MassTriple) target := by
  rw [Measure.addHaar_preimage_linearEquiv]
  have hfactor : ENNReal.ofReal
      |LinearMap.det ((decayLegMismatchFiberLinearEquiv leg).symm :
        MassTriple →ₗ[Real] MassTriple)| = 1 := by
    rw [LinearEquiv.det_coe_symm,
      det_decayLegMismatchFiberLinearEquiv]
    fin_cases leg <;> norm_num +decide
  rw [hfactor, one_mul]

/-! ## Bounded-fibre projection -/

/-- The lifted points whose fibre frequency lies in the physical band. -/
def decayLegFrequencyFiberBand (leg : Fin 3) (W : Real) : Set MassTriple :=
  {point | (decayLegMismatchFiberLinearEquiv leg point).2 ∈ Icc 0 W}

theorem measurableSet_decayLegFrequencyFiberBand (leg : Fin 3) (W : Real) :
    MeasurableSet (decayLegFrequencyFiberBand leg W) := by
  exact measurableSet_Icc.preimage
    (measurable_snd.comp (measurable_decayLegMismatchFiberLinearEquiv leg))

/-- Exact volume of a joint target with a bounded omitted-frequency fibre. -/
theorem volume_frequencyMismatch_preimage_inter_fiberBand
    (leg : Fin 3) {A : Set (Real × Real)} (hA : MeasurableSet A)
    {W : Real} :
    (volume : Measure MassTriple)
        (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd
            ⁻¹' A ∩ decayLegFrequencyFiberBand leg W) =
      (volume : Measure (Real × Real)) A * ENNReal.ofReal W := by
  have hset : MeasurableSet (A ×ˢ Icc (0 : Real) W) :=
    hA.prod measurableSet_Icc
  have hpreimage :
      frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd
            ⁻¹' A ∩ decayLegFrequencyFiberBand leg W =
        decayLegMismatchFiberLinearEquiv leg ⁻¹' (A ×ˢ Icc 0 W) := by
    ext point
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Icc]
    rw [decayLegMismatchFiberLinearEquiv_fst]
    rfl
  rw [hpreimage,
    volume_preimage_decayLegMismatchFiberLinearEquiv leg]
  conv_lhs => rw [Measure.volume_eq_prod]
  rw [Measure.prod_prod, Real.volume_Icc]
  simp only [sub_zero]

/-- A three-dimensional density bound supported in the physical fibre band
pushes forward to the two-dimensional leg--mismatch density bound. -/
theorem map_frequencyMismatch_le_volume_of_lifted_le_of_fiberSupport
    (measure : Measure MassTriple) (leg : Fin 3) (C : ENNReal) {W : Real}
    (hle : measure ≤ C • (volume : Measure MassTriple))
    (hsupport : measure (decayLegFrequencyFiberBand leg W)ᶜ = 0) :
    Measure.map
        (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd)
        measure ≤
      (C * ENNReal.ofReal W) •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  have haesupport : ∀ᵐ point ∂measure,
      point ∈ decayLegFrequencyFiberBand leg W :=
    ae_iff.mpr hsupport
  apply Measure.le_iff.2
  intro A hA
  rw [Measure.map_apply
      (measurable_frequencyMismatchCoordinates
        (measurable_decayLiftedLegFrequency leg) measurable_snd) hA,
    Measure.smul_apply, smul_eq_mul]
  calc
    measure
        (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd
          ⁻¹' A) =
        measure
          (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd
              ⁻¹' A ∩ decayLegFrequencyFiberBand leg W) := by
      rw [← Measure.measure_inter_eq_of_ae haesupport]
      rw [inter_comm]
    _ ≤ (C • (volume : Measure MassTriple))
          (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd
              ⁻¹' A ∩ decayLegFrequencyFiberBand leg W) :=
      Measure.le_iff'.1 hle _
    _ = C * (volume : Measure MassTriple)
          (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd
              ⁻¹' A ∩ decayLegFrequencyFiberBand leg W) := by
      rw [Measure.smul_apply, smul_eq_mul]
    _ = C * ((volume : Measure (Real × Real)) A * ENNReal.ofReal W) := by
      rw [volume_frequencyMismatch_preimage_inter_fiberBand leg hA]
    _ = (C * ENNReal.ofReal W) *
        ((volume : Measure Real).prod (volume : Measure Real)) A := by
      rw [← Measure.volume_eq_prod]
      ac_rfl

/-! ## The genuine actual all-distinct good law -/

theorem actualThreeMassLiftedFrequencyChart_mem_decayLegFrequencyFiberBand
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (leg : Fin 3) (triple : MassTriple) :
    actualThreeMassLiftedFrequencyChart fixed site₀ site₁ site₂
        decayInteractionSign modes triple ∈
      decayLegFrequencyFiberBand leg (Real.sqrt 5) := by
  have hfrequency (r : Fin 3) :
      orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
          (modes r) ∈ Icc 0 (Real.sqrt 5) :=
    ⟨Real.sqrt_nonneg _,
      actualThreeMass_orderedModeFrequency_le_sqrt_five
        fixed hfixed site₀ site₁ site₂ triple (modes r)⟩
  fin_cases leg
  · simpa [decayLegFrequencyFiberBand,
      decayLegMismatchFiberLinearEquiv,
      decayParentLegMismatchFiberLinearEquiv,
      decayChildOneLegMismatchFiberLinearEquiv,
      decayChildTwoLegMismatchFiberLinearEquiv,
      actualThreeMassLiftedFrequencyChart] using hfrequency (2 : Fin 3)
  · simpa [decayLegFrequencyFiberBand,
      decayLegMismatchFiberLinearEquiv,
      decayParentLegMismatchFiberLinearEquiv,
      decayChildOneLegMismatchFiberLinearEquiv,
      decayChildTwoLegMismatchFiberLinearEquiv,
      actualThreeMassLiftedFrequencyChart] using hfrequency (2 : Fin 3)
  · simpa [decayLegFrequencyFiberBand,
      decayLegMismatchFiberLinearEquiv,
      decayParentLegMismatchFiberLinearEquiv,
      decayChildOneLegMismatchFiberLinearEquiv,
      decayChildTwoLegMismatchFiberLinearEquiv,
      actualThreeMassLiftedFrequencyChart] using hfrequency (1 : Fin 3)

theorem actualThreeMassAllDistinctJointGood_compl_fiberBand_eq_zero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (good : OrderedModeTriple N → Set MassTriple)
    (leg : Fin 3) :
    actualThreeMassAllDistinctJointGoodLiftedMeasure
        fixed site₀ site₁ site₂ decayInteractionSign good
        (decayLegFrequencyFiberBand leg (Real.sqrt 5))ᶜ = 0 := by
  classical
  unfold actualThreeMassAllDistinctJointGoodLiftedMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, smul_eq_mul]
  have hsummand (modes : OrderedModeTriple N) :
      Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ decayInteractionSign modes)
          ((iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes)).restrict (good modes))
          (decayLegFrequencyFiberBand leg (Real.sqrt 5))ᶜ = 0 := by
    rw [Measure.map_apply
      (continuous_actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ decayInteractionSign modes).measurable
      (measurableSet_decayLegFrequencyFiberBand leg _).compl]
    have hpreimage :
        actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ decayInteractionSign modes ⁻¹'
            (decayLegFrequencyFiberBand leg (Real.sqrt 5))ᶜ = ∅ := by
      ext triple
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false]
      constructor
      · intro hnot
        exact (hnot
          (actualThreeMassLiftedFrequencyChart_mem_decayLegFrequencyFiberBand
            fixed hfixed site₀ site₁ site₂ modes leg triple)).elim
      · intro hfalse
        exact hfalse.elim
    rw [hpreimage, measure_empty]
  rw [Finset.sum_eq_zero fun modes _hmodes => hsummand modes]
  simp

/-- The requested uniform three-leg endpoint: a genuine 3D good coarea bound
for the actual all-distinct law implies a 2D raw `(omega_leg, mismatch)`
Lebesgue domination, with constant `C * ofReal (sqrt 5)` for every leg. -/
theorem actualThreeMassAllDistinctJointGood_map_legFrequencyMismatch_le_volume
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (good : OrderedModeTriple N → Set MassTriple)
    (C : ENNReal)
    (hcoarea : actualThreeMassAllDistinctJointGoodCoareaBound
      fixed site₀ site₁ site₂ decayInteractionSign good C)
    (leg : Fin 3) :
    Measure.map
        (frequencyMismatchCoordinates (decayLiftedLegFrequency leg) Prod.snd)
        (actualThreeMassAllDistinctJointGoodLiftedMeasure
          fixed site₀ site₁ site₂ decayInteractionSign good) ≤
      (C * ENNReal.ofReal (Real.sqrt 5)) •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  exact map_frequencyMismatch_le_volume_of_lifted_le_of_fiberSupport
    (actualThreeMassAllDistinctJointGoodLiftedMeasure
      fixed site₀ site₁ site₂ decayInteractionSign good)
    leg C hcoarea
    (actualThreeMassAllDistinctJointGood_compl_fiberBand_eq_zero
      fixed hfixed site₀ site₁ site₂ good leg)

end

end ArchonPhysics.ActualThreeMassAllDistinctLegMismatchDomination

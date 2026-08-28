import ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability

/-!
# Exact fixed-radius Haar moment closure

The canonical random-phase initial data used by the FPUT model have fixed
modal radii and independent Haar phases.  Their fourth moments are therefore
not Gaussian Wick moments on repeated indices.  The exact closure is instead
Fourier-charge balance.  This module records that closure for arbitrary mode
families and transfers it, with explicit constants, to any bounded measurable
family which is pointwise close to the Haar reference.

This is a finite-volume, unconditional phase-average statement.  It removes a
spurious Gaussian assumption from the one-block RPA interface; it does not by
itself propagate phase randomness through kinetic time.
-/

namespace ArchonPhysics.CanonicalFixedRadiusHaarMomentClosure

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability
open ArchonPhysics.RandomPhaseMoments

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance finitePhaseHaarLawIsProbability
    (d : Type*) [Fintype d] : IsProbabilityMeasure (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

variable {d I : Type*} [Fintype d]

/-- A deterministic modal radius multiplying one finite Haar character. -/
def fixedRadiusHaarAmplitude
    (coefficient : I → Complex) (charge : I → d → Int)
    (phase : UnitAddTorus d) (mode : I) : Complex :=
  coefficient mode * mFourier (charge mode) phase

theorem continuous_fixedRadiusHaarAmplitude
    (coefficient : I → Complex) (charge : I → d → Int) (mode : I) :
    Continuous (fun phase : UnitAddTorus d ↦
      fixedRadiusHaarAmplitude coefficient charge phase mode) := by
  unfold fixedRadiusHaarAmplitude
  fun_prop

theorem norm_fixedRadiusHaarAmplitude
    (coefficient : I → Complex) (charge : I → d → Int)
    (phase : UnitAddTorus d) (mode : I) :
    ‖fixedRadiusHaarAmplitude coefficient charge phase mode‖ =
      ‖coefficient mode‖ := by
  unfold fixedRadiusHaarAmplitude
  rw [norm_mul, ArchonPhysics.FreeFPUTDuhamelResonanceBridge.norm_mFourier_apply_eq_one,
    mul_one]

/-- Pointwise normal two-point charge reduction. -/
theorem twoPointProduct_fixedRadiusHaarAmplitude
    (coefficient : I → Complex) (charge : I → d → Int)
    (phase : UnitAddTorus d) (i j : I) :
    twoPointProduct
        (fixedRadiusHaarAmplitude coefficient charge phase i)
        (fixedRadiusHaarAmplitude coefficient charge phase j) =
      (coefficient i * starRingEnd Complex (coefficient j)) *
        mFourier (charge i - charge j) phase := by
  unfold twoPointProduct fixedRadiusHaarAmplitude
  rw [map_mul]
  calc
    coefficient i * mFourier (charge i) phase *
        (starRingEnd Complex (coefficient j) *
          starRingEnd Complex (mFourier (charge j) phase)) =
      (coefficient i * starRingEnd Complex (coefficient j)) *
        (mFourier (charge i) phase * starRingEnd Complex (mFourier (charge j) phase)) := by ring
    _ = (coefficient i * starRingEnd Complex (coefficient j)) *
        mFourier (charge i - charge j) phase := by
      rw [mFourier_mul_star_mFourier]

/-- Pointwise anomalous two-point charge reduction. -/
theorem anomalousProduct_fixedRadiusHaarAmplitude
    (coefficient : I → Complex) (charge : I → d → Int)
    (phase : UnitAddTorus d) (i j : I) :
    fixedRadiusHaarAmplitude coefficient charge phase i *
        fixedRadiusHaarAmplitude coefficient charge phase j =
      (coefficient i * coefficient j) *
        mFourier (charge i + charge j) phase := by
  unfold fixedRadiusHaarAmplitude
  calc
    coefficient i * mFourier (charge i) phase *
        (coefficient j * mFourier (charge j) phase) =
      (coefficient i * coefficient j) *
        (mFourier (charge i) phase * mFourier (charge j) phase) := by ring
    _ = (coefficient i * coefficient j) *
        mFourier (charge i + charge j) phase := by rw [← mFourier_add]

/-- Pointwise four-point charge reduction in the same ordering used by the
quantitative RPA API. -/
theorem fourPointProduct_fixedRadiusHaarAmplitude
    (coefficient : I → Complex) (charge : I → d → Int)
    (phase : UnitAddTorus d) (i j k l : I) :
    fourPointProduct
        (fixedRadiusHaarAmplitude coefficient charge phase i)
        (fixedRadiusHaarAmplitude coefficient charge phase j)
        (fixedRadiusHaarAmplitude coefficient charge phase k)
        (fixedRadiusHaarAmplitude coefficient charge phase l) =
      ((coefficient i * starRingEnd Complex (coefficient j)) *
        (coefficient k * starRingEnd Complex (coefficient l))) *
        mFourier ((charge i - charge j) + (charge k - charge l)) phase := by
  unfold fourPointProduct
  rw [twoPointProduct_fixedRadiusHaarAmplitude,
    twoPointProduct_fixedRadiusHaarAmplitude]
  calc
    (coefficient i * starRingEnd Complex (coefficient j) *
          mFourier (charge i - charge j) phase) *
        (coefficient k * starRingEnd Complex (coefficient l) *
          mFourier (charge k - charge l) phase) =
      ((coefficient i * starRingEnd Complex (coefficient j)) *
        (coefficient k * starRingEnd Complex (coefficient l))) *
        (mFourier (charge i - charge j) phase *
          mFourier (charge k - charge l) phase) := by ring
    _ = ((coefficient i * starRingEnd Complex (coefficient j)) *
        (coefficient k * starRingEnd Complex (coefficient l))) *
        mFourier ((charge i - charge j) + (charge k - charge l)) phase := by
      rw [← mFourier_add]

/-- Exact normal two-point moment: equality of total phase charge is the only
survival condition. -/
theorem integral_twoPointProduct_fixedRadiusHaarAmplitude
    (coefficient : I → Complex) (charge : I → d → Int) (i j : I) :
    (∫ phase : UnitAddTorus d,
      twoPointProduct
        (fixedRadiusHaarAmplitude coefficient charge phase i)
        (fixedRadiusHaarAmplitude coefficient charge phase j)
      ∂finitePhaseHaarLaw d) =
      if charge i - charge j = 0 then
        coefficient i * starRingEnd Complex (coefficient j) else 0 := by
  simp_rw [twoPointProduct_fixedRadiusHaarAmplitude]
  rw [integral_const_mul, integral_mFourier_eq_ite]
  split <;> simp_all

/-- Exact anomalous two-point moment. -/
theorem integral_anomalousProduct_fixedRadiusHaarAmplitude
    (coefficient : I → Complex) (charge : I → d → Int) (i j : I) :
    (∫ phase : UnitAddTorus d,
      fixedRadiusHaarAmplitude coefficient charge phase i *
        fixedRadiusHaarAmplitude coefficient charge phase j
      ∂finitePhaseHaarLaw d) =
      if charge i + charge j = 0 then coefficient i * coefficient j else 0 := by
  simp_rw [anomalousProduct_fixedRadiusHaarAmplitude]
  rw [integral_const_mul, integral_mFourier_eq_ite]
  split <;> simp_all

/-- Exact fixed-radius Haar fourth moment.  In particular, repeated modes
carry coefficient one rather than the Gaussian Wick multiplicity two. -/
theorem integral_fourPointProduct_fixedRadiusHaarAmplitude
    (coefficient : I → Complex) (charge : I → d → Int)
    (i j k l : I) :
    (∫ phase : UnitAddTorus d,
      fourPointProduct
        (fixedRadiusHaarAmplitude coefficient charge phase i)
        (fixedRadiusHaarAmplitude coefficient charge phase j)
        (fixedRadiusHaarAmplitude coefficient charge phase k)
        (fixedRadiusHaarAmplitude coefficient charge phase l)
      ∂finitePhaseHaarLaw d) =
      if (charge i - charge j) + (charge k - charge l) = 0 then
        (coefficient i * starRingEnd Complex (coefficient j)) *
          (coefficient k * starRingEnd Complex (coefficient l)) else 0 := by
  simp_rw [fourPointProduct_fixedRadiusHaarAmplitude]
  rw [integral_const_mul, integral_mFourier_eq_ite]
  split <;> simp_all

/-! ## Quantitative transfer to a nearby nonlinear family -/

theorem integrable_twoPointProduct_of_uniform_bound
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] (z₁ z₂ : Omega → Complex)
    (hz₁ : Measurable z₁) (hz₂ : Measurable z₂)
    {M : Real} (hM : 0 ≤ M)
    (hb₁ : ∀ omega, ‖z₁ omega‖ ≤ M)
    (hb₂ : ∀ omega, ‖z₂ omega‖ ≤ M) :
    Integrable (fun omega ↦ twoPointProduct (z₁ omega) (z₂ omega)) mu := by
  have hmeasurable : Measurable
      (fun omega ↦ twoPointProduct (z₁ omega) (z₂ omega)) := by
    unfold twoPointProduct
    fun_prop
  apply Integrable.of_bound hmeasurable.aestronglyMeasurable (M ^ 2)
  filter_upwards with omega
  change ‖z₁ omega * starRingEnd Complex (z₂ omega)‖ ≤ M ^ 2
  rw [norm_mul]
  have hstar : ‖starRingEnd Complex (z₂ omega)‖ = ‖z₂ omega‖ := by
    change ‖star (z₂ omega)‖ = ‖z₂ omega‖
    exact norm_star _
  rw [hstar]
  calc
    ‖z₁ omega‖ * ‖z₂ omega‖ ≤ M * M :=
      mul_le_mul (hb₁ omega) (hb₂ omega) (norm_nonneg _) hM
    _ = M ^ 2 := by ring

theorem integrable_fourPointProduct_of_uniform_bound
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] (z₁ z₂ z₃ z₄ : Omega → Complex)
    (hz₁ : Measurable z₁) (hz₂ : Measurable z₂)
    (hz₃ : Measurable z₃) (hz₄ : Measurable z₄)
    {M : Real} (hM : 0 ≤ M)
    (hb₁ : ∀ omega, ‖z₁ omega‖ ≤ M)
    (hb₂ : ∀ omega, ‖z₂ omega‖ ≤ M)
    (hb₃ : ∀ omega, ‖z₃ omega‖ ≤ M)
    (hb₄ : ∀ omega, ‖z₄ omega‖ ≤ M) :
    Integrable (fun omega ↦
      fourPointProduct (z₁ omega) (z₂ omega) (z₃ omega) (z₄ omega)) mu := by
  have hmeasurable : Measurable (fun omega ↦
      fourPointProduct (z₁ omega) (z₂ omega) (z₃ omega) (z₄ omega)) := by
    unfold fourPointProduct twoPointProduct
    fun_prop
  apply Integrable.of_bound hmeasurable.aestronglyMeasurable (M ^ 4)
  filter_upwards with omega
  have hnorm :
      ‖fourPointProduct (z₁ omega) (z₂ omega) (z₃ omega) (z₄ omega)‖ =
        (‖z₁ omega‖ * ‖z₂ omega‖) * (‖z₃ omega‖ * ‖z₄ omega‖) := by
    simp [fourPointProduct, twoPointProduct]
  rw [hnorm]
  have hleft : ‖z₁ omega‖ * ‖z₂ omega‖ ≤ M ^ 2 := by
    calc
      _ ≤ M * M := mul_le_mul (hb₁ omega) (hb₂ omega) (norm_nonneg _) hM
      _ = M ^ 2 := by ring
  have hright : ‖z₃ omega‖ * ‖z₄ omega‖ ≤ M ^ 2 := by
    calc
      _ ≤ M * M := mul_le_mul (hb₃ omega) (hb₄ omega) (norm_nonneg _) hM
      _ = M ^ 2 := by ring
  calc
    (‖z₁ omega‖ * ‖z₂ omega‖) * (‖z₃ omega‖ * ‖z₄ omega‖) ≤
        M ^ 2 * M ^ 2 := mul_le_mul hleft hright (by positivity) (sq_nonneg M)
    _ = M ^ 4 := by ring

/-- A pointwise `epsilon` perturbation of a fixed-radius Haar family has the
correct charge-balanced normal moment up to `2 M epsilon`. -/
theorem norm_integral_twoPoint_sub_chargeBalanced_le
    (coefficient : I → Complex) (charge : I → d → Int)
    (actual : UnitAddTorus d → I → Complex)
    (hactualMeasurable : ∀ i, Measurable (fun phase ↦ actual phase i))
    {M epsilon : Real} (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hactualBound : ∀ phase i, ‖actual phase i‖ ≤ M)
    (hrefBound : ∀ i, ‖coefficient i‖ ≤ M)
    (hdistance : ∀ phase i,
      ‖actual phase i - fixedRadiusHaarAmplitude coefficient charge phase i‖ ≤
        epsilon)
    (i j : I) :
    ‖(∫ phase : UnitAddTorus d,
        twoPointProduct (actual phase i) (actual phase j)
        ∂finitePhaseHaarLaw d) -
      (if charge i - charge j = 0 then
        coefficient i * starRingEnd Complex (coefficient j) else 0)‖ ≤
      2 * M * epsilon := by
  let reference : UnitAddTorus d → I → Complex :=
    fun phase mode ↦ fixedRadiusHaarAmplitude coefficient charge phase mode
  have hrefMeasurable : ∀ mode, Measurable (fun phase ↦ reference phase mode) :=
    fun mode ↦ (continuous_fixedRadiusHaarAmplitude coefficient charge mode).measurable
  have hrefPointBound : ∀ phase mode, ‖reference phase mode‖ ≤ M := by
    intro phase mode
    rw [norm_fixedRadiusHaarAmplitude]
    exact hrefBound mode
  have hactualIntegrable := integrable_twoPointProduct_of_uniform_bound
    (mu := finitePhaseHaarLaw d) (fun phase ↦ actual phase i)
      (fun phase ↦ actual phase j)
      (hactualMeasurable i) (hactualMeasurable j) hM
      (fun phase ↦ hactualBound phase i) (fun phase ↦ hactualBound phase j)
  have hrefIntegrable := integrable_twoPointProduct_of_uniform_bound
    (mu := finitePhaseHaarLaw d) (fun phase ↦ reference phase i)
      (fun phase ↦ reference phase j)
      (hrefMeasurable i) (hrefMeasurable j) hM
      (fun phase ↦ hrefPointBound phase i) (fun phase ↦ hrefPointBound phase j)
  rw [← integral_twoPointProduct_fixedRadiusHaarAmplitude
    coefficient charge i j, ← integral_sub hactualIntegrable hrefIntegrable]
  have h := norm_integral_le_of_norm_le_const
    (μ := finitePhaseHaarLaw d)
    (f := fun phase ↦
      twoPointProduct (actual phase i) (actual phase j) -
        twoPointProduct (reference phase i) (reference phase j))
    (C := 2 * M * epsilon)
    (Filter.Eventually.of_forall fun phase ↦
      norm_twoPointProduct_sub_le hM hepsilon
        (hactualBound phase i) (hactualBound phase j)
        (hrefPointBound phase i) (hrefPointBound phase j)
        (hdistance phase i) (hdistance phase j))
  rw [Measure.real, measure_univ] at h
  norm_num at h
  exact h

/-- The corresponding exact four-point transfer, with the deterministic
`4 M^3 epsilon` constant and the fixed-radius charge target. -/
theorem norm_integral_fourPoint_sub_chargeBalanced_le
    (coefficient : I → Complex) (charge : I → d → Int)
    (actual : UnitAddTorus d → I → Complex)
    (hactualMeasurable : ∀ i, Measurable (fun phase ↦ actual phase i))
    {M epsilon : Real} (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hactualBound : ∀ phase i, ‖actual phase i‖ ≤ M)
    (hrefBound : ∀ i, ‖coefficient i‖ ≤ M)
    (hdistance : ∀ phase i,
      ‖actual phase i - fixedRadiusHaarAmplitude coefficient charge phase i‖ ≤
        epsilon)
    (i j k l : I) :
    ‖(∫ phase : UnitAddTorus d,
        fourPointProduct
          (actual phase i) (actual phase j) (actual phase k) (actual phase l)
        ∂finitePhaseHaarLaw d) -
      (if (charge i - charge j) + (charge k - charge l) = 0 then
        (coefficient i * starRingEnd Complex (coefficient j)) *
          (coefficient k * starRingEnd Complex (coefficient l)) else 0)‖ ≤
      4 * M ^ 3 * epsilon := by
  let reference : UnitAddTorus d → I → Complex :=
    fun phase mode ↦ fixedRadiusHaarAmplitude coefficient charge phase mode
  have hrefMeasurable : ∀ mode, Measurable (fun phase ↦ reference phase mode) :=
    fun mode ↦ (continuous_fixedRadiusHaarAmplitude coefficient charge mode).measurable
  have hrefPointBound : ∀ phase mode, ‖reference phase mode‖ ≤ M := by
    intro phase mode
    rw [norm_fixedRadiusHaarAmplitude]
    exact hrefBound mode
  have hactualIntegrable := integrable_fourPointProduct_of_uniform_bound
    (mu := finitePhaseHaarLaw d)
    (fun phase ↦ actual phase i) (fun phase ↦ actual phase j)
    (fun phase ↦ actual phase k) (fun phase ↦ actual phase l)
    (hactualMeasurable i) (hactualMeasurable j)
    (hactualMeasurable k) (hactualMeasurable l) hM
    (fun phase ↦ hactualBound phase i) (fun phase ↦ hactualBound phase j)
    (fun phase ↦ hactualBound phase k) (fun phase ↦ hactualBound phase l)
  have hrefIntegrable := integrable_fourPointProduct_of_uniform_bound
    (mu := finitePhaseHaarLaw d)
    (fun phase ↦ reference phase i) (fun phase ↦ reference phase j)
    (fun phase ↦ reference phase k) (fun phase ↦ reference phase l)
    (hrefMeasurable i) (hrefMeasurable j)
    (hrefMeasurable k) (hrefMeasurable l) hM
    (fun phase ↦ hrefPointBound phase i) (fun phase ↦ hrefPointBound phase j)
    (fun phase ↦ hrefPointBound phase k) (fun phase ↦ hrefPointBound phase l)
  rw [← integral_fourPointProduct_fixedRadiusHaarAmplitude
    coefficient charge i j k l, ← integral_sub hactualIntegrable hrefIntegrable]
  have h := norm_integral_le_of_norm_le_const
    (μ := finitePhaseHaarLaw d)
    (f := fun phase ↦
      fourPointProduct
          (actual phase i) (actual phase j) (actual phase k) (actual phase l) -
        fourPointProduct
          (reference phase i) (reference phase j)
          (reference phase k) (reference phase l))
    (C := 4 * M ^ 3 * epsilon)
    (Filter.Eventually.of_forall fun phase ↦
      norm_fourPointProduct_sub_le hM hepsilon
        (hactualBound phase i) (hactualBound phase j)
        (hactualBound phase k) (hactualBound phase l)
        (hrefPointBound phase i) (hrefPointBound phase j)
        (hrefPointBound phase k) (hrefPointBound phase l)
        (hdistance phase i) (hdistance phase j)
        (hdistance phase k) (hdistance phase l))
  rw [Measure.real, measure_univ] at h
  norm_num at h
  exact h

/-! ## Canonical FPUT specialization -/

/-- Deterministic radial coefficient of the canonical FPUT initial amplitude. -/
def canonicalInitialHaarCoefficient
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (mode : Lattice.Site N) : Complex :=
  ((frequency mode * radius mode /
    Real.sqrt (2 * frequency mode) : Real) : Complex)

/-- The single positive phase charge carried by a canonical initial mode. -/
def canonicalInitialHaarCharge
    {N : Nat} [NeZero N] (mode : Lattice.Site N) :
    Lattice.Site N → Int :=
  freeInitialPhaseCharge mode 0

/-- The abstract fixed-radius character is exactly the canonical FPUT initial
complex amplitude, including the totalized zero-frequency convention. -/
theorem fixedRadiusHaarAmplitude_eq_canonicalFreeComplexInitialAmplitude
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (mode : Lattice.Site N) :
    fixedRadiusHaarAmplitude
        (canonicalInitialHaarCoefficient radius frequency)
        canonicalInitialHaarCharge phase mode =
      canonicalFreeComplexInitialAmplitude radius frequency phase mode := by
  unfold fixedRadiusHaarAmplitude canonicalInitialHaarCoefficient
    canonicalInitialHaarCharge
  rw [mFourier_freeInitialPhaseCharge]
  exact
    (canonicalFreeComplexInitialAmplitude_eq_coefficient_mul_unitPhase
      radius frequency phase mode).symm

/-- Exact cross-mode normal moment for the actual canonical FPUT
random-phase initialization. -/
theorem integral_twoPointProduct_canonicalFreeComplexInitialAmplitude
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (i j : Lattice.Site N) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      twoPointProduct
        (canonicalFreeComplexInitialAmplitude radius frequency phase i)
        (canonicalFreeComplexInitialAmplitude radius frequency phase j)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      if canonicalInitialHaarCharge i - canonicalInitialHaarCharge j = 0 then
        canonicalInitialHaarCoefficient radius frequency i *
          starRingEnd Complex
            (canonicalInitialHaarCoefficient radius frequency j) else 0 := by
  simpa only [fixedRadiusHaarAmplitude_eq_canonicalFreeComplexInitialAmplitude]
    using
      (integral_twoPointProduct_fixedRadiusHaarAmplitude
        (d := Lattice.Site N)
        (canonicalInitialHaarCoefficient radius frequency)
        canonicalInitialHaarCharge i j)

/-- Exact cross-mode fourth moment for the actual canonical FPUT
random-phase initialization.  This is charge balance, not Gaussian Wick
pairing, on every repeated-index sector. -/
theorem integral_fourPointProduct_canonicalFreeComplexInitialAmplitude
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (i j k l : Lattice.Site N) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      fourPointProduct
        (canonicalFreeComplexInitialAmplitude radius frequency phase i)
        (canonicalFreeComplexInitialAmplitude radius frequency phase j)
        (canonicalFreeComplexInitialAmplitude radius frequency phase k)
        (canonicalFreeComplexInitialAmplitude radius frequency phase l)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      if (canonicalInitialHaarCharge i - canonicalInitialHaarCharge j) +
          (canonicalInitialHaarCharge k - canonicalInitialHaarCharge l) = 0 then
        (canonicalInitialHaarCoefficient radius frequency i *
          starRingEnd Complex
            (canonicalInitialHaarCoefficient radius frequency j)) *
        (canonicalInitialHaarCoefficient radius frequency k *
          starRingEnd Complex
            (canonicalInitialHaarCoefficient radius frequency l)) else 0 := by
  simpa only [fixedRadiusHaarAmplitude_eq_canonicalFreeComplexInitialAmplitude]
    using
      (integral_fourPointProduct_fixedRadiusHaarAmplitude
        (d := Lattice.Site N)
        (canonicalInitialHaarCoefficient radius frequency)
        canonicalInitialHaarCharge i j k l)

/-- On the fully repeated sector the fixed-radius fourth moment has exactly
one surviving charge-balanced monomial. -/
theorem integral_fourPointProduct_canonicalFreeComplexInitialAmplitude_same
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real) (i : Lattice.Site N) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      fourPointProduct
        (canonicalFreeComplexInitialAmplitude radius frequency phase i)
        (canonicalFreeComplexInitialAmplitude radius frequency phase i)
        (canonicalFreeComplexInitialAmplitude radius frequency phase i)
        (canonicalFreeComplexInitialAmplitude radius frequency phase i)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      (canonicalInitialHaarCoefficient radius frequency i *
        starRingEnd Complex
          (canonicalInitialHaarCoefficient radius frequency i)) ^ 2 := by
  rw [integral_fourPointProduct_canonicalFreeComplexInitialAmplitude]
  simp [pow_two]

end

end ArchonPhysics.CanonicalFixedRadiusHaarMomentClosure

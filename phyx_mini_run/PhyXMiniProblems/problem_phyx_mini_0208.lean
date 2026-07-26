import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0208

open Dimension

/-!
# Resonant wavelengths of a string with one fixed and one free end

The primary figure shows a vibrating string of span `ℓ`.  Its left endpoint is
fixed.  Its right endpoint is attached to a ring that slides without friction
on a vertical pole, so the right endpoint is mechanically free in the
transverse direction.

The physical lengths and wave numbers below are unit-independent Physlib
quantities.  Real numbers occur only as scalar readouts in a selected coherent
unit system, as axial coordinates in that readout, and as dimensionless mode
numbers or phases.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A signed physical length, represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical spatial wave number, carrying inverse-length dimension. -/
abbrev WaveNumberQuantity : Type := Dimensionful (WithDim L𝓭⁻¹ ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a physical wave number in the inverse of a selected length unit. -/
def waveNumberReadout
    (unit : LengthUnit) (waveNumber : WaveNumberQuantity) : ℝ :=
  (waveNumber {UnitChoices.SI with length := unit}).val

/-! ## Apparatus and primary-figure data -/

/-- The endpoint labels printed in the primary figure. -/
inductive StringEndpoint where
  | fixedEnd
  | freeEnd
  deriving DecidableEq, Repr

/-- The mechanical attachment at an endpoint of the string. -/
inductive EndpointSupport where
  | fixedAnchor
  | slidingRingOnPole
  deriving DecidableEq, Repr

/-- Orientation of the pole that guides the sliding ring. -/
inductive PoleOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Friction model for the contact between the ring and its guiding pole. -/
inductive RingPoleContact where
  | frictionless
  | frictional
  deriving DecidableEq, Repr

/-!
Physical quantities and qualitative roles in the pictured apparatus.
`vibratingSpan` is the length denoted by `ℓ` in the figure.  Axial positions
are dimensionful; their scalar readouts will serve as inputs to a mode shape.
-/
structure FixedFreeStringSetup where
  vibratingSpan : LengthQuantity
  axialPosition : StringEndpoint → LengthQuantity
  endpointSupport : StringEndpoint → EndpointSupport
  ringEndpoint : StringEndpoint
  poleOrientation : PoleOrientation
  ringPoleContact : RingPoleContact

/-!
Data read directly from the primary figure and its physical description.
No resonant wavelength is specified here.  The equalities are required in
every selected length unit so they describe the physical endpoint geometry.
-/
structure MatchesPrimaryFigure (setup : FixedFreeStringSetup) : Prop where
  fixedEndSupport :
    setup.endpointSupport .fixedEnd = .fixedAnchor
  freeEndSupport :
    setup.endpointSupport .freeEnd = .slidingRingOnPole
  ringIsAtFreeEnd : setup.ringEndpoint = .freeEnd
  poleIsVertical : setup.poleOrientation = .vertical
  ringSlidesWithoutFriction : setup.ringPoleContact = .frictionless
  fixedEndAtOrigin :
    ∀ unit : LengthUnit,
      lengthReadout unit (setup.axialPosition .fixedEnd) = 0
  freeEndAtSpan :
    ∀ unit : LengthUnit,
      lengthReadout unit (setup.axialPosition .freeEnd) =
        lengthReadout unit setup.vibratingSpan

/-- Positivity of the nondegenerate physical string span. -/
structure HasPhysicalStringGeometry (setup : FixedFreeStringSetup) : Prop where
  spanPositive :
    ∀ unit : LengthUnit, 0 < lengthReadout unit setup.vibratingSpan

/-! ## Standing-wave witnesses and governing laws -/

/-!
Data witnessing one spatial standing-wave mode at a proposed wavelength.
The displacement function uses scalar coordinate and displacement readouts in
the selected length unit.  Its amplitude and wave number remain physical,
dimension-carrying quantities.
-/
structure StandingWaveMode
    (setup : FixedFreeStringSetup) (wavelength : LengthQuantity) where
  amplitude : LengthQuantity
  waveNumber : WaveNumberQuantity
  spatialDisplacementReadout : LengthUnit → ℝ → ℝ

/-!
Governing relations for a nontrivial fixed--free normal mode.

* A normal mode has a sinusoidal spatial profile.
* The fixed endpoint is a displacement node.
* The frictionless sliding ring gives the free endpoint zero spatial slope,
  i.e. a displacement antinode.
* Spatial wave number and wavelength obey `k λ = 2π`.

These fields contain no odd-quarter-wave formula and no mode number.
-/
structure SatisfiesFixedFreeStandingWaveLaws
    (setup : FixedFreeStringSetup)
    (wavelength : LengthQuantity)
    (mode : StandingWaveMode setup wavelength) : Prop where
  amplitudeNonzero :
    ∀ unit : LengthUnit, lengthReadout unit mode.amplitude ≠ 0
  waveNumberPositive :
    ∀ unit : LengthUnit, 0 < waveNumberReadout unit mode.waveNumber
  wavelengthPositive :
    ∀ unit : LengthUnit, 0 < lengthReadout unit wavelength
  harmonicSpatialProfile :
    ∀ (unit : LengthUnit) (axialCoordinate : ℝ),
      mode.spatialDisplacementReadout unit axialCoordinate =
        lengthReadout unit mode.amplitude *
          Real.sin
            (waveNumberReadout unit mode.waveNumber * axialCoordinate)
  fixedEndIsNode :
    ∀ unit : LengthUnit,
      mode.spatialDisplacementReadout unit
        (lengthReadout unit (setup.axialPosition .fixedEnd)) = 0
  freeEndHasZeroSlope :
    ∀ unit : LengthUnit,
      HasDerivAt (mode.spatialDisplacementReadout unit) 0
        (lengthReadout unit (setup.axialPosition .freeEnd))
  waveNumberWavelengthRelation :
    ∀ unit : LengthUnit,
      waveNumberReadout unit mode.waveNumber *
          lengthReadout unit wavelength = 2 * Real.pi

/-- A wavelength is resonant when a nontrivial fixed--free standing mode exists. -/
def IsResonantWavelength
    (setup : FixedFreeStringSetup) (wavelength : LengthQuantity) : Prop :=
  ∃ mode : StandingWaveMode setup wavelength,
    SatisfiesFixedFreeStandingWaveLaws setup wavelength mode

/-!
The fixed node and free zero-slope boundary quantize the phase accumulated
over the string to an odd multiple of `π / 2`.  This is an intermediate
conclusion derived from the boundary laws, not an assumed field.
-/
lemma fixedFree_phase_quantization
    (setup : FixedFreeStringSetup)
    (figure : MatchesPrimaryFigure setup)
    (physical : HasPhysicalStringGeometry setup)
    (wavelength : LengthQuantity)
    (mode : StandingWaveMode setup wavelength)
    (laws : SatisfiesFixedFreeStandingWaveLaws setup wavelength mode) :
    ∃ n : ℕ, 0 < n ∧
      ∀ unit : LengthUnit,
        waveNumberReadout unit mode.waveNumber *
            lengthReadout unit setup.vibratingSpan =
          (2 * (n : ℝ) - 1) * Real.pi / 2 := by
  have phase_invariant (unit₁ unit₂ : LengthUnit) :
      waveNumberReadout unit₁ mode.waveNumber *
          lengthReadout unit₁ setup.vibratingSpan =
        waveNumberReadout unit₂ mode.waveNumber *
          lengthReadout unit₂ setup.vibratingSpan := by
    let u₁ : UnitChoices := {UnitChoices.SI with length := unit₁}
    let u₂ : UnitChoices := {UnitChoices.SI with length := unit₂}
    have hk := congrArg WithDim.val (mode.waveNumber.2 u₁ u₂)
    have hℓ := congrArg WithDim.val (setup.vibratingSpan.2 u₁ u₂)
    change
      (mode.waveNumber u₁).val * (setup.vibratingSpan u₁).val =
        (mode.waveNumber u₂).val * (setup.vibratingSpan u₂).val
    rw [hk, hℓ]
    simp only [WithDim.smul_val, WithDim.dim_apply, NNReal.smul_def, smul_eq_mul]
    rw [UnitChoices.dimScale_of_inv_eq_swap]
    rw [mul_mul_mul_comm]
    rw [← NNReal.coe_mul, UnitChoices.dimScale_mul_symm]
    simp
  let baseUnit : LengthUnit := LengthUnit.meters
  have hprofile :
      mode.spatialDisplacementReadout baseUnit =
        fun x =>
          lengthReadout baseUnit mode.amplitude *
            Real.sin (waveNumberReadout baseUnit mode.waveNumber * x) := by
    funext x
    exact laws.harmonicSpatialProfile baseUnit x
  have hfree := laws.freeEndHasZeroSlope baseUnit
  rw [hprofile] at hfree
  have hlinear :
      HasDerivAt
        (fun x : ℝ => waveNumberReadout baseUnit mode.waveNumber * x)
        (waveNumberReadout baseUnit mode.waveNumber)
        (lengthReadout baseUnit (setup.axialPosition .freeEnd)) := by
    simpa using
      (hasDerivAt_id
        (lengthReadout baseUnit (setup.axialPosition .freeEnd))).const_mul
          (waveNumberReadout baseUnit mode.waveNumber)
  have hderiv :
      HasDerivAt
        (fun x =>
          lengthReadout baseUnit mode.amplitude *
            Real.sin (waveNumberReadout baseUnit mode.waveNumber * x))
        (lengthReadout baseUnit mode.amplitude *
          (Real.cos
              (waveNumberReadout baseUnit mode.waveNumber *
                lengthReadout baseUnit (setup.axialPosition .freeEnd)) *
            waveNumberReadout baseUnit mode.waveNumber))
        (lengthReadout baseUnit (setup.axialPosition .freeEnd)) := by
    exact hlinear.sin.const_mul (lengthReadout baseUnit mode.amplitude)
  have hproduct_zero :
      lengthReadout baseUnit mode.amplitude *
          (Real.cos
              (waveNumberReadout baseUnit mode.waveNumber *
                lengthReadout baseUnit (setup.axialPosition .freeEnd)) *
            waveNumberReadout baseUnit mode.waveNumber) =
        0 :=
    (hfree.unique hderiv).symm
  have hcos_free :
      Real.cos
          (waveNumberReadout baseUnit mode.waveNumber *
            lengthReadout baseUnit (setup.axialPosition .freeEnd)) =
        0 := by
    rcases mul_eq_zero.mp hproduct_zero with hAmplitude | hrest
    · exact (laws.amplitudeNonzero baseUnit hAmplitude).elim
    rcases mul_eq_zero.mp hrest with hcos | hWaveNumber
    · exact hcos
    · exact ((ne_of_gt (laws.waveNumberPositive baseUnit)) hWaveNumber).elim
  have hcos :
      Real.cos
          (waveNumberReadout baseUnit mode.waveNumber *
            lengthReadout baseUnit setup.vibratingSpan) =
        0 := by
    rw [← figure.freeEndAtSpan baseUnit]
    exact hcos_free
  obtain ⟨j, hj⟩ := Real.cos_eq_zero_iff.mp hcos
  have hphase :
      0 <
        waveNumberReadout baseUnit mode.waveNumber *
          lengthReadout baseUnit setup.vibratingSpan :=
    mul_pos (laws.waveNumberPositive baseUnit) (physical.spanPositive baseUnit)
  have hodd : 0 < 2 * (j : ℝ) + 1 := by
    rw [hj] at hphase
    nlinarith [Real.pi_pos]
  have hj_nonneg : 0 ≤ j := by
    by_contra hj_neg
    have hj_le : j ≤ -1 := by omega
    have hj_le_real : (j : ℝ) ≤ -1 := by exact_mod_cast hj_le
    linarith
  refine ⟨j.toNat + 1, by omega, ?_⟩
  intro unit
  calc
    waveNumberReadout unit mode.waveNumber *
        lengthReadout unit setup.vibratingSpan =
      waveNumberReadout baseUnit mode.waveNumber *
        lengthReadout baseUnit setup.vibratingSpan :=
      phase_invariant unit baseUnit
    _ = (2 * (j : ℝ) + 1) * Real.pi / 2 := hj
    _ = (2 * ((j.toNat + 1 : ℕ) : ℝ) - 1) * Real.pi / 2 := by
      have hj_cast : (j.toNat : ℝ) = (j : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hj_nonneg
      rw [Nat.cast_add, Nat.cast_one, hj_cast]
      ring

/-!
The resonant wavelengths are exactly

`λₙ = 4 ℓ / (2 n - 1)`, for positive natural mode numbers `n`.

Thus the theorem formalizes answer D while characterizing the entire resonant
spectrum, rather than baking a selected wavelength into the setup or laws.
-/
theorem resonantWavelengths_iff
    (setup : FixedFreeStringSetup)
    (figure : MatchesPrimaryFigure setup)
    (physical : HasPhysicalStringGeometry setup)
    (wavelength : LengthQuantity) :
    IsResonantWavelength setup wavelength ↔
      ∃ n : ℕ, 0 < n ∧
        ∀ unit : LengthUnit,
          lengthReadout unit wavelength =
            4 * lengthReadout unit setup.vibratingSpan /
              (2 * (n : ℝ) - 1) := by
  have phase_invariant
      (waveNumber : WaveNumberQuantity) (length : LengthQuantity)
      (unit₁ unit₂ : LengthUnit) :
      waveNumberReadout unit₁ waveNumber * lengthReadout unit₁ length =
        waveNumberReadout unit₂ waveNumber * lengthReadout unit₂ length := by
    let u₁ : UnitChoices := {UnitChoices.SI with length := unit₁}
    let u₂ : UnitChoices := {UnitChoices.SI with length := unit₂}
    have hk := congrArg WithDim.val (waveNumber.2 u₁ u₂)
    have hℓ := congrArg WithDim.val (length.2 u₁ u₂)
    change
      (waveNumber u₁).val * (length u₁).val =
        (waveNumber u₂).val * (length u₂).val
    rw [hk, hℓ]
    simp only [WithDim.smul_val, WithDim.dim_apply, NNReal.smul_def, smul_eq_mul]
    rw [UnitChoices.dimScale_of_inv_eq_swap]
    rw [mul_mul_mul_comm]
    rw [← NNReal.coe_mul, UnitChoices.dimScale_mul_symm]
    simp
  constructor
  · rintro ⟨mode, laws⟩
    obtain ⟨n, hn, hphase⟩ :=
      fixedFree_phase_quantization setup figure physical wavelength mode laws
    refine ⟨n, hn, ?_⟩
    intro unit
    have hn_real : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hodd : 0 < 2 * (n : ℝ) - 1 := by linarith
    apply mul_left_cancel₀ (ne_of_gt (laws.waveNumberPositive unit))
    rw [laws.waveNumberWavelengthRelation unit]
    field_simp [ne_of_gt hodd]
    nlinarith [hphase unit]
  · rintro ⟨n, hn, hwavelength⟩
    let baseUnit : LengthUnit := LengthUnit.meters
    let baseChoices : UnitChoices := {UnitChoices.SI with length := baseUnit}
    let waveNumber : WaveNumberQuantity :=
      CarriesDimension.toDimensionful baseChoices
        ⟨(2 * (n : ℝ) - 1) * Real.pi /
          (2 * lengthReadout baseUnit setup.vibratingSpan)⟩
    have hn_real : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hodd : 0 < 2 * (n : ℝ) - 1 := by linarith
    have hbaseSpan :
        0 < lengthReadout baseUnit setup.vibratingSpan :=
      physical.spanPositive baseUnit
    have hwaveNumberBase :
        waveNumberReadout baseUnit waveNumber =
          (2 * (n : ℝ) - 1) * Real.pi /
            (2 * lengthReadout baseUnit setup.vibratingSpan) := by
      simp [waveNumber, waveNumberReadout, baseChoices, baseUnit,
        CarriesDimension.toDimensionful_apply_apply]
    have hphaseBase :
        waveNumberReadout baseUnit waveNumber *
            lengthReadout baseUnit setup.vibratingSpan =
          (2 * (n : ℝ) - 1) * Real.pi / 2 := by
      rw [hwaveNumberBase]
      field_simp [ne_of_gt hbaseSpan]
    have hphase (unit : LengthUnit) :
        waveNumberReadout unit waveNumber *
            lengthReadout unit setup.vibratingSpan =
          (2 * (n : ℝ) - 1) * Real.pi / 2 :=
      (phase_invariant waveNumber setup.vibratingSpan unit baseUnit).trans hphaseBase
    let mode : StandingWaveMode setup wavelength :=
      { amplitude := setup.vibratingSpan
        waveNumber := waveNumber
        spatialDisplacementReadout := fun unit x =>
          lengthReadout unit setup.vibratingSpan *
            Real.sin (waveNumberReadout unit waveNumber * x) }
    refine ⟨mode, ?_⟩
    refine
      { amplitudeNonzero := ?_
        waveNumberPositive := ?_
        wavelengthPositive := ?_
        harmonicSpatialProfile := ?_
        fixedEndIsNode := ?_
        freeEndHasZeroSlope := ?_
        waveNumberWavelengthRelation := ?_ }
    · intro unit
      exact ne_of_gt (physical.spanPositive unit)
    · intro unit
      have hright :
          0 < (2 * (n : ℝ) - 1) * Real.pi / 2 :=
        div_pos (mul_pos hodd Real.pi_pos) (by norm_num)
      have hproduct :
          0 <
            waveNumberReadout unit waveNumber *
              lengthReadout unit setup.vibratingSpan := by
        rw [hphase unit]
        exact hright
      exact
        pos_of_mul_pos_left hproduct
          (le_of_lt (physical.spanPositive unit))
    · intro unit
      rw [hwavelength unit]
      exact
        div_pos
          (mul_pos (by norm_num) (physical.spanPositive unit))
          hodd
    · intro unit axialCoordinate
      rfl
    · intro unit
      simp [mode, figure.fixedEndAtOrigin unit]
    · intro unit
      have hlinear :
          HasDerivAt
            (fun x : ℝ => waveNumberReadout unit waveNumber * x)
            (waveNumberReadout unit waveNumber)
            (lengthReadout unit (setup.axialPosition .freeEnd)) := by
        simpa using
          (hasDerivAt_id
            (lengthReadout unit (setup.axialPosition .freeEnd))).const_mul
              (waveNumberReadout unit waveNumber)
      have hphaseFree :
          waveNumberReadout unit waveNumber *
              lengthReadout unit (setup.axialPosition .freeEnd) =
            (2 * (n : ℝ) - 1) * Real.pi / 2 := by
        rw [figure.freeEndAtSpan unit]
        exact hphase unit
      have hcos :
          Real.cos
              (waveNumberReadout unit waveNumber *
                lengthReadout unit (setup.axialPosition .freeEnd)) =
            0 := by
        rw [hphaseFree]
        apply Real.cos_eq_zero_iff.mpr
        refine ⟨(n : ℤ) - 1, ?_⟩
        push_cast
        ring
      have hderiv :
          HasDerivAt
            (fun x =>
              lengthReadout unit setup.vibratingSpan *
                Real.sin (waveNumberReadout unit waveNumber * x))
            (lengthReadout unit setup.vibratingSpan *
              (Real.cos
                  (waveNumberReadout unit waveNumber *
                    lengthReadout unit (setup.axialPosition .freeEnd)) *
                waveNumberReadout unit waveNumber))
            (lengthReadout unit (setup.axialPosition .freeEnd)) := by
        exact
          hlinear.sin.const_mul
            (lengthReadout unit setup.vibratingSpan)
      simpa [mode, hcos] using hderiv
    · intro unit
      rw [hwavelength unit]
      field_simp [ne_of_gt hodd]
      nlinarith [hphase unit]

end PhyXMiniProblems.ProblemPhyXMini0208

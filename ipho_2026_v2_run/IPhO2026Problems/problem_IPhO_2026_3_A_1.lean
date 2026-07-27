import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026 Problem 3, A.1

This file models the homogeneous isotropic paramagnetic torus shown in Fig. 3a.
All scalar equations below use SI readouts of Physlib dimensionful quantities.
The thin-torus and dense-winding approximations are represented by a single
uniform scalar magnitude for each toroidal field.
-/

noncomputable section

open Dimension

namespace IPhO2026Problems.IPhO2026_3_A_1

/-- A scalar length magnitude, retaining its physical dimension. -/
abbrev LengthMagnitude := Dimensionful (WithDim L𝓭 ℝ)

/-- A scalar cross-sectional area magnitude, retaining its physical dimension. -/
abbrev AreaMagnitude := Dimensionful (WithDim (L𝓭 * L𝓭) ℝ)

/-- A scalar volume magnitude, retaining its physical dimension. -/
abbrev VolumeMagnitude := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- The magnitude of an instantaneous electric current, with dimension charge/time. -/
abbrev ElectricCurrentMagnitude := Dimensionful (WithDim (C𝓭 / T𝓭) ℝ)

/-- The magnitude of `H` or `M`, with dimension current/length. -/
abbrev MagneticFieldStrengthMagnitude :=
  Dimensionful (WithDim ((C𝓭 / T𝓭) / L𝓭) ℝ)

/-- The magnitude of `B`, with its magnetic-flux-density dimension. -/
abbrev MagneticFluxDensityMagnitude :=
  Dimensionful (WithDim (M𝓭 / (C𝓭 * T𝓭)) ℝ)

/-- A magnetic permeability magnitude, including the vacuum permeability `μ₀`. -/
abbrev MagneticPermeabilityMagnitude :=
  Dimensionful (WithDim ((M𝓭 * L𝓭) / (C𝓭 * C𝓭)) ℝ)

/-- An energy magnitude, used only to record the problem's transfer sign convention. -/
abbrev EnergyMagnitude :=
  Dimensionful (WithDim ((M𝓭 * L𝓭 * L𝓭) / (T𝓭 * T𝓭)) ℝ)

/-- The numerical readout of a dimensionful scalar quantity in SI units. -/
def siValue {d : Dimension} (q : Dimensionful (WithDim d ℝ)) : ℝ :=
  (q UnitChoices.SI).val

/-- The official source labels the apparatus drawing as Fig. 3a. -/
def apparatusFigureLabel : String := "Fig. 3a"

/-- Whether energy crosses the system boundary into or out of the Pm-T. -/
inductive EnergyTransferDirection where
  | intoSystem
  | outOfSystem

/--
The source convention: work and heat entering the paramagnetic torus are
positive, while transfers leaving it are negative.
-/
def signedEnergySI (direction : EnergyTransferDirection) (magnitude : EnergyMagnitude) : ℝ :=
  match direction with
  | .intoSystem => siValue magnitude
  | .outOfSystem => -siValue magnitude

/--
The homogeneous isotropic paramagnetic torus and its Fig. 3a geometry.

`minorRadius` is the cross-sectional radius `r` marked by the diameter `2r` in
the figure. The explicit dimensionless bound records the approximation `r ≪ R`
without choosing an unsupported numerical tolerance.
-/
structure HomogeneousIsotropicParamagneticTorus where
  meanRadius : LengthMagnitude
  minorRadius : LengthMagnitude
  crossSectionArea : AreaMagnitude
  volume : VolumeMagnitude
  thinnessBound : ℝ
  meanRadius_pos : 0 < siValue meanRadius
  minorRadius_pos : 0 < siValue minorRadius
  crossSectionArea_pos : 0 < siValue crossSectionArea
  thinnessBound_pos : 0 < thinnessBound
  thinnessBound_lt_one : thinnessBound < 1
  thin_geometry : siValue minorRadius ≤ thinnessBound * siValue meanRadius
  volume_eq_meanCircumference_mul_area :
    siValue volume =
      (2 * Real.pi * siValue meanRadius) * siValue crossSectionArea

/--
The densely wound insulated wire. Its instantaneous current is represented by
its nonnegative magnitude, so no orientation branch is selected implicitly.
-/
structure DenseInsulatedWinding where
  turnCount : ℕ
  currentMagnitude : ElectricCurrentMagnitude
  turnCount_pos : 0 < turnCount
  currentMagnitude_nonneg : 0 ≤ siValue currentMagnitude

/--
The approximately uniform magnitudes of `H`, `B`, and `M` in the torus.
For the isotropic paramagnet, the nonnegative scalar `magnetization` is the
component along the same toroidal direction as `fieldStrength`.
-/
structure UniformToroidalMagneticState where
  fieldStrength : MagneticFieldStrengthMagnitude
  fluxDensity : MagneticFluxDensityMagnitude
  magnetization : MagneticFieldStrengthMagnitude
  fieldStrength_nonneg : 0 ≤ siValue fieldStrength
  fluxDensity_nonneg : 0 ≤ siValue fluxDensity
  magnetization_nonneg : 0 ≤ siValue magnetization

/-- The length `2πR` of the circular Ampèrian loop through the torus. -/
def meanLoopLengthSI (torus : HomogeneousIsotropicParamagneticTorus) : ℝ :=
  2 * Real.pi * siValue torus.meanRadius

/--
The scalar consequence of `B = μ₀ H + μ₀ M` for the common toroidal direction.
It is recorded as a governing law, not as a definition of any field.
-/
def ParamagneticConstitutiveLaw
    (state : UniformToroidalMagneticState)
    (vacuumPermeability : MagneticPermeabilityMagnitude) : Prop :=
  siValue state.fluxDensity =
    siValue vacuumPermeability * siValue state.fieldStrength +
      siValue vacuumPermeability * siValue state.magnetization

/--
Ampère's circuital law reduced using the approximately uniform toroidal field:
the circulation `H (2πR)` equals the enclosed free current `N I`.
-/
def ToroidalAmpereLaw
    (torus : HomogeneousIsotropicParamagneticTorus)
    (winding : DenseInsulatedWinding)
    (state : UniformToroidalMagneticState) : Prop :=
  siValue state.fieldStrength * meanLoopLengthSI torus =
    (winding.turnCount : ℝ) * siValue winding.currentMagnitude

/--
For the Fig. 3a paramagnetic torus, Ampère's law and
`V = (2πR) A` give `H = N I A / V`.
-/
theorem fieldStrength_eq_turns_current_area_div_volume
    (torus : HomogeneousIsotropicParamagneticTorus)
    (winding : DenseInsulatedWinding)
    (state : UniformToroidalMagneticState)
    (vacuumPermeability : MagneticPermeabilityMagnitude)
    (_vacuumPermeability_pos : 0 < siValue vacuumPermeability)
    (_constitutiveLaw : ParamagneticConstitutiveLaw state vacuumPermeability)
    (_ampereLaw : ToroidalAmpereLaw torus winding state) :
    siValue state.fieldStrength =
      (winding.turnCount : ℝ) * siValue winding.currentMagnitude *
        siValue torus.crossSectionArea / siValue torus.volume := by
  have hvolume_pos : 0 < siValue torus.volume := by
    rw [torus.volume_eq_meanCircumference_mul_area]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) torus.meanRadius_pos)
      torus.crossSectionArea_pos
  apply (eq_div_iff (ne_of_gt hvolume_pos)).2
  unfold ToroidalAmpereLaw at _ampereLaw
  calc
    siValue state.fieldStrength * siValue torus.volume =
        siValue state.fieldStrength *
          (meanLoopLengthSI torus * siValue torus.crossSectionArea) := by
      rw [torus.volume_eq_meanCircumference_mul_area]
      rfl
    _ = (siValue state.fieldStrength * meanLoopLengthSI torus) *
          siValue torus.crossSectionArea := by ring
    _ = ((winding.turnCount : ℝ) * siValue winding.currentMagnitude) *
          siValue torus.crossSectionArea := by rw [_ampereLaw]

end IPhO2026Problems.IPhO2026_3_A_1

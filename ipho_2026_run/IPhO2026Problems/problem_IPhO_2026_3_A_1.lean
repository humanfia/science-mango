import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 3, part A.1

This file models the homogeneous, isotropic paramagnetic torus of Figure 3a.
All scalar physical quantities are `Dimensionful` Physlib quantities.  The
closed-loop circulation in Ampère's law is kept as an explicit physical
readout because Physlib's available Ampère law is a differential vacuum-field
statement rather than the material-field circuital law used here.
-/

namespace IPhO2026Problems.IPhO2026_3_A_1

open Dimension UnitChoices

/-! ## Dimensions and physical scalar quantities -/

/-- The dimension of electric current, charge divided by time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- The dimension of magnetic field strength `H`, electric current per length. -/
def magneticFieldStrengthDimension : Dimension :=
  electricCurrentDimension * L𝓭⁻¹

/-- The dimension of vacuum permeability `μ₀`. -/
def vacuumPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- The dimension of magnetic flux density `B` (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A physical length, independent of a choice of units. -/
abbrev PhysicalLength := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical area. -/
abbrev PhysicalArea := Dimensionful (WithDim (L𝓭 * L𝓭) ℝ)

/-- A physical volume. -/
abbrev PhysicalVolume := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- The magnitude of an instantaneous electric current. -/
abbrev ElectricCurrentMagnitude :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- The magnitude of the material magnetic field strength `H`. -/
abbrev MagneticFieldStrengthMagnitude :=
  Dimensionful (WithDim magneticFieldStrengthDimension ℝ)

/-- The magnitude of the magnetization `M`, which has the same dimension as `H`. -/
abbrev MagnetizationMagnitude :=
  Dimensionful (WithDim magneticFieldStrengthDimension ℝ)

/-- The vacuum permeability `μ₀`. -/
abbrev VacuumPermeabilityMagnitude :=
  Dimensionful (WithDim vacuumPermeabilityDimension ℝ)

/-- The magnitude of the magnetic flux density `B`. -/
abbrev MagneticFluxDensityMagnitude :=
  Dimensionful (WithDim magneticFluxDensityDimension ℝ)

/-- The numerical readout of a dimensionful real scalar in coherent SI units. -/
noncomputable def siReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity SI).val

/-! ## Figure 3a objects and data -/

/--
The torus shown in Figure 3a.

`meanRadius`, `crossSectionRadius`, `crossSectionArea`, and `volume` represent
the labels `R`, `r`, `A`, and `V`.  `meanAmperePathLength` is the length of the
central circular curve `C` used in Ampère's circuital law.
-/
structure ParamagneticTorus where
  meanRadius : PhysicalLength
  crossSectionRadius : PhysicalLength
  crossSectionArea : PhysicalArea
  volume : PhysicalVolume
  meanAmperePathLength : PhysicalLength
  materialIsHomogeneous : Prop
  materialIsIsotropic : Prop
  materialIsParamagnetic : Prop

/-- The material qualifications stated for the torus. -/
def HasStatedMaterialProperties (torus : ParamagneticTorus) : Prop :=
  torus.materialIsHomogeneous ∧
    torus.materialIsIsotropic ∧
    torus.materialIsParamagnetic

/--
The positive geometric readouts and the three Figure 3a relations
`ℓ = 2πR`, `A = πr²`, and `V = Aℓ`.
-/
def HasFigure3aGeometry (torus : ParamagneticTorus) : Prop :=
  0 < siReadout torus.meanRadius ∧
    0 < siReadout torus.crossSectionRadius ∧
    0 < siReadout torus.crossSectionArea ∧
    0 < siReadout torus.volume ∧
    siReadout torus.meanAmperePathLength =
      2 * Real.pi * siReadout torus.meanRadius ∧
    siReadout torus.crossSectionArea =
      Real.pi * siReadout torus.crossSectionRadius ^ 2 ∧
    siReadout torus.volume =
      siReadout torus.crossSectionArea *
        siReadout torus.meanAmperePathLength

/--
An explicit thin-torus approximation: `r ≤ ε R`, for a positive
dimensionless tolerance `ε < 1`.
-/
def IsThinToroidAtScale (torus : ParamagneticTorus) (ε : ℝ) : Prop :=
  0 < ε ∧
    ε < 1 ∧
    siReadout torus.crossSectionRadius ≤
      ε * siReadout torus.meanRadius

/-- The insulated, densely wound conducting wire shown in Figure 3a. -/
structure ToroidalWinding where
  turnCount : ℕ
  wireIsInsulated : Prop
  windingIsDense : Prop
  connectedToExternalVoltageSource : Prop
  ohmicHeatingIsNegligible : Prop

/-- The winding qualifications stated in the source and Figure 3a. -/
def HasStatedWindingProperties (winding : ToroidalWinding) : Prop :=
  0 < winding.turnCount ∧
    winding.wireIsInsulated ∧
    winding.windingIsDense ∧
    winding.connectedToExternalVoltageSource ∧
    winding.ohmicHeatingIsNegligible

/-- The sign convention used for work and heat transfer. -/
inductive EnergyTransferSignConvention
  | positiveIntoTorus
  | positiveOutOfTorus
  deriving DecidableEq

/-! ## Magnetic state and governing laws -/

/--
The instantaneous uniform-field state.  The scalar fields are the magnitudes
of the approximately uniform vectors `H`, `B`, and `M`.
-/
structure ToroidalMagneticState where
  instantaneousCurrent : ElectricCurrentMagnitude
  fieldStrength : MagneticFieldStrengthMagnitude
  fluxDensity : MagneticFluxDensityMagnitude
  magnetization : MagnetizationMagnitude
  fieldStrengthApproximatelyUniform : Prop
  fluxDensityApproximatelyUniform : Prop
  magnetizationApproximatelyUniform : Prop
  magnetizationParallelToFieldStrength : Prop

/-- The uniformity and alignment assumptions justified by `r ≪ R`. -/
def UsesUniformParallelFieldApproximation
    (state : ToroidalMagneticState) : Prop :=
  state.fieldStrengthApproximatelyUniform ∧
    state.fluxDensityApproximatelyUniform ∧
    state.magnetizationApproximatelyUniform ∧
    state.magnetizationParallelToFieldStrength

/-- All quantities designated as magnitudes have nonnegative SI readouts. -/
def HasNonnegativeMagnitudes (state : ToroidalMagneticState) : Prop :=
  0 ≤ siReadout state.instantaneousCurrent ∧
    0 ≤ siReadout state.fieldStrength ∧
    0 ≤ siReadout state.fluxDensity ∧
    0 ≤ siReadout state.magnetization

/--
The constitutive relation `B = μ₀ H + μ₀ M` on the parallel scalar
magnitudes, together with positivity of the vacuum permeability.
-/
def SatisfiesParamagneticConstitutiveLaw
    (μ₀ : VacuumPermeabilityMagnitude)
    (state : ToroidalMagneticState) : Prop :=
  0 < siReadout μ₀ ∧
    siReadout state.fluxDensity =
      siReadout μ₀ * siReadout state.fieldStrength +
        siReadout μ₀ * siReadout state.magnetization

/--
The two current-dimensional quantities in Ampère's circuital law:
the circulation `∮_C H · dℓ` and the free current linked by `C`.
-/
structure ToroidalAmpereReadouts where
  fieldCirculation : ElectricCurrentMagnitude
  linkedFreeCurrent : ElectricCurrentMagnitude

/--
Ampère's circuital law and its two thin-torus evaluations.

The first conjunct is `∮_C H · dℓ = I_C`.  The second uses uniform `H` to
evaluate the circulation as `Hℓ`.  The third says that the curve links all
`N` turns, so its net free current is `NI`.
-/
def SatisfiesToroidalAmpereCircuitalLaw
    (torus : ParamagneticTorus)
    (winding : ToroidalWinding)
    (state : ToroidalMagneticState)
    (readouts : ToroidalAmpereReadouts) : Prop :=
  siReadout readouts.fieldCirculation =
      siReadout readouts.linkedFreeCurrent ∧
    siReadout readouts.fieldCirculation =
      siReadout state.fieldStrength *
        siReadout torus.meanAmperePathLength ∧
    siReadout readouts.linkedFreeCurrent =
      (winding.turnCount : ℝ) *
        siReadout state.instantaneousCurrent

/--
For the homogeneous thin torus of Figure 3a, Ampère's circuital law gives

`H = N I A / V`.

This is the formalization target for IPhO 2026 problem 3, part A.1.
-/
theorem fieldStrength_eq_turns_current_area_div_volume
    (torus : ParamagneticTorus)
    (winding : ToroidalWinding)
    (state : ToroidalMagneticState)
    (μ₀ : VacuumPermeabilityMagnitude)
    (ampereReadouts : ToroidalAmpereReadouts)
    (ε : ℝ)
    (signConvention : EnergyTransferSignConvention)
    (h_material : HasStatedMaterialProperties torus)
    (h_geometry : HasFigure3aGeometry torus)
    (h_thin_torus : IsThinToroidAtScale torus ε)
    (h_winding : HasStatedWindingProperties winding)
    (h_uniform_fields : UsesUniformParallelFieldApproximation state)
    (h_nonnegative_magnitudes : HasNonnegativeMagnitudes state)
    (h_constitutive :
      SatisfiesParamagneticConstitutiveLaw μ₀ state)
    (h_ampere :
      SatisfiesToroidalAmpereCircuitalLaw
        torus winding state ampereReadouts)
    (h_sign_convention :
      signConvention = EnergyTransferSignConvention.positiveIntoTorus) :
    siReadout state.fieldStrength =
      (winding.turnCount : ℝ) *
        siReadout state.instantaneousCurrent *
        siReadout torus.crossSectionArea /
        siReadout torus.volume := by
  rcases h_geometry with
    ⟨_, _, _, h_volume_pos, _, _, h_volume⟩
  rcases h_ampere with
    ⟨h_circulation_eq_linked, h_circulation_eval, h_linked_current⟩
  have h_ampere_scalar :
      siReadout state.fieldStrength *
          siReadout torus.meanAmperePathLength =
        (winding.turnCount : ℝ) *
          siReadout state.instantaneousCurrent := by
    calc
      siReadout state.fieldStrength *
            siReadout torus.meanAmperePathLength =
          siReadout ampereReadouts.fieldCirculation :=
        h_circulation_eval.symm
      _ = siReadout ampereReadouts.linkedFreeCurrent :=
        h_circulation_eq_linked
      _ = (winding.turnCount : ℝ) *
            siReadout state.instantaneousCurrent :=
        h_linked_current
  apply (eq_div_iff h_volume_pos.ne').2
  rw [h_volume]
  calc
    siReadout state.fieldStrength *
          (siReadout torus.crossSectionArea *
            siReadout torus.meanAmperePathLength) =
        (siReadout state.fieldStrength *
            siReadout torus.meanAmperePathLength) *
          siReadout torus.crossSectionArea := by
      ring
    _ = (winding.turnCount : ℝ) *
          siReadout state.instantaneousCurrent *
          siReadout torus.crossSectionArea := by
      rw [h_ampere_scalar]

end IPhO2026Problems.IPhO2026_3_A_1

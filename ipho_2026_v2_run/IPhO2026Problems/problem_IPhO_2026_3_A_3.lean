import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Energy

/-!
# IPhO 2026 Problem 3 A.3

This file models the infinitesimal work balance for the homogeneous,
isotropic paramagnetic torus in Figure 3a.  The fields are uniform scalar
components along one common toroidal orientation.  Finite state values are
nonnegative magnitudes, while `dH`, `dB`, and `dM` are signed infinitesimal
changes.
-/

namespace IPhO2026Problems
namespace Problem3A3

open Dimension

/-! ## Dimensionful quantities used by the model -/

/-- Length, used for the radii `R` and `r`. -/
abbrev Length := Dimensionful (WithDim L𝓭 ℝ)

/-- Volume, with dimension `L³`. -/
abbrev Volume := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Cross-sectional area, with dimension `L²`. -/
abbrev Area := Dimensionful (WithDim (L𝓭 * L𝓭) ℝ)

/-- Electric current, with dimension charge/time. -/
abbrev ElectricCurrent := Dimensionful (WithDim (C𝓭 * T𝓭⁻¹) ℝ)

/-- Magnetic field strength `H`, with SI unit A/m. -/
abbrev MagneticFieldStrength :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- Magnetization `M`, which has the same dimension as `H`. -/
abbrev Magnetization :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- Magnetic flux density `B`, with SI unit tesla. -/
abbrev MagneticFluxDensity :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * C𝓭⁻¹) ℝ)

/-- Vacuum permeability `μ₀`, with SI dimension mass·length/charge². -/
abbrev VacuumPermeability :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹) ℝ)

/-- Work/energy, grounded by Physlib's dimensionful energy type. -/
abbrev Energy := DimEnergy

/-- The numerical value of a dimensionful real quantity in SI units. -/
noncomputable def siValue {d : Dimension} (q : Dimensionful (WithDim d ℝ)) : ℝ :=
  (q.1 UnitChoices.SI).val

/-- Construct a dimensionful energy from a numerical value in joules. -/
noncomputable def energyFromSI (x : ℝ) : Energy :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨x⟩

/-- Evaluation in SI is injective on quantities of any fixed dimension. -/
theorem dimensionful_ext_si {d : Dimension}
    {x y : Dimensionful (WithDim d ℝ)}
    (h : siValue x = siValue y) :
    x = y := by
  apply (CarriesDimension.toDimensionful UnitChoices.SI).symm.injective
  apply WithDim.ext
  exact h

/-- `energyFromSI` has the prescribed numerical value in joules. -/
theorem siValue_energyFromSI (x : ℝ) :
    siValue (energyFromSI x) = x := by
  simp [siValue, energyFromSI,
    CarriesDimension.toDimensionful_apply_apply]

/-! ## Figure and sign data -/

/-- Choice of the common positive direction around the torus. -/
inductive ToroidalOrientation where
  | clockwise
  | counterclockwise
  deriving DecidableEq

/-- Sign convention for signed work increments. -/
inductive WorkSignConvention where
  | positiveIntoSystem
  | positiveOutOfSystem
  deriving DecidableEq

/--
The homogeneous isotropic paramagnetic torus and winding in Figure 3a.
The field entries are uniform components along `toroidalOrientation`.
-/
structure TorusData where
  /-- Mean radius labelled `R` in Figure 3a. -/
  meanRadiusR : Length
  /-- Minor/cross-sectional radius labelled `r` in Figure 3a. -/
  minorRadiusr : Length
  /-- Torus volume labelled `V`. -/
  volumeV : Volume
  /-- Cross-sectional area labelled `A`. -/
  crossSectionAreaA : Area
  /-- Total number of dense winding turns, labelled `N`. -/
  turnCountN : ℕ
  /-- Instantaneous current in the insulated wire, labelled `I`. -/
  currentI : ElectricCurrent
  /-- Vacuum permeability `μ₀`. -/
  vacuumPermeabilityMu0 : VacuumPermeability
  /-- Approximately uniform magnetic field-strength magnitude `H`. -/
  fieldStrengthH : MagneticFieldStrength
  /-- Approximately uniform magnetic flux-density magnitude `B`. -/
  fluxDensityB : MagneticFluxDensity
  /-- Approximately uniform magnetization magnitude `M`, parallel to `H`. -/
  magnetizationM : Magnetization
  /--
  Dimensionless tolerance that makes the approximation `r ≪ R`
  quantitative.
  -/
  thinnessRatio : ℝ
  /-- The common positive direction used for `H`, `B`, and `M`. -/
  toroidalOrientation : ToroidalOrientation
  /-- Convention used for every signed work increment below. -/
  workSignConvention : WorkSignConvention

/-- Signed infinitesimal field changes used in A.3. -/
structure FieldIncrements where
  /-- Signed change `dH`. -/
  dH : MagneticFieldStrength
  /-- Signed change `dB` in the actual paramagnetic torus. -/
  dB : MagneticFluxDensity
  /-- Signed change `dM`. -/
  dM : Magnetization
  /-- Signed change `dB_vac = μ₀ dH` for the comparison vacuum core. -/
  dBVac : MagneticFluxDensity

/--
Signed infinitesimal work transfers.  Under the required convention, a
positive value denotes energy entering the named recipient.
-/
structure WorkIncrements where
  /-- Work `dW_emf` supplied by the external voltage source. -/
  sourceWorkdWemf : Energy
  /-- Comparison work `dW_vac` for a vacuum-core torus. -/
  vacuumCoreWorkdWvac : Energy
  /-- Work `dW` done on the paramagnetic material. -/
  materialWorkdW : Energy
  /-- Parasitic work deposited as heat in the low-resistance wire. -/
  wireHeatingWork : Energy

/-! ## Governing laws and reusable previous-part result -/

/--
All assumptions used to derive A.3.  In particular, this interface contains
the work decomposition and the vacuum comparison, but does not contain the
requested formula for `materialWorkdW`.
-/
structure Assumptions
    (data : TorusData) (changes : FieldIncrements) (works : WorkIncrements) : Prop where
  /-- The problem's convention is that work entering the torus is positive. -/
  signConvention :
    data.workSignConvention = WorkSignConvention.positiveIntoSystem
  meanRadius_positive : 0 < siValue data.meanRadiusR
  minorRadius_positive : 0 < siValue data.minorRadiusr
  volume_positive : 0 < siValue data.volumeV
  area_positive : 0 < siValue data.crossSectionAreaA
  turnCount_positive : 0 < data.turnCountN
  current_nonnegative : 0 ≤ siValue data.currentI
  vacuumPermeability_positive : 0 < siValue data.vacuumPermeabilityMu0
  fieldStrength_nonnegative : 0 ≤ siValue data.fieldStrengthH
  fluxDensity_nonnegative : 0 ≤ siValue data.fluxDensityB
  magnetization_nonnegative : 0 ≤ siValue data.magnetizationM
  thinnessRatio_positive : 0 < data.thinnessRatio
  thinnessRatio_lt_one : data.thinnessRatio < 1
  /-- Quantitative carrier of the approximation `r ≪ R`. -/
  thinTorus :
    siValue data.minorRadiusr ≤
      data.thinnessRatio * siValue data.meanRadiusR
  /-- Figure geometry: `V = (2πR) A`. -/
  torusVolumeGeometry :
    siValue data.volumeV =
      (2 * Real.pi * siValue data.meanRadiusR) *
        siValue data.crossSectionAreaA
  /-- Ampère's law for the mean circular path through the dense winding. -/
  ampereLaw :
    siValue data.fieldStrengthH *
        (2 * Real.pi * siValue data.meanRadiusR) =
      (data.turnCountN : ℝ) * siValue data.currentI
  /-- Static constitutive law `B = μ₀ (H + M)`. -/
  constitutiveLaw :
    siValue data.fluxDensityB =
      siValue data.vacuumPermeabilityMu0 *
        (siValue data.fieldStrengthH + siValue data.magnetizationM)
  /-- Differential constitutive law `dB = μ₀ (dH + dM)`. -/
  differentialConstitutiveLaw :
    siValue changes.dB =
      siValue data.vacuumPermeabilityMu0 *
        (siValue changes.dH + siValue changes.dM)
  /-- For the comparison vacuum core, `dB_vac = μ₀ dH`. -/
  vacuumCoreIncrementLaw :
    siValue changes.dBVac =
      siValue data.vacuumPermeabilityMu0 * siValue changes.dH
  /--
  Reusable conclusion of A.2, included directly rather than imported from
  another problem file: `dW_emf = V H dB`.
  -/
  previousPartSourceWork :
    siValue works.sourceWorkdWemf =
      siValue data.volumeV * siValue data.fieldStrengthH *
        siValue changes.dB
  /-- The same source-work law applied to the vacuum-core comparison. -/
  vacuumCoreWorkLaw :
    siValue works.vacuumCoreWorkdWvac =
      siValue data.volumeV * siValue data.fieldStrengthH *
        siValue changes.dBVac
  /-- The voltage-source work is divided into vacuum and material work. -/
  sourceWorkSplit :
    siValue works.sourceWorkdWemf =
      siValue works.vacuumCoreWorkdWvac +
        siValue works.materialWorkdW
  /-- The wire resistance is negligible, so its Joule-heating work vanishes. -/
  negligibleWireHeating :
    siValue works.wireHeatingWork = 0

/-! ## A.3 target and its SI bridge -/

/--
Scalar bridge for the A.3 subtraction: the material-work value in joules is
`μ₀ V H dM`.
-/
theorem materialWork_siValue_eq
    (data : TorusData) (changes : FieldIncrements) (works : WorkIncrements)
    (laws : Assumptions data changes works) :
    siValue works.materialWorkdW =
      siValue data.vacuumPermeabilityMu0 *
        siValue data.volumeV *
        siValue data.fieldStrengthH *
        siValue changes.dM := by
  have hsplit := laws.sourceWorkSplit
  rw [laws.previousPartSourceWork, laws.vacuumCoreWorkLaw] at hsplit
  rw [laws.differentialConstitutiveLaw,
    laws.vacuumCoreIncrementLaw] at hsplit
  ring_nf at hsplit ⊢
  linarith

/--
After subtracting the vacuum-core contribution, the work done on the
paramagnetic material is `dW = μ₀ V H dM`.
-/
theorem materialWork_eq_mu0_volume_H_dM
    (data : TorusData) (changes : FieldIncrements) (works : WorkIncrements)
    (laws : Assumptions data changes works) :
    works.materialWorkdW =
      energyFromSI
        (siValue data.vacuumPermeabilityMu0 *
          siValue data.volumeV *
          siValue data.fieldStrengthH *
          siValue changes.dM) := by
  apply dimensionful_ext_si
  rw [siValue_energyFromSI]
  exact materialWork_siValue_eq data changes works laws

end Problem3A3
end IPhO2026Problems

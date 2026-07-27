import Mathlib
import Physlib.Units.WithDim.Pressure

/-!
# IPhO 2026 experimental problem 4, part A.1

The sealed air column is treated as an ideal gas.  Figure 17 supplies the
inner-cylinder geometry, propylene glycol is filled to `4.5 cm`, and the
ambient air density is `1.12 kg m⁻³`.  The dimensionful quantities below use
Physlib's unit-dependent quantity interface; all scalar equations are their
explicit SI readouts.
-/

noncomputable section

open Dimension

namespace IPhO2026Problems
namespace Problem4A1

/-- A length carrying Physlib's length dimension. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 ^ 3) ℝ)

/-- A mass carrying Physlib's mass dimension. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 ℝ)

/-- An absolute temperature carrying Physlib's temperature dimension. -/
abbrev TemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 ℝ)

/-- A mass density carrying dimension `M L⁻³`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * (L𝓭 ^ 3)⁻¹) ℝ)

/-- The numerical value of a dimensionful real quantity in SI units. -/
def siValue {d : Dimension} (q : Dimensionful (WithDim d ℝ)) : ℝ :=
  (q UnitChoices.SI).val

/-- Amount of substance, represented by its nonnegative scalar readout in moles.

Physlib's current five-base-dimension system has no amount-of-substance
dimension, so this is kept distinct from dimensionless real numbers.
-/
structure AmountOfSubstance where
  moles : ℝ
  moles_nonnegative : 0 ≤ moles

/-- A nonnegative experimental estimate of the number of molecules. -/
structure MoleculePopulation where
  estimatedCount : ℝ
  count_nonnegative : 0 ≤ estimatedCount

/-- A scalar reading reported as `central ± uncertainty`. -/
structure ScalarMeasurement where
  central : ℝ
  uncertainty : ℝ
  uncertainty_nonnegative : 0 ≤ uncertainty

namespace ScalarMeasurement

/-- The usual absolute-error semantics of a `central ± uncertainty` report. -/
def Covers (reading : ScalarMeasurement) (actual : ℝ) : Prop :=
  |actual - reading.central| ≤ reading.uncertainty

/-- Lower endpoint of the reported error interval. -/
def lower (reading : ScalarMeasurement) : ℝ :=
  reading.central - reading.uncertainty

/-- Upper endpoint of the reported error interval. -/
def upper (reading : ScalarMeasurement) : ℝ :=
  reading.central + reading.uncertainty

end ScalarMeasurement

/-- The three quantities reported in the official sample solution.

The units of the fields are respectively grams, millimoles, and `10²¹`
molecules.
-/
structure InventoryReport where
  massGrams : ScalarMeasurement
  amountMillimoles : ScalarMeasurement
  moleculesInTenTo21 : ScalarMeasurement

/-- The recorded official sample, including all three reported uncertainties. -/
def officialSample : InventoryReport where
  massGrams := ⟨0.94, 0.02, by norm_num⟩
  amountMillimoles := ⟨3.24, 0.7, by norm_num⟩
  moleculesInTenTo21 := ⟨1.95, 0.05, by norm_num⟩

/-- Figure 17 labels needed to calculate the cylindrical confined-air volume. -/
structure Figure17Geometry where
  innerCylinderDiameter : LengthQuantity
  innerCylinderUsableHeight : LengthQuantity
  glycolFillHeight : LengthQuantity
  confinedAirHeight : LengthQuantity
  confinedAirVolume : VolumeQuantity

/-- The geometric interpretation of Figure 17 and the prescribed `h = 4.5 cm`.

The equations are stated on SI readouts, so the right-hand volume is in cubic
metres.
-/
def Figure17GeometryLaw (g : Figure17Geometry) : Prop :=
  0 < siValue g.innerCylinderDiameter ∧
  0 ≤ siValue g.glycolFillHeight ∧
  0 < siValue g.confinedAirHeight ∧
  siValue g.glycolFillHeight = 0.045 ∧
  siValue g.confinedAirHeight =
    siValue g.innerCylinderUsableHeight - siValue g.glycolFillHeight ∧
  siValue g.confinedAirVolume =
    Real.pi * (siValue g.innerCylinderDiameter / 2) ^ 2 *
      siValue g.confinedAirHeight

/-- The physical inventory and thermodynamic state of the sealed air column CA. -/
structure ConfinedAirColumnState where
  mass : MassQuantity
  amount : AmountOfSubstance
  molecules : MoleculePopulation
  volume : VolumeQuantity
  pressure : DimPressure
  temperature : TemperatureQuantity
  ambientAirDensity : MassDensityQuantity

/-- The two valves explicitly named in the experimental procedure. -/
inductive ValveLabel
  | D
  | E
  deriving DecidableEq

/-- The isochoric heating procedure after valves D and E are closed.

Time is only a trace parameter here; the subquestion uses the fixed-volume
consequence, not a choice of time unit.
-/
structure IsochoricApparatusRun where
  state : ConfinedAirColumnState
  geometry : Figure17Geometry
  pressureTrace : ℝ → DimPressure
  temperatureTrace : ℝ → TemperatureQuantity
  volumeTrace : ℝ → VolumeQuantity
  valveClosed : ValveLabel → Bool
  valveDClosed : valveClosed .D = true
  valveEClosed : valveClosed .E = true
  volumeFixed : ∀ t : ℝ, volumeTrace t = state.volume
  stateVolumeFromFigure : state.volume = geometry.confinedAirVolume

/-- Governing physical laws for the CA inventory.

`gasConstantSI` has scalar unit `J mol⁻¹ K⁻¹`, and
`avogadroPerMole` has scalar unit `molecules mol⁻¹`.  These dimensions cannot
currently be expressed by Physlib because amount of substance is not among its
base dimensions.
-/
structure AirInventoryLaws
    (s : ConfinedAirColumnState) (gasConstantSI avogadroPerMole : ℝ) : Prop where
  mass_from_density :
    siValue s.mass = siValue s.ambientAirDensity * siValue s.volume
  ideal_gas :
    siValue s.pressure * siValue s.volume =
      s.amount.moles * gasConstantSI * siValue s.temperature
  molecules_from_amount :
    s.molecules.estimatedCount = s.amount.moles * avogadroPerMole

/-- The ambient-density datum printed in the problem statement. -/
def AmbientDensityReadout (s : ConfinedAirColumnState) : Prop :=
  siValue s.ambientAirDensity = 1.12

/-- Exact symbolic determination of mass, amount, and molecule population.

This conclusion is not a field of `AirInventoryLaws`: it substitutes the
Figure 17 cylinder volume and algebraically solves the ideal-gas and Avogadro
relations.
-/
theorem determineConfinedAirInventory
    (run : IsochoricApparatusRun)
    (gasConstantSI avogadroPerMole : ℝ)
    (hgeometry : Figure17GeometryLaw run.geometry)
    (hlaws : AirInventoryLaws run.state gasConstantSI avogadroPerMole)
    (hgas : gasConstantSI ≠ 0)
    (htemperature : siValue run.state.temperature ≠ 0) :
    siValue run.state.mass =
        siValue run.state.ambientAirDensity *
          (Real.pi * (siValue run.geometry.innerCylinderDiameter / 2) ^ 2 *
            siValue run.geometry.confinedAirHeight) ∧
      run.state.amount.moles =
        (siValue run.state.pressure * siValue run.state.volume) /
          (gasConstantSI * siValue run.state.temperature) ∧
      run.state.molecules.estimatedCount =
        ((siValue run.state.pressure * siValue run.state.volume) /
          (gasConstantSI * siValue run.state.temperature)) * avogadroPerMole := by
  sorry

/-- Uncertain scalar inputs used for interval propagation.

Length fields are in metres, density in `kg m⁻³`, pressure in pascals, and
temperature in kelvin.
-/
structure ExperimentalInputReadouts where
  diameterMeters : ScalarMeasurement
  usableHeightMeters : ScalarMeasurement
  glycolHeightMeters : ScalarMeasurement
  densityKgPerM3 : ScalarMeasurement
  pressurePa : ScalarMeasurement
  temperatureK : ScalarMeasurement

/-- The readout intervals contain the actual SI components of the apparatus. -/
def InputReadoutsCover
    (run : IsochoricApparatusRun) (r : ExperimentalInputReadouts) : Prop :=
  r.diameterMeters.Covers (siValue run.geometry.innerCylinderDiameter) ∧
  r.usableHeightMeters.Covers (siValue run.geometry.innerCylinderUsableHeight) ∧
  r.glycolHeightMeters.Covers (siValue run.geometry.glycolFillHeight) ∧
  r.densityKgPerM3.Covers (siValue run.state.ambientAirDensity) ∧
  r.pressurePa.Covers (siValue run.state.pressure) ∧
  r.temperatureK.Covers (siValue run.state.temperature)

/-- Positivity conditions needed for monotone interval propagation. -/
structure ValidInputReadouts
    (r : ExperimentalInputReadouts) (gasConstantSI avogadroPerMole : ℝ) : Prop where
  diameter_lower_nonnegative : 0 ≤ r.diameterMeters.lower
  air_height_lower_nonnegative :
    0 ≤ r.usableHeightMeters.lower - r.glycolHeightMeters.upper
  density_lower_nonnegative : 0 ≤ r.densityKgPerM3.lower
  pressure_lower_nonnegative : 0 ≤ r.pressurePa.lower
  temperature_lower_positive : 0 < r.temperatureK.lower
  gas_constant_positive : 0 < gasConstantSI
  avogadro_nonnegative : 0 ≤ avogadroPerMole

/-- Lower volume bound obtained from the cylinder readout intervals. -/
def propagatedVolumeLower (r : ExperimentalInputReadouts) : ℝ :=
  Real.pi * (r.diameterMeters.lower / 2) ^ 2 *
    (r.usableHeightMeters.lower - r.glycolHeightMeters.upper)

/-- Upper volume bound obtained from the cylinder readout intervals. -/
def propagatedVolumeUpper (r : ExperimentalInputReadouts) : ℝ :=
  Real.pi * (r.diameterMeters.upper / 2) ^ 2 *
    (r.usableHeightMeters.upper - r.glycolHeightMeters.lower)

/-- Mass interval obtained by multiplying the density and volume intervals. -/
def propagatedMassLower (r : ExperimentalInputReadouts) : ℝ :=
  r.densityKgPerM3.lower * propagatedVolumeLower r

def propagatedMassUpper (r : ExperimentalInputReadouts) : ℝ :=
  r.densityKgPerM3.upper * propagatedVolumeUpper r

/-- Amount interval obtained from `n = PV/(RT)`. -/
def propagatedAmountLower (r : ExperimentalInputReadouts) (gasConstantSI : ℝ) : ℝ :=
  r.pressurePa.lower * propagatedVolumeLower r /
    (gasConstantSI * r.temperatureK.upper)

def propagatedAmountUpper (r : ExperimentalInputReadouts) (gasConstantSI : ℝ) : ℝ :=
  r.pressurePa.upper * propagatedVolumeUpper r /
    (gasConstantSI * r.temperatureK.lower)

/-- The propagated inventory interval, including the Avogadro conversion. -/
def InventoryInPropagatedBounds
    (s : ConfinedAirColumnState) (r : ExperimentalInputReadouts)
    (gasConstantSI avogadroPerMole : ℝ) : Prop :=
  propagatedMassLower r ≤ siValue s.mass ∧
  siValue s.mass ≤ propagatedMassUpper r ∧
  propagatedAmountLower r gasConstantSI ≤ s.amount.moles ∧
  s.amount.moles ≤ propagatedAmountUpper r gasConstantSI ∧
  propagatedAmountLower r gasConstantSI * avogadroPerMole ≤
    s.molecules.estimatedCount ∧
  s.molecules.estimatedCount ≤
    propagatedAmountUpper r gasConstantSI * avogadroPerMole

/-- Propagation of the input readout uncertainties to `m`, `n`, and `N`. -/
theorem propagateInventoryUncertainty
    (run : IsochoricApparatusRun)
    (r : ExperimentalInputReadouts)
    (gasConstantSI avogadroPerMole : ℝ)
    (hgeometry : Figure17GeometryLaw run.geometry)
    (hlaws : AirInventoryLaws run.state gasConstantSI avogadroPerMole)
    (hcover : InputReadoutsCover run r)
    (hvalid : ValidInputReadouts r gasConstantSI avogadroPerMole) :
    InventoryInPropagatedBounds run.state r gasConstantSI avogadroPerMole := by
  sorry

/-- The relation asserting agreement with every number in the official sample.

The conversions are `kg → g`, `mol → mmol`, and molecules to units of `10²¹`.
-/
def AgreesWithOfficialSample (s : ConfinedAirColumnState) : Prop :=
  officialSample.massGrams.Covers (1000 * siValue s.mass) ∧
  officialSample.amountMillimoles.Covers (1000 * s.amount.moles) ∧
  officialSample.moleculesInTenTo21.Covers
    (s.molecules.estimatedCount / (10 : ℝ) ^ 21)

/-- Numerical target recorded for A.1 in the supplied source report.

The statement deliberately keeps the result on the conclusion side.  Its proof
requires the numerical Figure 17 dimensions and their error budget, which are
not visible on the supplied source-page image.
-/
theorem officialSampleTarget
    (run : IsochoricApparatusRun)
    (gasConstantSI avogadroPerMole : ℝ)
    (hgeometry : Figure17GeometryLaw run.geometry)
    (hdensity : AmbientDensityReadout run.state)
    (hlaws : AirInventoryLaws run.state gasConstantSI avogadroPerMole)
    (hgas : 0 < gasConstantSI)
    (havogadro : 0 ≤ avogadroPerMole)
    (htemperature : 0 < siValue run.state.temperature) :
    AgreesWithOfficialSample run.state := by
  sorry

end Problem4A1
end IPhO2026Problems

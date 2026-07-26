import Mathlib.Algebra.Order.Round
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0493

/-!
# Carnot efficiency with ambient air and liquid nitrogen

The hot reservoir is ambient air at `293 K`; the cold reservoir is inexpensive
liquid nitrogen at `77 K`.  The engine is idealized as reversible, so its
dimensionless thermal efficiency obeys the Carnot relation

`η = 1 - T_L / T_H`.

Absolute temperatures use Physlib's `Temperature` type.  Real numbers below
are only calibrated kelvin readouts or dimensionless efficiency values, while
the displayed answer percentages are integers.
-/

/-! ## Physical quantities and named-unit readouts -/

/-- A nonnegative absolute thermodynamic temperature. -/
abbrev AbsoluteTemperatureQuantity : Type := Temperature

/-- Read an absolute temperature in kelvins from its stated storage unit. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit)
    (temperature : AbsoluteTemperatureQuantity) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Heat-engine, reservoir, and primary-figure vocabulary -/

/-- The thermodynamic role of the device described in the problem. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- The reversible ideal-engine model named by the question. -/
inductive HeatEngineModel where
  | carnot
  deriving DecidableEq, Repr

/-- The two thermal reservoirs used in the Carnot model. -/
inductive Reservoir where
  | hot
  | cold
  deriving DecidableEq, Fintype, Repr

/-- The material supplying each reservoir in the narrated scenario. -/
inductive ReservoirSubstance where
  | ambientAir
  | liquidNitrogen
  deriving DecidableEq, Repr

/-- Literal marks visibly painted on the cryogenic vessels in the bitmap. -/
inductive CryogenicVesselMark where
  | numeralOne
  | numeralTwo
  | numeralThree
  | letterK
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and literal data visible in the primary bitmap.  These fields keep
the supplied image in the formal model even though the efficiency calculation
uses the temperatures stated in the prose.
-/
structure CryogenicFacilityFigure where
  markShown : CryogenicVesselMark → Bool
  metalCryogenicVesselsShown : Bool
  vaporShown : Bool
  attendantShown : Bool
  attendantWearsLabCoat : Bool
  paperworkCartShown : Bool

/-!
The physical setup.  The efficiency is an unconstrained dimensionless field
until the generic Carnot governing law is imposed below.
-/
structure AmbientNitrogenCarnotSetup where
  deviceRole : ThermodynamicDeviceRole
  engineModel : HeatEngineModel
  temperatureStorageUnit : TemperatureUnit
  reservoirTemperature : Reservoir → AbsoluteTemperatureQuantity
  reservoirSubstance : Reservoir → ReservoirSubstance
  heatTransferSource : Reservoir
  heatTransferSink : Reservoir
  coldReservoirSupplyIsInexpensive : Bool
  thermalEfficiency : ℝ
  figure : CryogenicFacilityFigure

/-! ## Scenario, data readouts, physical domain, and governing law -/

/-!
Problem-statement data: heat is taken from ambient air at room temperature and
transferred to an inexpensive liquid-nitrogen sink.  These premises do not
assign a value to the requested efficiency.
-/
structure MatchesProblemStatement
    (setup : AmbientNitrogenCarnotSetup) : Prop where
  deviceIsHeatEngine : setup.deviceRole = .heatEngine
  engineUsesCarnotModel : setup.engineModel = .carnot
  temperaturesStoredInKelvins :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  hotReservoirIsAmbientAir :
    setup.reservoirSubstance .hot = .ambientAir
  coldReservoirIsLiquidNitrogen :
    setup.reservoirSubstance .cold = .liquidNitrogen
  hotAmbientTemperatureKelvins :
    temperatureInKelvins setup.temperatureStorageUnit
      (setup.reservoirTemperature .hot) = 293
  coldLiquidNitrogenTemperatureKelvins :
    temperatureInKelvins setup.temperatureStorageUnit
      (setup.reservoirTemperature .cold) = 77
  heatComesFromHotReservoir : setup.heatTransferSource = .hot
  heatGoesToColdReservoir : setup.heatTransferSink = .cold
  liquidNitrogenSupplyIsInexpensive :
    setup.coldReservoirSupplyIsInexpensive = true

/-!
Primary-image evidence.  The raster visibly contains marks `1`, `2`, `3`, and
`K`, metal cryogenic vessels emitting vapor, a lab-coated attendant, and a
paperwork cart.  No efficiency value is read from the image.
-/
structure MatchesPrimaryCryogenicFigure
    (setup : AmbientNitrogenCarnotSetup) : Prop where
  everyVisibleMarkIsShown :
    ∀ mark : CryogenicVesselMark, setup.figure.markShown mark = true
  metalCryogenicVesselsAreShown :
    setup.figure.metalCryogenicVesselsShown = true
  cryogenicVaporIsShown : setup.figure.vaporShown = true
  attendantIsShown : setup.figure.attendantShown = true
  attendantWearsLabCoat : setup.figure.attendantWearsLabCoat = true
  paperworkCartIsShown : setup.figure.paperworkCartShown = true

/-- Positivity, ordering, and range conditions for a physical heat engine. -/
structure HasPhysicalCarnotParameters
    (setup : AmbientNitrogenCarnotSetup) : Prop where
  hotTemperaturePositive :
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.reservoirTemperature .hot)
  coldTemperaturePositive :
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.reservoirTemperature .cold)
  coldTemperatureBelowHot :
    temperatureInKelvins setup.temperatureStorageUnit
        (setup.reservoirTemperature .cold) <
      temperatureInKelvins setup.temperatureStorageUnit
        (setup.reservoirTemperature .hot)
  efficiencyInPhysicalRange :
    0 ≤ setup.thermalEfficiency ∧ setup.thermalEfficiency < 1

/-!
The governing law for a reversible Carnot engine.  It is stated generically in
terms of the two reservoir temperatures and does not contain the requested
numerical efficiency or answer choice.
-/
structure SatisfiesCarnotEfficiencyLaw
    (setup : AmbientNitrogenCarnotSetup) : Prop where
  reversibleCarnotEfficiency :
    setup.thermalEfficiency =
      1 -
        temperatureInKelvins setup.temperatureStorageUnit
            (setup.reservoirTemperature .cold) /
          temperatureInKelvins setup.temperatureStorageUnit
            (setup.reservoirTemperature .hot)

/-! ## Answer choices and target-side consequences -/

/-- Labels attached to the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Whole efficiency percentage printed beside each answer label. -/
def AnswerChoice.efficiencyPercent : AnswerChoice → ℤ
  | .A => 68
  | .B => 70
  | .C => 72
  | .D => 74

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The exact Carnot efficiency is `1 - 77 / 293 = 216 / 293`.
-/
lemma carnotEfficiency_eq_216_div_293
    (setup : AmbientNitrogenCarnotSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryCryogenicFigure setup)
    (_physical : HasPhysicalCarnotParameters setup)
    (_law : SatisfiesCarnotEfficiencyLaw setup) :
    setup.thermalEfficiency = (216 / 293 : ℝ) := by
  rw [_law.reversibleCarnotEfficiency,
    _problem.coldLiquidNitrogenTemperatureKelvins,
    _problem.hotAmbientTemperatureKelvins]
  norm_num

/-!
Multiplying the exact efficiency by `100` gives approximately `73.72`, which
rounds to the whole percentage `74` printed for answer choice D.

Blueprint label: `thm:physics:phyx_mini_0493:target`.
-/
theorem carnotEfficiency_rounds_to_recordedAnswerD
    (setup : AmbientNitrogenCarnotSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryCryogenicFigure setup)
    (_physical : HasPhysicalCarnotParameters setup)
    (_law : SatisfiesCarnotEfficiencyLaw setup) :
    setup.thermalEfficiency = (216 / 293 : ℝ) ∧
      round (100 * setup.thermalEfficiency) =
        recordedAnswerChoice.efficiencyPercent := by
  refine
    ⟨carnotEfficiency_eq_216_div_293
        setup _problem _figure _physical _law, ?_⟩
  rw [carnotEfficiency_eq_216_div_293
      setup _problem _figure _physical _law]
  simp only [recordedAnswerChoice, AnswerChoice.efficiencyPercent]
  rw [round_eq_iff]
  constructor <;> norm_num

end PhyXMiniProblems.ProblemPhyXMini0493

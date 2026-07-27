import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 3, part C.3

The paramagnetic torus follows the oriented Carnot cycle
`1 → 2 → 3 → 4 → 1` in the `H`-versus-`T` plane.  The cold isothermal
leg is `2 → 3`, and the hot isothermal leg is `4 → 1`.

The source data are SI scalar readouts.  `Physlib.WithDim` records their
physical dimensions, while `PhysicalRole` also distinguishes quantities
such as magnetic field strength and magnetization that have the same
dimension but different physical roles.
-/

namespace IPhO2026Problems
namespace Problem3C3

open Dimension

/-- Physical roles of the scalar SI readouts occurring in problem 3 C.3. -/
inductive PhysicalRole
  | temperature
  | volume
  | amountOfSubstance
  | curieConstant
  | massDensity
  | molarMass
  | magneticFieldStrength
  | magnetization
  | specificHeatCapacity
  | vacuumPermeability
  | energy
  deriving DecidableEq

/-- The Physlib dimension carried by each physical role.

Physlib's foundational dimensions do not include amount of substance.
Consequently the mole is dimensionless here, while its physical role is
retained by the `amountOfSubstance`, `molarMass`, and `curieConstant`
indices.
-/
def PhysicalRole.dimension : PhysicalRole → Dimension
  | .temperature => Θ𝓭
  | .volume => L𝓭 * L𝓭 * L𝓭
  | .amountOfSubstance => 1
  | .curieConstant => Θ𝓭 * L𝓭 * L𝓭 * L𝓭
  | .massDensity => M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹
  | .molarMass => M𝓭
  | .magneticFieldStrength => C𝓭 * T𝓭⁻¹ * L𝓭⁻¹
  | .magnetization => C𝓭 * T𝓭⁻¹ * L𝓭⁻¹
  | .specificHeatCapacity => L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹
  | .vacuumPermeability => M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹
  | .energy => M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative scalar readout in SI units, indexed by its physical role. -/
structure SIQuantity (role : PhysicalRole) where
  reading : WithDim role.dimension ℝ
  nonnegative : 0 ≤ reading.val

/-- The real-valued SI coordinate of a physical readout. -/
def SIQuantity.siValue {role : PhysicalRole} (q : SIQuantity role) : ℝ :=
  q.reading.val

/-- The four labelled vertices in Figure 3b. -/
inductive CyclePoint
  | one
  | two
  | three
  | four
  deriving DecidableEq

/-- Physical kind and orientation of each outgoing Carnot-cycle leg. -/
inductive CarnotLegKind
  | adiabaticCooling
  | coldIsothermal
  | adiabaticHeating
  | hotIsothermal
  deriving DecidableEq

/-- The `H`-versus-`T` coordinates and magnetization at a labelled cycle point. -/
structure TorusStateReading where
  temperature : SIQuantity .temperature
  fieldStrength : SIQuantity .magneticFieldStrength
  magnetization : SIQuantity .magnetization

/-- Figure 3b with the directed order `1 → 2 → 3 → 4 → 1`. -/
structure CarnotTorusCycle where
  state : CyclePoint → TorusStateReading
  outgoingLeg : CyclePoint → CarnotLegKind
  oneToTwo : outgoingLeg .one = .adiabaticCooling
  twoToThree : outgoingLeg .two = .coldIsothermal
  threeToFour : outgoingLeg .three = .adiabaticHeating
  fourToOne : outgoingLeg .four = .hotIsothermal

/-- Potassium-chromate paramagnetic torus data. -/
structure ParamagneticTorus where
  amount : SIQuantity .amountOfSubstance
  curieConstant : SIQuantity .curieConstant
  density : SIQuantity .massDensity
  molarMass : SIQuantity .molarMass
  volume : SIQuantity .volume

/-- Liquid-helium sample data. -/
structure LiquidHeliumSample where
  volume : SIQuantity .volume
  initialTemperature : SIQuantity .temperature
  density : SIQuantity .massDensity
  specificHeatCapacity : SIQuantity .specificHeatCapacity

/-- All material data and the vacuum permeability used by the cycle. -/
structure RefrigerationSetup where
  torus : ParamagneticTorus
  helium : LiquidHeliumSample
  vacuumPermeability : SIQuantity .vacuumPermeability

/-- Magnitudes `Q_c` and `Q_h` associated with one oriented cycle. -/
structure CycleHeatExchange where
  absorbedFromCold : SIQuantity .energy
  deliveredToHot : SIQuantity .energy

/-- Exact SI readouts supplied in C.3, together with the standard value of `μ₀`. -/
structure SuppliedReadouts
    (setup : RefrigerationSetup) (cycle : CarnotTorusCycle) : Prop where
  torusAmount :
    setup.torus.amount.siValue = 2
  potassiumChromateCurieConstant :
    setup.torus.curieConstant.siValue = 187 / 100000000
  potassiumChromateDensity :
    setup.torus.density.siValue = 2730
  potassiumChromateMolarMass :
    setup.torus.molarMass.siValue = 19 / 100
  heliumVolume :
    setup.helium.volume.siValue = 1 / 1000
  heliumInitialTemperature :
    setup.helium.initialTemperature.siValue = 1
  heliumDensity :
    setup.helium.density.siValue = 130
  heliumSpecificHeatCapacity :
    setup.helium.specificHeatCapacity.siValue = 100
  fieldAtOne :
    (cycle.state .one).fieldStrength.siValue = 411624
  fieldAtTwo :
    (cycle.state .two).fieldStrength.siValue = 311306
  fieldAtThree :
    (cycle.state .three).fieldStrength.siValue = 204618
  fieldAtFour :
    (cycle.state .four).fieldStrength.siValue = 240446
  standardVacuumPermeability :
    setup.vacuumPermeability.siValue = 4 * Real.pi / 10000000

/-- The material volume is mass divided by density:
`V ρ = n m_molar`. -/
structure TorusVolumeMassBalance (setup : RefrigerationSetup) : Prop where
  volumeDensityEquation :
    setup.torus.volume.siValue * setup.torus.density.siValue =
      setup.torus.amount.siValue * setup.torus.molarMass.siValue

/-- The given paramagnetic equation of state `T M V = n K H` at every vertex. -/
structure ParamagneticEquationOfState
    (setup : RefrigerationSetup) (cycle : CarnotTorusCycle) : Prop where
  equationAtState : ∀ point : CyclePoint,
    (cycle.state point).temperature.siValue *
        (cycle.state point).magnetization.siValue *
        setup.torus.volume.siValue =
      setup.torus.amount.siValue *
        setup.torus.curieConstant.siValue *
        (cycle.state point).fieldStrength.siValue

/-- The two horizontal-temperature branches and their hot/cold orientation. -/
structure CarnotTemperaturePattern (cycle : CarnotTorusCycle) : Prop where
  coldIsothermal :
    (cycle.state .two).temperature.siValue =
      (cycle.state .three).temperature.siValue
  hotIsothermal :
    (cycle.state .four).temperature.siValue =
      (cycle.state .one).temperature.siValue
  coldBelowHot :
    (cycle.state .two).temperature.siValue <
      (cycle.state .one).temperature.siValue

/-- Reusable conclusion of previous part C.2, with the nonnegative square-root
branch selected by the magnitude-valued magnetization readouts. -/
structure PreviousPartC2MagnetizationRelation (cycle : CarnotTorusCycle) : Prop where
  stateOneMagnetization :
    (cycle.state .one).magnetization.siValue =
      Real.sqrt
        ((cycle.state .two).magnetization.siValue ^ 2 -
          (cycle.state .three).magnetization.siValue ^ 2 +
          (cycle.state .four).magnetization.siValue ^ 2)

/-- The B.1 isothermal heat law applied to the oriented cold and hot legs.

Heat entering the torus is positive.  Thus `Q_c` is the positive heat entering
on `2 → 3`, while `Q_h` is the positive magnitude of the heat leaving on
`4 → 1`.
-/
structure CarnotIsothermalHeatLaw
    (setup : RefrigerationSetup) (cycle : CarnotTorusCycle)
    (heats : CycleHeatExchange) : Prop where
  coldReservoirContact :
    (cycle.state .two).temperature.siValue =
      setup.helium.initialTemperature.siValue
  coldTemperaturePositive :
    0 < (cycle.state .two).temperature.siValue
  hotTemperaturePositive :
    0 < (cycle.state .one).temperature.siValue
  coldHeatEquation :
    heats.absorbedFromCold.siValue =
      -(setup.vacuumPermeability.siValue *
          setup.torus.amount.siValue *
          setup.torus.curieConstant.siValue /
          (2 * (cycle.state .two).temperature.siValue)) *
        ((cycle.state .three).fieldStrength.siValue ^ 2 -
          (cycle.state .two).fieldStrength.siValue ^ 2)
  hotHeatEquation :
    heats.deliveredToHot.siValue =
      (setup.vacuumPermeability.siValue *
          setup.torus.amount.siValue *
          setup.torus.curieConstant.siValue /
          (2 * (cycle.state .one).temperature.siValue)) *
        ((cycle.state .one).fieldStrength.siValue ^ 2 -
          (cycle.state .four).fieldStrength.siValue ^ 2)

/-- Constant-density, constant-specific-heat calorimetry for the helium.

The energy absorbed by the torus is removed from the helium.  The inequality
selects the cooling rather than heating orientation of the signed balance.
-/
structure HeliumCalorimetryLaw
    (setup : RefrigerationSetup) (heats : CycleHeatExchange)
    (finalTemperature : SIQuantity .temperature) : Prop where
  energyBalance :
    heats.absorbedFromCold.siValue =
      setup.helium.density.siValue *
        setup.helium.volume.siValue *
        setup.helium.specificHeatCapacity.siValue *
        (setup.helium.initialTemperature.siValue - finalTemperature.siValue)
  coolingOrientation :
    finalTemperature.siValue ≤ setup.helium.initialTemperature.siValue

/-- After one cycle, the torus absorbs approximately `0.129 J`; the helium
cools by approximately `0.00992 K`, to approximately `0.99008 K`.

The bounds are numerical-rounding envelopes around the values reported in the
official answer, rather than measurement-uncertainty assumptions.
-/
theorem IPhO_2026_3_C_3_helium_temperature_after_one_cycle
    (setup : RefrigerationSetup)
    (cycle : CarnotTorusCycle)
    (heats : CycleHeatExchange)
    (finalTemperature : SIQuantity .temperature)
    (readouts : SuppliedReadouts setup cycle)
    (volumeLaw : TorusVolumeMassBalance setup)
    (equationOfState : ParamagneticEquationOfState setup cycle)
    (temperaturePattern : CarnotTemperaturePattern cycle)
    (previousPartC2 : PreviousPartC2MagnetizationRelation cycle)
    (heatLaw : CarnotIsothermalHeatLaw setup cycle heats)
    (calorimetry : HeliumCalorimetryLaw setup heats finalTemperature) :
    abs (heats.absorbedFromCold.siValue - 129 / 1000) ≤ 1 / 2000 ∧
      abs
          ((setup.helium.initialTemperature.siValue - finalTemperature.siValue) -
            992 / 100000) ≤
        1 / 20000 ∧
      abs (finalTemperature.siValue - 99008 / 100000) ≤ 1 / 20000 := by
  have hQ :
      heats.absorbedFromCold.siValue =
        (40207118149 / 976562500000 : ℝ) * Real.pi := by
    rw [heatLaw.coldHeatEquation, readouts.standardVacuumPermeability,
      readouts.torusAmount, readouts.potassiumChromateCurieConstant,
      heatLaw.coldReservoirContact, readouts.heliumInitialTemperature,
      readouts.fieldAtThree, readouts.fieldAtTwo]
    ring
  have hQ_error :
      abs (heats.absorbedFromCold.siValue - 129 / 1000) ≤ 1 / 2000 := by
    rw [hQ, abs_le]
    constructor <;> nlinarith [Real.pi_gt_d4, Real.pi_lt_d4]
  have hcal := calorimetry.energyBalance
  rw [readouts.heliumDensity, readouts.heliumVolume,
    readouts.heliumSpecificHeatCapacity, readouts.heliumInitialTemperature] at hcal
  norm_num at hcal
  rcases (abs_le.mp hQ_error) with ⟨hQ_lower, hQ_upper⟩
  refine ⟨hQ_error, ?_, ?_⟩
  · rw [readouts.heliumInitialTemperature, abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith

end Problem3C3
end IPhO2026Problems

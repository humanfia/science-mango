import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 3, part C.2

The paramagnetic torus follows the Carnot refrigeration cycle
`1 → 2 → 3 → 4 → 1` in the magnetic-field-versus-temperature plane.
This file records the dimensionful state data, the figure readouts, the
paramagnetic equation of state, the isothermal heat law, and the reversible
Carnot heat balance needed to determine the magnetization at state `1`.

All scalar equations below are equations between SI-coordinate readouts of
dimensionful quantities.
-/

open Dimension

namespace IPhO2026Problem3C2

noncomputable section

/-! ## Dimensions and physical quantities -/

/-- The SI dimension of magnetic-field strength and magnetization, `A / m`. -/
def magneticIntensityDimension : Dimension := C𝓭 * T𝓭⁻¹ * L𝓭⁻¹

/-- The SI dimension of volume, `m³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/--
The dimension of the material constant `K` in `T M V = n K H`.
Since `M` and `H` have the same dimension, this is temperature times volume.
-/
def curieConstantDimension : Dimension := Θ𝓭 * volumeDimension

/-- The SI dimension of vacuum permeability, `kg m / C²`. -/
def vacuumPermeabilityDimension : Dimension := M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- The SI dimension of heat/energy, `kg m² / s²`. -/
def energyDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A unit-covariant real physical quantity carrying dimension `d`. -/
abbrev PhysicalQuantity (d : Dimension) : Type :=
  Dimensionful (WithDim d ℝ)

abbrev Temperature : Type := PhysicalQuantity Θ𝓭
abbrev Volume : Type := PhysicalQuantity volumeDimension
abbrev MagneticFieldMagnitude : Type := PhysicalQuantity magneticIntensityDimension
abbrev MagnetizationMagnitude : Type := PhysicalQuantity magneticIntensityDimension
abbrev CurieConstant : Type := PhysicalQuantity curieConstantDimension
abbrev VacuumPermeability : Type := PhysicalQuantity vacuumPermeabilityDimension
abbrev HeatMagnitude : Type := PhysicalQuantity energyDimension

/-- The real coordinate of a dimensionful quantity in SI units. -/
def siValue {d : Dimension} (q : PhysicalQuantity d) : ℝ :=
  (q UnitChoices.SI).val

/-! ## Figure labels and oriented cycle legs -/

/-- The four labeled vertices in Figure 3b. -/
inductive CycleVertex where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Repr

/-- The oriented legs of the cycle `1 → 2 → 3 → 4 → 1`. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToFour
  | fourToOne
  deriving DecidableEq, Repr

/-- Initial vertex of an oriented cycle leg. -/
def CycleLeg.initial : CycleLeg → CycleVertex
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToFour => .three
  | .fourToOne => .four

/-- Final vertex of an oriented cycle leg. -/
def CycleLeg.final : CycleLeg → CycleVertex
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToFour => .four
  | .fourToOne => .one

/-- The thermodynamic kind of each leg, including the reservoir involved. -/
inductive CycleProcessKind where
  | adiabaticExpansion
  | coldIsothermalHeatAbsorption
  | adiabaticCompression
  | hotIsothermalHeatRejection
  deriving DecidableEq, Repr

/-- Figure/process readout for the four oriented legs of the Carnot cycle. -/
def CycleLeg.processKind : CycleLeg → CycleProcessKind
  | .oneToTwo => .adiabaticExpansion
  | .twoToThree => .coldIsothermalHeatAbsorption
  | .threeToFour => .adiabaticCompression
  | .fourToOne => .hotIsothermalHeatRejection

/-! ## Physical data and governing laws -/

/-- A state of the torus at one vertex of the cycle. -/
structure ThermodynamicState where
  temperature : Temperature
  magneticField : MagneticFieldMagnitude
  magnetization : MagnetizationMagnitude
  temperature_pos : 0 < siValue temperature
  magneticField_nonneg : 0 ≤ siValue magneticField
  magnetization_nonneg : 0 ≤ siValue magnetization

/-- Fixed physical parameters of the paramagnetic torus. -/
structure ParamagneticTorus where
  volume : Volume
  /-- The dimensionless number `n` of paramagnetic constituents. -/
  constituentCount : ℝ
  curieConstant : CurieConstant
  vacuumPermeability : VacuumPermeability
  volume_pos : 0 < siValue volume
  constituentCount_pos : 0 < constituentCount
  curieConstant_pos : 0 < siValue curieConstant
  vacuumPermeability_pos : 0 < siValue vacuumPermeability

/--
The cycle data, including the reservoir temperatures, positive heat magnitudes,
and the state attached to every labeled vertex.
-/
structure CarnotCycleData where
  torus : ParamagneticTorus
  hotTemperature : Temperature
  coldTemperature : Temperature
  /-- `Q_h`, the magnitude of the heat delivered to the hot reservoir. -/
  heatToHot : HeatMagnitude
  /-- `Q_c`, the magnitude of the heat absorbed from the cold reservoir. -/
  heatFromCold : HeatMagnitude
  state : CycleVertex → ThermodynamicState
  hotTemperature_pos : 0 < siValue hotTemperature
  coldTemperature_pos : 0 < siValue coldTemperature
  cold_lt_hot : siValue coldTemperature < siValue hotTemperature
  heatToHot_nonneg : 0 ≤ siValue heatToHot
  heatFromCold_nonneg : 0 ≤ siValue heatFromCold
  /-- Figure readout: states `1` and `4` are on the hot isotherm. -/
  state_one_at_hot : (state .one).temperature = hotTemperature
  state_four_at_hot : (state .four).temperature = hotTemperature
  /-- Figure readout: states `2` and `3` are on the cold isotherm. -/
  state_two_at_cold : (state .two).temperature = coldTemperature
  state_three_at_cold : (state .three).temperature = coldTemperature

/-- SI magnetization magnitude at a labeled cycle vertex. -/
def magnetizationSI (cycle : CarnotCycleData) (v : CycleVertex) : ℝ :=
  siValue (cycle.state v).magnetization

/-- SI magnetic-field magnitude at a labeled cycle vertex. -/
def magneticFieldSI (cycle : CarnotCycleData) (v : CycleVertex) : ℝ :=
  siValue (cycle.state v).magneticField

/-- SI temperature at a labeled cycle vertex. -/
def stateTemperatureSI (cycle : CarnotCycleData) (v : CycleVertex) : ℝ :=
  siValue (cycle.state v).temperature

/--
The physical laws used in part C.2.

The heat-law equations preserve the orientation and sign convention from part
B.1: heat transferred *into* the torus is positive. Thus `Q_c` is used on
`2 → 3`, while the signed heat into the torus on `4 → 1` is `-Q_h`.
-/
structure SatisfiesParamagneticCarnotLaws (cycle : CarnotCycleData) : Prop where
  /-- Equation of state `T M V = n K H` at every vertex. -/
  equationOfState : ∀ v : CycleVertex,
    stateTemperatureSI cycle v * magnetizationSI cycle v *
        siValue cycle.torus.volume =
      cycle.torus.constituentCount * siValue cycle.torus.curieConstant *
        magneticFieldSI cycle v
  /--
  The isothermal heat law on `2 → 3`, where `Q_c` is absorbed by the torus.
  -/
  coldIsothermalHeat :
    siValue cycle.heatFromCold =
      -(siValue cycle.torus.vacuumPermeability *
          cycle.torus.constituentCount * siValue cycle.torus.curieConstant /
          (2 * siValue cycle.coldTemperature)) *
        (magneticFieldSI cycle .three ^ 2 - magneticFieldSI cycle .two ^ 2)
  /--
  The isothermal heat law on `4 → 1`; signed heat into the torus is `-Q_h`.
  -/
  hotIsothermalHeat :
    -(siValue cycle.heatToHot) =
      -(siValue cycle.torus.vacuumPermeability *
          cycle.torus.constituentCount * siValue cycle.torus.curieConstant /
          (2 * siValue cycle.hotTemperature)) *
        (magneticFieldSI cycle .one ^ 2 - magneticFieldSI cycle .four ^ 2)
  /--
  Entropy balance for a reversible Carnot cycle:
  `Q_h / T_h = Q_c / T_c`.
  -/
  carnotEntropyBalance :
    siValue cycle.heatToHot / siValue cycle.hotTemperature =
      siValue cycle.heatFromCold / siValue cycle.coldTemperature

/-! ## Derived relations requested by part C.2 -/

/--
The algebraic square balance obtained by combining the equation of state, the
two isothermal heat equations, and the reversible Carnot heat balance.
-/
theorem magnetization_square_balance
    (cycle : CarnotCycleData)
    (laws : SatisfiesParamagneticCarnotLaws cycle) :
    magnetizationSI cycle .one ^ 2 - magnetizationSI cycle .four ^ 2 =
      magnetizationSI cycle .two ^ 2 - magnetizationSI cycle .three ^ 2 := by
  have hhot : siValue cycle.hotTemperature ≠ 0 :=
    ne_of_gt cycle.hotTemperature_pos
  have hcold : siValue cycle.coldTemperature ≠ 0 :=
    ne_of_gt cycle.coldTemperature_pos
  have hn : cycle.torus.constituentCount ≠ 0 :=
    ne_of_gt cycle.torus.constituentCount_pos
  have hK : siValue cycle.torus.curieConstant ≠ 0 :=
    ne_of_gt cycle.torus.curieConstant_pos
  have heos1 := laws.equationOfState .one
  have heos2 := laws.equationOfState .two
  have heos3 := laws.equationOfState .three
  have heos4 := laws.equationOfState .four
  simp only [stateTemperatureSI, cycle.state_one_at_hot] at heos1
  simp only [stateTemperatureSI, cycle.state_two_at_cold] at heos2
  simp only [stateTemperatureSI, cycle.state_three_at_cold] at heos3
  simp only [stateTemperatureSI, cycle.state_four_at_hot] at heos4
  have hf1 :
      magneticFieldSI cycle .one =
        siValue cycle.hotTemperature * magnetizationSI cycle .one *
            siValue cycle.torus.volume /
          (cycle.torus.constituentCount *
            siValue cycle.torus.curieConstant) := by
    field_simp [hn, hK]
    nlinarith [heos1]
  have hf2 :
      magneticFieldSI cycle .two =
        siValue cycle.coldTemperature * magnetizationSI cycle .two *
            siValue cycle.torus.volume /
          (cycle.torus.constituentCount *
            siValue cycle.torus.curieConstant) := by
    field_simp [hn, hK]
    nlinarith [heos2]
  have hf3 :
      magneticFieldSI cycle .three =
        siValue cycle.coldTemperature * magnetizationSI cycle .three *
            siValue cycle.torus.volume /
          (cycle.torus.constituentCount *
            siValue cycle.torus.curieConstant) := by
    field_simp [hn, hK]
    nlinarith [heos3]
  have hf4 :
      magneticFieldSI cycle .four =
        siValue cycle.hotTemperature * magnetizationSI cycle .four *
            siValue cycle.torus.volume /
          (cycle.torus.constituentCount *
            siValue cycle.torus.curieConstant) := by
    field_simp [hn, hK]
    nlinarith [heos4]
  have hc := laws.coldIsothermalHeat
  rw [hf2, hf3] at hc
  field_simp [hhot, hcold, hn, hK] at hc
  have hc' :
      cycle.torus.constituentCount *
            siValue cycle.torus.curieConstant * 2 *
          siValue cycle.heatFromCold =
        siValue cycle.torus.vacuumPermeability *
            siValue cycle.torus.volume ^ 2 *
            siValue cycle.coldTemperature *
          (magnetizationSI cycle .two ^ 2 -
            magnetizationSI cycle .three ^ 2) := by
    linear_combination hc
  have hh := laws.hotIsothermalHeat
  rw [hf1, hf4] at hh
  field_simp [hhot, hcold, hn, hK] at hh
  have hh' :
      cycle.torus.constituentCount *
            siValue cycle.torus.curieConstant * 2 *
          siValue cycle.heatToHot =
        siValue cycle.torus.vacuumPermeability *
            siValue cycle.torus.volume ^ 2 *
            siValue cycle.hotTemperature *
          (magnetizationSI cycle .one ^ 2 -
            magnetizationSI cycle .four ^ 2) := by
    linear_combination -hh
  have hb := laws.carnotEntropyBalance
  field_simp [hhot, hcold] at hb
  have hscaled :
      (siValue cycle.torus.vacuumPermeability *
          siValue cycle.torus.volume ^ 2 *
          siValue cycle.hotTemperature *
          siValue cycle.coldTemperature) *
        (magnetizationSI cycle .one ^ 2 -
          magnetizationSI cycle .four ^ 2) =
      (siValue cycle.torus.vacuumPermeability *
          siValue cycle.torus.volume ^ 2 *
          siValue cycle.hotTemperature *
          siValue cycle.coldTemperature) *
        (magnetizationSI cycle .two ^ 2 -
          magnetizationSI cycle .three ^ 2) := by
    calc
      _ = siValue cycle.coldTemperature *
          (cycle.torus.constituentCount *
              siValue cycle.torus.curieConstant * 2 *
            siValue cycle.heatToHot) := by rw [hh']; ring
      _ = (cycle.torus.constituentCount *
              siValue cycle.torus.curieConstant * 2) *
            (siValue cycle.coldTemperature *
              siValue cycle.heatToHot) := by ring
      _ = (cycle.torus.constituentCount *
              siValue cycle.torus.curieConstant * 2) *
            (siValue cycle.heatFromCold *
              siValue cycle.hotTemperature) := by
        linear_combination
          (cycle.torus.constituentCount *
            siValue cycle.torus.curieConstant * 2) * hb
      _ = siValue cycle.hotTemperature *
          (cycle.torus.constituentCount *
              siValue cycle.torus.curieConstant * 2 *
            siValue cycle.heatFromCold) := by ring
      _ = _ := by rw [hc']; ring
  exact mul_left_cancel₀
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (ne_of_gt cycle.torus.vacuumPermeability_pos)
          (pow_ne_zero 2 (ne_of_gt cycle.torus.volume_pos)))
        hhot)
      hcold)
    hscaled

/--
IPhO 2026 problem 3 C.2: the magnetization at state `1`, on the nonnegative
magnitude branch, in terms of the magnetizations at states `2`, `3`, and `4`.
-/
theorem magnetization_at_state_one
    (cycle : CarnotCycleData)
    (laws : SatisfiesParamagneticCarnotLaws cycle) :
    magnetizationSI cycle .one =
      Real.sqrt
        (magnetizationSI cycle .two ^ 2 -
          magnetizationSI cycle .three ^ 2 +
          magnetizationSI cycle .four ^ 2) := by
  have hnonneg : 0 ≤ magnetizationSI cycle .one := by
    exact (cycle.state .one).magnetization_nonneg
  have hsquare :
      magnetizationSI cycle .one ^ 2 =
        magnetizationSI cycle .two ^ 2 -
          magnetizationSI cycle .three ^ 2 +
          magnetizationSI cycle .four ^ 2 := by
    nlinarith [magnetization_square_balance cycle laws]
  calc
    magnetizationSI cycle .one =
        Real.sqrt (magnetizationSI cycle .one ^ 2) :=
      (Real.sqrt_sq hnonneg).symm
    _ = _ := congrArg Real.sqrt hsquare

end

end IPhO2026Problem3C2

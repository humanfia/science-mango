import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0491

open Dimension

/-!
# Total heat into an ideal gas along the path `B → D → A`

An ideal gas is compressed from `B` to `D` at constant pressure `2 atm`,
changing volume from `10 L` to `2 L`.  It is then heated from `D` to `A` at
constant volume until its temperature again equals the temperature at `B`.

The primary raster shows `B → D` as a leftward horizontal isobaric leg,
`D → A` as an upward vertical isovolumetric leg, and `A`--`B` as an
isothermal curve.  Heat is positive into the gas and boundary work is positive
when done by the gas.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` contains only prose and raster readouts,
  including `T_A = T_B`;
* `HasPhysicalParameters` contains positivity conditions;
* `SatisfiesIdealGasProcessLaws` states temperature dependence of ideal-gas
  internal energy, isobaric/isochoric boundary work, and the first law;
* the exact total heat and its match to answer D occur only as conclusions.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Litre readout of a physical volume, using `1 m³ = 1000 L`. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Pascal readout of a dimensionful pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Standard-atmosphere readout of a dimensionful pressure. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.standardAtmosphere UnitChoices.SI).val

/-- Joule readout of a signed physical energy, heat transfer, or work. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Exact SI value of one litre-atmosphere, in joules. -/
def joulesPerLiterAtmosphere : ℝ := 101325 / 1000

/-- Physlib's standard atmosphere is exactly `101325 Pa`. -/
lemma standardAtmosphereInPascals :
    pressureInPascals DimPressure.standardAtmosphere = 101325 := by
  norm_num [pressureInPascals, DimPressure.standardAtmosphere,
    DimPressure.pascal, CarriesDimension.toDimensionful_apply_apply]

/-! ## Thermodynamic states, process legs, and primary-figure vocabulary -/

/-- The three labeled equilibrium states in the supplied `pV` diagram. -/
inductive ThermodynamicState where
  | A
  | B
  | D
  deriving DecidableEq, Fintype, Repr

/-- The two directed legs of the requested process `B → D → A`. -/
inductive ProcessLeg where
  | bToD
  | dToA
  deriving DecidableEq, Fintype, Repr

/-- Initial state of a directed process leg. -/
def legSource : ProcessLeg → ThermodynamicState
  | .bToD => .B
  | .dToA => .D

/-- Final state of a directed process leg. -/
def legTarget : ProcessLeg → ThermodynamicState
  | .bToD => .D
  | .dToA => .A

/-- The three red segments or curves visible in the primary raster. -/
inductive DiagramSegment where
  | aToB
  | bToD
  | dToA
  deriving DecidableEq, Fintype, Repr

/-- Thermodynamic constraint named beside a path in the diagram. -/
inductive ProcessKind where
  | isothermal
  | isobaric
  | isovolumetric
  deriving DecidableEq, Fintype, Repr

/-- Process label attached to each visible segment. -/
def displayedProcessKind : DiagramSegment → ProcessKind
  | .aToB => .isothermal
  | .bToD => .isobaric
  | .dToA => .isovolumetric

/-- Process kind of each traversed leg. -/
def legProcessKind : ProcessLeg → ProcessKind
  | .bToD => .isobaric
  | .dToA => .isovolumetric

/-- Whether a leg is traversed slowly enough to be modeled quasistatically. -/
inductive ProcessRegime where
  | quasistatic
  | unspecified
  deriving DecidableEq, Repr

/-- Geometric shape of a visible path in the `pV` plane. -/
inductive SegmentShape where
  | curved
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Shape read directly from the primary raster. -/
def displayedSegmentShape : DiagramSegment → SegmentShape
  | .aToB => .curved
  | .bToD => .horizontal
  | .dToA => .vertical

/-- Direction of a visible process arrow. -/
inductive ArrowDirection where
  | left
  | up
  deriving DecidableEq, Repr

/-- Arrow direction on each of the two traversed legs. -/
def displayedArrowDirection : ProcessLeg → ArrowDirection
  | .bToD => .left
  | .dToA => .up

/-- The two Cartesian axes shown in the raster. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity represented by an axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit information literally printed on an axis. -/
inductive AxisDisplayUnit where
  | liters
  | symbolicPressure
  deriving DecidableEq, Repr

/-- The two symbolic pressure levels labeled on the vertical axis. -/
inductive PressureLevelLabel where
  | pA
  | pB
  deriving DecidableEq, Fintype, Repr

/-- Literal visible content of the supplied pressure-volume diagram. -/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  stateLabelVisible : ThermodynamicState → Bool
  segmentVisible : DiagramSegment → Bool
  processLabelVisible : ProcessKind → Bool
  segmentShape : DiagramSegment → SegmentShape
  arrowVisible : ProcessLeg → Bool
  arrowDirection : ProcessLeg → ArrowDirection
  pressureLevelLabelVisible : PressureLevelLabel → Bool
  volumeTickVisible : ℝ → Bool

/-! ## Physical system and independent observables -/

/-- Thermodynamic model stated in the problem. -/
inductive GasModel where
  | idealGas
  deriving DecidableEq, Repr

/-!
The ideal-gas process and its independent observables.  Neither heat transfer
is defined from an answer choice.  `workDoneByGasOn` is signed positive for
expansion, and `heatTransferredIntoGasOn` is signed positive into the gas.
-/
structure IdealGasBDAProcess where
  gasModel : GasModel
  figure : PressureVolumeFigure
  volumeAt : ThermodynamicState → VolumeQuantity
  pressureAt : ThermodynamicState → DimPressure
  temperatureAt : ThermodynamicState → Temperature
  internalEnergyAt : ThermodynamicState → DimEnergy
  processRegime : ProcessLeg → ProcessRegime
  workDoneByGasOn : ProcessLeg → DimEnergy
  heatTransferredIntoGasOn : ProcessLeg → DimEnergy

/-- Joule readout of internal energy at a labeled state. -/
def internalEnergyInJoules
    (setup : IdealGasBDAProcess) (state : ThermodynamicState) : ℝ :=
  energyInJoules (setup.internalEnergyAt state)

/-- Signed joule readout of work done by the gas on a leg. -/
def workDoneByGasInJoules
    (setup : IdealGasBDAProcess) (leg : ProcessLeg) : ℝ :=
  energyInJoules (setup.workDoneByGasOn leg)

/-- Signed joule readout of heat transferred into the gas on a leg. -/
def heatTransferredIntoGasInJoules
    (setup : IdealGasBDAProcess) (leg : ProcessLeg) : ℝ :=
  energyInJoules (setup.heatTransferredIntoGasOn leg)

/-!
Total heat into the gas over `B → D → A`, defined only as the sum of the two
independent leg heats.  This definition contains no numerical answer.
-/
def totalHeatIntoGasInJoules (setup : IdealGasBDAProcess) : ℝ :=
  heatTransferredIntoGasInJoules setup .bToD +
    heatTransferredIntoGasInJoules setup .dToA

/-- Total boundary work done by the gas over the two traversed legs. -/
def totalWorkDoneByGasInJoules (setup : IdealGasBDAProcess) : ℝ :=
  workDoneByGasInJoules setup .bToD +
    workDoneByGasInJoules setup .dToA

/-! ## Source data, figure readouts, and governing laws -/

/-!
Exact transcription of the problem prose and primary raster.  The final
temperature equality is endpoint data, not a heat-value assumption.
-/
structure MatchesProblemAndPrimaryFigure (setup : IdealGasBDAProcess) : Prop where
  modelIsIdealGas : setup.gasModel = .idealGas
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  volumeAxisUsesLiters :
    setup.figure.axisDisplayUnit .horizontal = .liters
  pressureAxisIsSymbolic :
    setup.figure.axisDisplayUnit .vertical = .symbolicPressure
  everyStateLabelIsVisible :
    ∀ state, setup.figure.stateLabelVisible state = true
  everySegmentIsVisible :
    ∀ segment, setup.figure.segmentVisible segment = true
  everyProcessLabelIsVisible :
    ∀ kind, setup.figure.processLabelVisible kind = true
  segmentShapesAgreeWithRaster :
    ∀ segment,
      setup.figure.segmentShape segment = displayedSegmentShape segment
  everyProcessArrowIsVisible :
    ∀ leg, setup.figure.arrowVisible leg = true
  arrowDirectionsAgreeWithRaster :
    ∀ leg, setup.figure.arrowDirection leg = displayedArrowDirection leg
  bothPressureLevelLabelsAreVisible :
    ∀ label, setup.figure.pressureLevelLabelVisible label = true
  displayedVolumeTicks :
    setup.figure.volumeTickVisible 0 = true ∧
      setup.figure.volumeTickVisible 2 = true ∧
      setup.figure.volumeTickVisible 4 = true ∧
      setup.figure.volumeTickVisible 6 = true ∧
      setup.figure.volumeTickVisible 8 = true ∧
      setup.figure.volumeTickVisible 10 = true
  volumeAtBIsTenLiters : volumeInLiters (setup.volumeAt .B) = 10
  volumeAtDIsTwoLiters : volumeInLiters (setup.volumeAt .D) = 2
  volumeAtAIsTwoLiters : volumeInLiters (setup.volumeAt .A) = 2
  pressureAtBIsTwoAtmospheres :
    pressureInAtmospheres (setup.pressureAt .B) = 2
  pressureAtDIsTwoAtmospheres :
    pressureInAtmospheres (setup.pressureAt .D) = 2
  compressionIsSlow : setup.processRegime .bToD = .quasistatic
  pressureRisesFromDToA :
    pressureInPascals (setup.pressureAt .D) <
      pressureInPascals (setup.pressureAt .A)
  temperatureDropsFromBToD :
    (setup.temperatureAt .D).val < (setup.temperatureAt .B).val
  finalTemperatureReturnsToInitial :
    setup.temperatureAt .A = setup.temperatureAt .B
  heatLeavesGasOnCompression :
    heatTransferredIntoGasInJoules setup .bToD < 0
  heatEntersGasOnIsochoricLeg :
    0 < heatTransferredIntoGasInJoules setup .dToA

/-- Positivity conditions for the physical equilibrium states. -/
structure HasPhysicalParameters (setup : IdealGasBDAProcess) : Prop where
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.volumeAt state)
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.pressureAt state)
  absoluteTemperaturePositive :
    ∀ state, 0 < (setup.temperatureAt state).val

/-!
Macroscopic laws used by the calculation:

* ideal-gas internal energy depends only on absolute temperature;
* isobaric boundary work is `p (V_f - V_i)`;
* isovolumetric boundary work vanishes;
* on each leg, `Q_in = U_f - U_i + W_by`.

No field states a leg's numerical heat, the total heat, or the selected answer.
-/
structure SatisfiesIdealGasProcessLaws (setup : IdealGasBDAProcess) : Prop where
  internalEnergyDependsOnlyOnTemperature :
    ∀ state₁ state₂,
      setup.temperatureAt state₁ = setup.temperatureAt state₂ →
        internalEnergyInJoules setup state₁ =
          internalEnergyInJoules setup state₂
  isobaricBoundaryWork :
    ∀ leg,
      legProcessKind leg = .isobaric →
        setup.processRegime leg = .quasistatic →
        workDoneByGasInJoules setup leg =
          pressureInPascals (setup.pressureAt (legSource leg)) *
            (volumeInCubicMeters (setup.volumeAt (legTarget leg)) -
              volumeInCubicMeters (setup.volumeAt (legSource leg)))
  isovolumetricBoundaryWork :
    ∀ leg,
      legProcessKind leg = .isovolumetric →
        workDoneByGasInJoules setup leg = 0
  firstLawOnEachLeg :
    ∀ leg,
      heatTransferredIntoGasInJoules setup leg =
        internalEnergyInJoules setup (legTarget leg) -
          internalEnergyInJoules setup (legSource leg) +
            workDoneByGasInJoules setup leg

/-! ## Answer choices and requested conclusion -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Joule value printed beside each answer label. -/
def displayedTotalHeatInJoules : AnswerChoice → ℝ
  | .A => -1800
  | .B => 1800
  | .C => 1600
  | .D => -1600

/-- Answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The source reports energy to the nearest hundred joules.  This predicate says
that the exact SI value lies within half of one `100 J` display interval.
-/
def RoundsToNearestHundredJoules (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 50

/-- A choice is uniquely closest to the exact derived heat. -/
def IsUniqueClosestDisplayedHeat
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |actual - displayedTotalHeatInJoules choice| <
      |actual - displayedTotalHeatInJoules other|

/-!
The two boundary-work contributions are `-16 L atm` and zero.  These values
are derived conclusions, not fields of a premise structure.
-/
lemma boundaryWorkAlongBDA
    (setup : IdealGasBDAProcess)
    (h_source : MatchesProblemAndPrimaryFigure setup)
    (h_laws : SatisfiesIdealGasProcessLaws setup) :
    workDoneByGasInJoules setup .bToD =
        -(16 * joulesPerLiterAtmosphere) ∧
      workDoneByGasInJoules setup .dToA = 0 ∧
      totalWorkDoneByGasInJoules setup =
        -(16 * joulesPerLiterAtmosphere) := by
  have h_work_bd :=
    h_laws.isobaricBoundaryWork .bToD (by rfl) h_source.compressionIsSlow
  have h_work_da :=
    h_laws.isovolumetricBoundaryWork .dToA (by rfl)
  simp only [legSource, legTarget] at h_work_bd
  norm_num [pressureInPascals, DimPressure.pascal,
    CarriesDimension.toDimensionful_apply_apply] at h_work_bd
  have h_pressure := h_source.pressureAtBIsTwoAtmospheres
  have h_volume_b := h_source.volumeAtBIsTenLiters
  have h_volume_d := h_source.volumeAtDIsTwoLiters
  norm_num [pressureInAtmospheres, DimPressure.standardAtmosphere,
    CarriesDimension.toDimensionful_apply_apply] at h_pressure
  norm_num [volumeInLiters] at h_volume_b h_volume_d
  have h_work_bd_exact :
      workDoneByGasInJoules setup .bToD =
        -(16 * joulesPerLiterAtmosphere) := by
    norm_num [joulesPerLiterAtmosphere]
    nlinarith [h_work_bd, h_pressure, h_volume_b, h_volume_d]
  refine ⟨h_work_bd_exact, h_work_da, ?_⟩
  simp [totalWorkDoneByGasInJoules, h_work_bd_exact, h_work_da]

/-- Equal endpoint temperatures give zero total internal-energy change. -/
lemma internalEnergyReturnsToInitialValue
    (setup : IdealGasBDAProcess)
    (h_source : MatchesProblemAndPrimaryFigure setup)
    (h_laws : SatisfiesIdealGasProcessLaws setup) :
    internalEnergyInJoules setup .A = internalEnergyInJoules setup .B := by
  exact h_laws.internalEnergyDependsOnlyOnTemperature .A .B
    h_source.finalTemperatureReturnsToInitial

/-!
The first law and cancellation of the intermediate internal energy give an
exact heat input of `-16 L atm = -8106/5 J = -1621.2 J`.
-/
lemma totalHeatAlongBDA_exact
    (setup : IdealGasBDAProcess)
    (h_source : MatchesProblemAndPrimaryFigure setup)
    (h_laws : SatisfiesIdealGasProcessLaws setup) :
    totalHeatIntoGasInJoules setup =
        -(16 * joulesPerLiterAtmosphere) ∧
      totalHeatIntoGasInJoules setup = -(8106 / 5) := by
  have h_work := boundaryWorkAlongBDA setup h_source h_laws
  have h_internal :=
    internalEnergyReturnsToInitialValue setup h_source h_laws
  have h_first_bd := h_laws.firstLawOnEachLeg .bToD
  have h_first_da := h_laws.firstLawOnEachLeg .dToA
  simp only [legSource, legTarget] at h_first_bd h_first_da
  have h_exact :
      totalHeatIntoGasInJoules setup =
        -(16 * joulesPerLiterAtmosphere) := by
    rw [totalHeatIntoGasInJoules, h_first_bd, h_first_da,
      h_work.1, h_work.2.1, h_internal]
    ring
  refine ⟨h_exact, h_exact.trans ?_⟩
  norm_num [joulesPerLiterAtmosphere]

/-!
Thus the total heat flow into the gas is exactly `-1621.2 J`; at the precision
of the displayed choices this is `-1600 J`, recorded answer D.

Blueprint: `thm:physics:phyx_mini_0491:target`.
-/
theorem problem_phyx_mini_0491
    (setup : IdealGasBDAProcess)
    (h_source : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesIdealGasProcessLaws setup) :
    totalHeatIntoGasInJoules setup = -(8106 / 5) ∧
      RoundsToNearestHundredJoules
        (totalHeatIntoGasInJoules setup)
        (displayedTotalHeatInJoules recordedAnswerChoice) ∧
      IsUniqueClosestDisplayedHeat
        (totalHeatIntoGasInJoules setup) recordedAnswerChoice := by
  have h_exact :=
    (totalHeatAlongBDA_exact setup h_source h_laws).2
  refine ⟨h_exact, ?_, ?_⟩
  · rw [h_exact]
    norm_num [RoundsToNearestHundredJoules, recordedAnswerChoice,
      displayedTotalHeatInJoules, abs_of_nonneg, abs_of_nonpos]
  · rw [h_exact]
    intro other h_other
    cases other with
    | A =>
        norm_num [recordedAnswerChoice, displayedTotalHeatInJoules,
          abs_of_nonneg, abs_of_nonpos]
    | B =>
        norm_num [recordedAnswerChoice, displayedTotalHeatInJoules,
          abs_of_nonneg, abs_of_nonpos]
    | C =>
        norm_num [recordedAnswerChoice, displayedTotalHeatInJoules,
          abs_of_nonneg, abs_of_nonpos]
    | D => exact (h_other rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0491

import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0152

open Dimension

/-!
# Refractive index from a gas-cell interferometer

An initially evacuated cell lies in the horizontal arm of the interferometer.
The supplied figure shows that light crosses the cell on the way from the
splitting mirror `M_S` to `M_2` and crosses it again after reflection. Filling
the cell therefore changes the round-trip optical path by
`2 L (n_gas - n_vacuum)`. The observed fringe count relates this optical-path
change to the vacuum wavelength.

Lengths are represented by genuine Physlib dimensionful quantities. Real
numbers are used only for unit readouts, schematic coordinates, angles, and
the dimensionless refractive index.
-/

/-- A signed physical length with coherent readouts in every unit system. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The SI scalar readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The scalar readout of a physical length, in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := LengthUnit.centimeters }).val

/-- The scalar readout of a physical length, in nanometres. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := LengthUnit.nanometers }).val

/-- The two cell states compared during the slowly performed experiment. -/
inductive CellState where
  | evacuated
  | gasAtFinalDensity
  deriving DecidableEq, Repr

/-- Labels in the source figure, together with the stated observation line. -/
inductive FigureElement where
  | source
  | splittingMirrorMS
  | mirrorM1
  | glassContainer
  | mirrorM2
  | referenceLine
  deriving DecidableEq, Repr

/-- Directed pieces of the beam path visible in the source figure. -/
inductive BeamLeg where
  | sourceToMS
  | msToM1
  | m1ToMS
  | msToM2
  | m2ToMS
  | recombinedOutput
  deriving DecidableEq, Repr

/-- Cardinal directions used to transcribe the arrows in the figure. -/
inductive PropagationDirection where
  | leftward
  | rightward
  | upward
  | downward
  deriving DecidableEq, Repr

/-
The physical quantities measured in the filling experiment and the auxiliary
data needed to transcribe its figure. The refractive-index field gives an
unknown dimensionless readout at each cell state; it does not contain the
requested numerical answer.
-/
structure GasCellInterferometer where
  containerInteriorDepth : LengthQuantity
  vacuumWavelength : LengthQuantity
  opticalPathIncrease : LengthQuantity
  darkFringesPastReferenceLine : ℕ
  refractiveIndex : CellState → ℝ
  cellTraversalCount : ℕ
  fringeObservationSite : FigureElement
  figureX : FigureElement → ℝ
  figureY : FigureElement → ℝ
  elementOrientationDegrees : FigureElement → ℝ
  beamDirection : BeamLeg → PropagationDirection
  legCrossesContainer : BeamLeg → Bool

/-
Problem/data readouts: the cell is `1.155 cm` deep, the vacuum wavelength is
`632.8 nm`, and 158 dark fringes pass the stated reference line.
-/
def HasStatedReadouts (setup : GasCellInterferometer) : Prop :=
  lengthInCentimeters setup.containerInteriorDepth = 1.155 ∧
    lengthInNanometers setup.vacuumWavelength = 632.8 ∧
    setup.darkFringesPastReferenceLine = 158 ∧
    setup.fringeObservationSite = .referenceLine

/-
Figure readout: source, `M_S`, cell, and `M_2` are ordered along the horizontal
arm, while the `M_1` arm rises from `M_S`. The 45-degree splitting mirror sends
light into both arms. The cell lies on the outbound and return portions of the
`M_2` arm, giving two traversals.
-/
def MatchesSourceFigure (setup : GasCellInterferometer) : Prop :=
  let x := setup.figureX
  let y := setup.figureY
  x .source < x .splittingMirrorMS ∧
    x .splittingMirrorMS < x .glassContainer ∧
    x .glassContainer < x .mirrorM2 ∧
    y .source = y .splittingMirrorMS ∧
    y .splittingMirrorMS = y .glassContainer ∧
    y .glassContainer = y .mirrorM2 ∧
    x .mirrorM1 = x .splittingMirrorMS ∧
    y .splittingMirrorMS < y .mirrorM1 ∧
    setup.elementOrientationDegrees .splittingMirrorMS = 45 ∧
    setup.elementOrientationDegrees .mirrorM2 = 90 ∧
    setup.beamDirection .sourceToMS = .rightward ∧
    setup.beamDirection .msToM1 = .upward ∧
    setup.beamDirection .m1ToMS = .downward ∧
    setup.beamDirection .msToM2 = .rightward ∧
    setup.beamDirection .m2ToMS = .leftward ∧
    setup.beamDirection .recombinedOutput = .downward ∧
    setup.legCrossesContainer .sourceToMS = false ∧
    setup.legCrossesContainer .msToM1 = false ∧
    setup.legCrossesContainer .m1ToMS = false ∧
    setup.legCrossesContainer .msToM2 = true ∧
    setup.legCrossesContainer .m2ToMS = true ∧
    setup.legCrossesContainer .recombinedOutput = false ∧
    setup.cellTraversalCount = 2

/-- Positivity and monotonicity conditions for the measured physical system. -/
def HasPhysicalParameters (setup : GasCellInterferometer) : Prop :=
  0 < lengthInMeters setup.containerInteriorDepth ∧
    0 < lengthInMeters setup.vacuumWavelength ∧
    0 ≤ lengthInMeters setup.opticalPathIncrease ∧
    0 < setup.refractiveIndex .evacuated ∧
    0 < setup.refractiveIndex .gasAtFinalDensity ∧
    setup.refractiveIndex .evacuated ≤
      setup.refractiveIndex .gasAtFinalDensity

/-- The initially evacuated cell has the vacuum refractive index `1`. -/
def HasVacuumReferenceIndex (setup : GasCellInterferometer) : Prop :=
  setup.refractiveIndex .evacuated = 1

/-
Governing optical-path law. Since the glass walls do not change while the gas
is admitted, only the container interior contributes to the path increase.
The traversal count is supplied independently by the source figure.
-/
def ObeysGasCellOpticalPathLaw (setup : GasCellInterferometer) : Prop :=
  lengthInMeters setup.opticalPathIncrease =
    (setup.cellTraversalCount : ℝ) *
      lengthInMeters setup.containerInteriorDepth *
        (setup.refractiveIndex .gasAtFinalDensity -
          setup.refractiveIndex .evacuated)

/-
Governing fringe-counting law: one complete fringe passage corresponds to one
vacuum wavelength of accumulated optical-path change.
-/
def ObeysFringeCountingLaw (setup : GasCellInterferometer) : Prop :=
  lengthInMeters setup.opticalPathIncrease =
    (setup.darkFringesPastReferenceLine : ℝ) *
      lengthInMeters setup.vacuumWavelength

/-- Labels of the four numerical choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The displayed dimensionless refractive-index readout for each choice. -/
def answerRefractiveIndex : AnswerChoice → ℝ
  | .A => 1.004008
  | .B => 1.004828
  | .C => 1.004328
  | .D => 1.005018

/-
A six-decimal display is a nearest-millionth report of an exact value. This
distinguishes the rounded answer choice from the exact rational index.
-/
def IsNearestMillionthReadout (exact reported : ℝ) : Prop :=
  (∃ millionths : ℤ, reported = (millionths : ℝ) / 1000000) ∧
    |exact - reported| ≤ 1 / 2000000

/-
The double-pass and fringe-counting laws determine the exact refractive index
before it is rounded to match one of the displayed choices.
-/
lemma finalRefractiveIndex_eq_exact
    (setup : GasCellInterferometer)
    (h_data : HasStatedReadouts setup)
    (h_figure : MatchesSourceFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_vacuum : HasVacuumReferenceIndex setup)
    (h_opticalPath : ObeysGasCellOpticalPathLaw setup)
    (h_fringes : ObeysFringeCountingLaw setup) :
    setup.refractiveIndex .gasAtFinalDensity = 2071427 / 2062500 := by
  rcases h_data with
    ⟨h_depth_centimeters, h_wavelength_nanometers, h_fringe_count, _⟩
  rcases h_figure with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      h_traversal_count⟩
  have centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h_units := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.centimeters } : UnitChoices)
    have h_units_real := congrArg
      (fun reading : WithDim L𝓭 ℝ => reading.val) h_units
    norm_num [lengthInCentimeters, lengthInMeters, UnitChoices.dimScale,
      LengthUnit.centimeters, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val, NNReal.smul_def] at h_units_real ⊢
    exact h_units_real
  have nanometers_eq (length : LengthQuantity) :
      lengthInNanometers length = 1000000000 * lengthInMeters length := by
    have h_units := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    have h_units_real := congrArg
      (fun reading : WithDim L𝓭 ℝ => reading.val) h_units
    norm_num [lengthInNanometers, lengthInMeters, UnitChoices.dimScale,
      LengthUnit.nanometers, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val, NNReal.smul_def] at h_units_real ⊢
    exact h_units_real
  have h_depth_meters :
      lengthInMeters setup.containerInteriorDepth = 231 / 20000 := by
    nlinarith only
      [h_depth_centimeters, centimeters_eq setup.containerInteriorDepth]
  have h_wavelength_meters :
      lengthInMeters setup.vacuumWavelength = 791 / 1250000000 := by
    nlinarith only
      [h_wavelength_nanometers, nanometers_eq setup.vacuumWavelength]
  change setup.refractiveIndex .evacuated = 1 at h_vacuum
  change
    lengthInMeters setup.opticalPathIncrease =
      (setup.cellTraversalCount : ℝ) *
        lengthInMeters setup.containerInteriorDepth *
          (setup.refractiveIndex .gasAtFinalDensity -
            setup.refractiveIndex .evacuated) at h_opticalPath
  change
    lengthInMeters setup.opticalPathIncrease =
      (setup.darkFringesPastReferenceLine : ℝ) *
        lengthInMeters setup.vacuumWavelength at h_fringes
  rw [h_traversal_count, h_depth_meters, h_vacuum] at h_opticalPath
  rw [h_fringe_count, h_wavelength_meters] at h_fringes
  norm_num at h_opticalPath h_fringes ⊢
  linarith

/-
The gas has exact refractive index `2071427 / 2062500`. Its nearest-millionth
display is `1.004328`, which is answer choice C.

This formalizes `thm:physics:phyx_mini_0152:target`.
-/
theorem problem_phyx_mini_0152
    (setup : GasCellInterferometer)
    (h_data : HasStatedReadouts setup)
    (h_figure : MatchesSourceFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_vacuum : HasVacuumReferenceIndex setup)
    (h_opticalPath : ObeysGasCellOpticalPathLaw setup)
    (h_fringes : ObeysFringeCountingLaw setup) :
    setup.refractiveIndex .gasAtFinalDensity = 2071427 / 2062500 ∧
      IsNearestMillionthReadout
        (setup.refractiveIndex .gasAtFinalDensity)
        (answerRefractiveIndex .C) := by
  have h_exact := finalRefractiveIndex_eq_exact setup h_data h_figure
    h_physical h_vacuum h_opticalPath h_fringes
  refine ⟨h_exact, ?_⟩
  rw [h_exact]
  constructor
  · refine ⟨1004328, ?_⟩
    norm_num [answerRefractiveIndex]
  · norm_num [answerRefractiveIndex, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0152

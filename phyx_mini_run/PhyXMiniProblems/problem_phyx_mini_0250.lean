import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0250

open Dimension

/-!
# Refractive index from a Michelson gas-cell interferometer

A helium-neon laser illuminates a Michelson interferometer.  The primary
figure places a glass cell of interior thickness `d` in the horizontal `M₂`
arm, so the beam crosses the gas column once on the outward leg and once on
the return leg.  Filling the initially evacuated cell changes the round-trip
optical path by `2 d (n_gas - n_vacuum)`.  Each complete bright-dark-bright
shift accounts for one vacuum wavelength of that change.

Lengths are genuine Physlib dimensionful quantities.  Real numbers occur
only as unit readouts, schematic coordinates, and dimensionless refractive
indices.
-/

/-! ## Dimensionful quantities and scalar readouts -/

/-- A physical length represented independently of the chosen unit system. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The metre readout used by the governing optical-path laws. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The centimetre readout used for the cell thickness `d`. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The nanometre readout used for the helium-neon laser wavelength. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-! ## Physical states and labels -/

/-- The source type named in the problem statement. -/
inductive LaserKind where
  | heliumNeon
  deriving DecidableEq, Repr

/-- The two cell states compared during the slow filling experiment. -/
inductive CellState where
  | evacuated
  | gasAtAtmosphericPressure
  deriving DecidableEq, Repr

/-- The quasi-static preparation described by the prose. -/
inductive FillingProtocol where
  | slowlyFromVacuumToAtmosphericPressure
  deriving DecidableEq, Repr

/-- Brightness states of the central interference spot. -/
inductive FringeBrightness where
  | bright
  | dark
  deriving DecidableEq, Repr

/-- The complete fringe pattern counted once per observed shift. -/
inductive FringeShiftPattern where
  | brightDarkBright
  deriving DecidableEq, Repr

/-- The two Michelson arms, carrying the figure labels `L₁` and `L₂`. -/
inductive InterferometerArm where
  /-- The vertical arm ending at mirror `M₁`, whose length is `L₁`. -/
  | mirrorM1ArmL1
  /-- The horizontal cell arm ending at mirror `M₂`, whose length is `L₂`. -/
  | mirrorM2ArmL2
  deriving DecidableEq, Repr

/-- Optical components and the observer shown in the primary figure. -/
inductive FigureElement where
  | source
  | beamSplitter
  | mirrorM1
  | gasCell
  | mirrorM2
  | eye
  deriving DecidableEq, Repr

/-- Directed beam legs drawn in the primary figure. -/
inductive BeamLeg where
  | sourceToSplitter
  | splitterToM1
  | m1ToSplitter
  | splitterToM2
  | m2ToSplitter
  | splitterToEye
  deriving DecidableEq, Repr

/-- Cardinal directions used to transcribe the beam arrows. -/
inductive PropagationDirection where
  | leftward
  | rightward
  | upward
  | downward
  deriving DecidableEq, Repr

/-!
The physical quantities and figure data of the interferometer.

`refractiveIndex` is an unknown dimensionless material readout at each cell
state.  The field does not contain the requested numerical answer.
-/
structure MichelsonGasCellExperiment where
  sourceKind : LaserKind
  vacuumWavelength : LengthQuantity
  cellInteriorThickness : LengthQuantity
  beamSplitterToMirrorDistance : InterferometerArm → LengthQuantity
  refractiveIndex : CellState → ℝ
  opticalPathIncrease : LengthQuantity
  completeFringeShiftCount : ℕ
  initialCentralSpotBrightness : FringeBrightness
  observedShiftPattern : FringeShiftPattern
  fillingProtocol : FillingProtocol
  cellArm : InterferometerArm
  cellTraversalCount : ℕ
  outputObserver : FigureElement
  mirrorIsAdjustable : InterferometerArm → Bool
  figureX : FigureElement → ℝ
  figureY : FigureElement → ℝ
  beamDirection : BeamLeg → PropagationDirection
  legCrossesCell : BeamLeg → Bool

/-! ## Assumption/target split -/

/-
The source readouts and observed fringe record.  This predicate fixes neither
the final refractive index nor any answer choice.
-/
def HasStatedProblemReadouts (setup : MichelsonGasCellExperiment) : Prop :=
  setup.sourceKind = .heliumNeon ∧
    lengthInNanometers setup.vacuumWavelength = 633 ∧
    lengthInCentimeters setup.cellInteriorThickness = 4 ∧
    setup.completeFringeShiftCount = 43 ∧
    setup.initialCentralSpotBrightness = .bright ∧
    setup.observedShiftPattern = .brightDarkBright ∧
    setup.fillingProtocol = .slowlyFromVacuumToAtmosphericPressure

/-
Figure transcription: `M₁` is above the splitter, while the gas cell and
adjustable `M₂` are to its right.  The eye is below the recombined output.
Only the outward and return `M₂` legs cross the cell, giving two traversals.
-/
def MatchesSourceFigure (setup : MichelsonGasCellExperiment) : Prop :=
  let x := setup.figureX
  let y := setup.figureY
  x .source < x .beamSplitter ∧
    x .beamSplitter < x .gasCell ∧
    x .gasCell < x .mirrorM2 ∧
    y .source = y .beamSplitter ∧
    y .beamSplitter = y .gasCell ∧
    y .gasCell = y .mirrorM2 ∧
    x .mirrorM1 = x .beamSplitter ∧
    y .beamSplitter < y .mirrorM1 ∧
    x .eye = x .beamSplitter ∧
    y .eye < y .beamSplitter ∧
    setup.cellArm = .mirrorM2ArmL2 ∧
    setup.outputObserver = .eye ∧
    setup.mirrorIsAdjustable .mirrorM1ArmL1 = false ∧
    setup.mirrorIsAdjustable .mirrorM2ArmL2 = true ∧
    setup.beamDirection .sourceToSplitter = .rightward ∧
    setup.beamDirection .splitterToM1 = .upward ∧
    setup.beamDirection .m1ToSplitter = .downward ∧
    setup.beamDirection .splitterToM2 = .rightward ∧
    setup.beamDirection .m2ToSplitter = .leftward ∧
    setup.beamDirection .splitterToEye = .downward ∧
    setup.legCrossesCell .sourceToSplitter = false ∧
    setup.legCrossesCell .splitterToM1 = false ∧
    setup.legCrossesCell .m1ToSplitter = false ∧
    setup.legCrossesCell .splitterToM2 = true ∧
    setup.legCrossesCell .m2ToSplitter = true ∧
    setup.legCrossesCell .splitterToEye = false ∧
    setup.cellTraversalCount = 2

/-- Positivity and monotonicity conditions for the physical experiment. -/
def HasPhysicalParameters (setup : MichelsonGasCellExperiment) : Prop :=
  0 < lengthInMeters setup.vacuumWavelength ∧
    0 < lengthInMeters setup.cellInteriorThickness ∧
    0 < lengthInMeters
      (setup.beamSplitterToMirrorDistance .mirrorM1ArmL1) ∧
    0 < lengthInMeters
      (setup.beamSplitterToMirrorDistance .mirrorM2ArmL2) ∧
    lengthInMeters setup.cellInteriorThickness ≤
      lengthInMeters
        (setup.beamSplitterToMirrorDistance .mirrorM2ArmL2) ∧
    0 ≤ lengthInMeters setup.opticalPathIncrease ∧
    0 < setup.refractiveIndex .evacuated ∧
    setup.refractiveIndex .evacuated ≤
      setup.refractiveIndex .gasAtAtmosphericPressure

/-- The evacuated reference state has vacuum refractive index one. -/
def HasVacuumReferenceIndex (setup : MichelsonGasCellExperiment) : Prop :=
  setup.refractiveIndex .evacuated = 1

/-
The governing gas-cell optical-path law.  The unchanged glass walls cancel
between the two cell states, so only the gas-column index change contributes.
-/
def ObeysRoundTripOpticalPathLaw
    (setup : MichelsonGasCellExperiment) : Prop :=
  lengthInMeters setup.opticalPathIncrease =
    (setup.cellTraversalCount : ℝ) *
      lengthInMeters setup.cellInteriorThickness *
        (setup.refractiveIndex .gasAtAtmosphericPressure -
          setup.refractiveIndex .evacuated)

/-
The governing fringe-counting law: every complete bright-dark-bright shift
corresponds to one vacuum wavelength of accumulated optical-path change.
-/
def ObeysCompleteFringeShiftLaw
    (setup : MichelsonGasCellExperiment) : Prop :=
  lengthInMeters setup.opticalPathIncrease =
    (setup.completeFringeShiftCount : ℝ) *
      lengthInMeters setup.vacuumWavelength

/-! ## Requested result and displayed choices -/

/-- Labels of the four numerical choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless refractive-index readout displayed by each choice. -/
def answerRefractiveIndex : AnswerChoice → ℝ
  | .A => 50017 / 50000
  | .B => 100031 / 100000
  | .C => 50021 / 50000
  | .D => 25007 / 25000

/-- Agreement with a five-decimal display by nearest-value rounding. -/
def IsNearestHundredThousandthReadout (exact reported : ℝ) : Prop :=
  (∃ hundredThousandths : ℤ,
      reported = (hundredThousandths : ℝ) / 100000) ∧
    |exact - reported| ≤ 1 / 200000

/-
The double-pass geometry and the two governing laws first determine the exact
dimensionless index at atmospheric pressure.
-/
lemma gasRefractiveIndex_eq_exact
    (setup : MichelsonGasCellExperiment)
    (h_readouts : HasStatedProblemReadouts setup)
    (h_figure : MatchesSourceFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_vacuum : HasVacuumReferenceIndex setup)
    (h_opticalPath : ObeysRoundTripOpticalPathLaw setup)
    (h_fringes : ObeysCompleteFringeShiftLaw setup) :
    setup.refractiveIndex .gasAtAtmosphericPressure =
      80027219 / 80000000 := by
  unfold HasStatedProblemReadouts at h_readouts
  rcases h_readouts with
    ⟨_, h_wavelength_nm, h_thickness_cm, h_count, _⟩
  have h_traversals : setup.cellTraversalCount = 2 := by
    unfold MatchesSourceFigure at h_figure
    tauto
  unfold HasVacuumReferenceIndex at h_vacuum
  unfold ObeysRoundTripOpticalPathLaw at h_opticalPath
  unfold ObeysCompleteFringeShiftLaw at h_fringes
  have h_wavelength_m :
      lengthInMeters setup.vacuumWavelength = 633 / 1000000000 := by
    let u_nm : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.nanometers }
    let u_m : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.meters }
    have h_units := congrArg WithDim.val
      (setup.vacuumWavelength.2 u_nm u_m)
    simp only [WithDim.smul_val] at h_units
    have h_nm_val : (setup.vacuumWavelength u_nm).val = 633 := by
      simpa [u_nm, lengthInNanometers, lengthReadout] using h_wavelength_nm
    rw [h_nm_val] at h_units
    have h_scale :
        (u_nm.dimScale u_m (dim (WithDim L𝓭 ℝ)) : ℝ) =
          1 / 1000000000 := by
      dsimp [u_nm, u_m]
      norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
        NNReal.coe_inv]
      rfl
    simp only [NNReal.smul_def, smul_eq_mul] at h_units
    rw [h_scale] at h_units
    convert h_units using 1 <;>
      norm_num [lengthInMeters, lengthReadout, u_m]
  have h_thickness_m :
      lengthInMeters setup.cellInteriorThickness = 4 / 100 := by
    let u_cm : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.centimeters }
    let u_m : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.meters }
    have h_units := congrArg WithDim.val
      (setup.cellInteriorThickness.2 u_cm u_m)
    simp only [WithDim.smul_val] at h_units
    have h_cm_val : (setup.cellInteriorThickness u_cm).val = 4 := by
      simpa [u_cm, lengthInCentimeters, lengthReadout] using h_thickness_cm
    rw [h_cm_val] at h_units
    have h_scale :
        (u_cm.dimScale u_m (dim (WithDim L𝓭 ℝ)) : ℝ) =
          1 / 100 := by
      dsimp [u_cm, u_m]
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
        NNReal.coe_inv]
      rfl
    simp only [NNReal.smul_def, smul_eq_mul] at h_units
    rw [h_scale] at h_units
    convert h_units using 1 <;>
      norm_num [lengthInMeters, lengthReadout, u_m]
  norm_num [h_traversals, h_count, h_vacuum, h_wavelength_m,
    h_thickness_m] at h_opticalPath h_fringes ⊢
  linarith

/-
The exact index `80027219 / 80000000 = 1.0003402375` rounds to `1.00034`,
which is answer choice A.

Blueprint: `thm:physics:phyx_mini_0250:target`.
-/
theorem problem_phyx_mini_0250
    (setup : MichelsonGasCellExperiment)
    (h_readouts : HasStatedProblemReadouts setup)
    (h_figure : MatchesSourceFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_vacuum : HasVacuumReferenceIndex setup)
    (h_opticalPath : ObeysRoundTripOpticalPathLaw setup)
    (h_fringes : ObeysCompleteFringeShiftLaw setup) :
    setup.refractiveIndex .gasAtAtmosphericPressure =
        80027219 / 80000000 ∧
      IsNearestHundredThousandthReadout
        (setup.refractiveIndex .gasAtAtmosphericPressure)
        (answerRefractiveIndex .A) := by
  have h_exact := gasRefractiveIndex_eq_exact setup h_readouts h_figure
    h_physical h_vacuum h_opticalPath h_fringes
  refine ⟨h_exact, ?_⟩
  unfold IsNearestHundredThousandthReadout answerRefractiveIndex
  constructor
  · refine ⟨100034, ?_⟩
    norm_num
  · rw [h_exact]
    norm_num [abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0250

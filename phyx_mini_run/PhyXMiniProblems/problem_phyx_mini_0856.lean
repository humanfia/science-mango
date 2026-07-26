import Mathlib
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0856

open Dimension

/-!
# Kinetic energy of an oscillating electric dipole at alignment

The primary figure plots the electric-dipole potential energy `U(φ)` in
microjoules against the angle `φ` in degrees.  It has the negative-cosine
shape appropriate to a dipole in a uniform electric field, with
`U(0°) = -2 μJ` and `U(±180°) = 2 μJ`.  The dipole oscillates between the
turning angles `±60°`.

Energy and the electromagnetic magnitudes are represented by Physlib
dimensionful quantities.  Mathlib's `Real.Angle` records angles modulo a full
turn.  Scalar real numbers are used only for coherent-SI and plotted-axis
readouts.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- The dimension `C L` of the magnitude of an electric dipole moment. -/
def electricDipoleMomentDimension : Dimension := C𝓭 * L𝓭

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent electric-dipole-moment magnitude. -/
abbrev ElectricDipoleMomentMagnitude : Type :=
  Dimensionful (WithDim electricDipoleMomentDimension NNReal)

/-- A nonnegative, unit-independent electric-field-strength magnitude. -/
abbrev ElectricFieldStrengthMagnitude : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Electric-dipole-moment magnitude in coulomb-metres. -/
def dipoleMomentInCoulombMeters
    (moment : ElectricDipoleMomentMagnitude) : ℝ :=
  nonnegativeSIReadout moment

/-- Electric-field-strength magnitude in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthMagnitude) : ℝ :=
  nonnegativeSIReadout strength

/-- Construct a signed physical energy from its coherent-SI joule readout. -/
def joules (value : ℝ) : DimEnergy :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-- Construct a signed physical energy from its microjoule readout. -/
def microjoules (value : ℝ) : DimEnergy :=
  joules (value / (10 : ℝ) ^ 6)

/-- Read a signed physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a signed physical energy in microjoules. -/
def energyInMicrojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy * (10 : ℝ) ^ 6

/-! ## Angles from the plotted degree axis -/

/-- Convert a real-valued degree readout to a geometric angle. -/
def degreesToAngle (angleInDegrees : ℝ) : Real.Angle :=
  ((angleInDegrees * Real.pi / 180 : ℝ) : Real.Angle)

/-- Alignment of the dipole moment with the electric field, `φ = 0`. -/
def alignedAngle : Real.Angle := 0

/-- The magnitude of either stated turning angle, `60°`. -/
def sixtyDegrees : Real.Angle := degreesToAngle 60

/-- Anti-alignment, represented by the `180°` tick. -/
def antiAlignedAngle : Real.Angle := degreesToAngle 180

/-! ## Primary-figure vocabulary -/

/-- The two axes visible in the supplied graph. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- The physical or geometric quantity assigned to a graph axis. -/
inductive FigureAxisQuantity where
  | dipoleAngle
  | potentialEnergy
  deriving DecidableEq, Repr

/-- The unit printed beside a graph axis. -/
inductive FigureAxisUnit where
  | degrees
  | microjoules
  deriving DecidableEq, Repr

/-- The three labeled angular ticks in image `856.png`. -/
inductive AngleTick where
  | leftAntiAligned
  | aligned
  | rightAntiAligned
  deriving DecidableEq, Fintype, Repr

/-- The three labeled energy ticks in image `856.png`. -/
inductive PotentialEnergyTick where
  | lower
  | zero
  | upper
  deriving DecidableEq, Fintype, Repr

/-- Qualitative shape of the plotted potential-energy trace. -/
inductive TraceShape where
  | negativeCosine
  | other
  deriving DecidableEq, Repr

/-- Color of the plotted trace in the primary raster. -/
inductive TraceColor where
  | blue
  | other
  deriving DecidableEq, Repr

/-- Typed data represented by the potential-energy graph. -/
structure DipolePotentialEnergyFigure where
  axisQuantity : FigureAxis → FigureAxisQuantity
  axisUnit : FigureAxis → FigureAxisUnit
  angleTickInDegrees : AngleTick → ℝ
  potentialEnergyTickInMicrojoules : PotentialEnergyTick → ℝ
  plottedPotentialEnergyAt : Real.Angle → DimEnergy
  traceShape : TraceShape
  traceColor : TraceColor

/-! ## Physical setup and source assumptions -/

/-- The external-field model relevant to the standard dipole energy law. -/
inductive ExternalFieldModel where
  | uniform
  | other
  deriving DecidableEq, Repr

/--
Independent physical observables for the oscillating dipole.  The energy
functions are not defined from one another; their relation is imposed by the
governing laws below.
-/
structure OscillatingElectricDipole where
  externalFieldModel : ExternalFieldModel
  dipoleMomentMagnitude : ElectricDipoleMomentMagnitude
  electricFieldStrength : ElectricFieldStrengthMagnitude
  turningAngleMagnitude : Real.Angle
  traversedAngle : Real.Angle → Prop
  potentialEnergyAt : Real.Angle → DimEnergy
  kineticEnergyAt : Real.Angle → DimEnergy
  totalMechanicalEnergy : DimEnergy
  figure : DipolePotentialEnergyFigure

/--
Literal axis labels, ticks, and calibrated potential-energy readouts from the
primary raster.  These are figure/data premises and do not state the requested
kinetic energy at alignment.
-/
structure MatchesPrimaryFigure
    (setup : OscillatingElectricDipole) : Prop where
  horizontalAxisIsAngle :
    setup.figure.axisQuantity .horizontal = .dipoleAngle
  verticalAxisIsPotentialEnergy :
    setup.figure.axisQuantity .vertical = .potentialEnergy
  horizontalAxisUsesDegrees :
    setup.figure.axisUnit .horizontal = .degrees
  verticalAxisUsesMicrojoules :
    setup.figure.axisUnit .vertical = .microjoules
  leftAngleTick :
    setup.figure.angleTickInDegrees .leftAntiAligned = -180
  alignedAngleTick : setup.figure.angleTickInDegrees .aligned = 0
  rightAngleTick :
    setup.figure.angleTickInDegrees .rightAntiAligned = 180
  lowerEnergyTick :
    setup.figure.potentialEnergyTickInMicrojoules .lower = -2
  zeroEnergyTick :
    setup.figure.potentialEnergyTickInMicrojoules .zero = 0
  upperEnergyTick :
    setup.figure.potentialEnergyTickInMicrojoules .upper = 2
  traceIsNegativeCosine : setup.figure.traceShape = .negativeCosine
  traceIsBlue : setup.figure.traceColor = .blue
  plottedCurveRepresentsPhysicalPotential :
    ∀ angle,
      setup.figure.plottedPotentialEnergyAt angle =
        setup.potentialEnergyAt angle
  alignedPotentialReadout :
    energyInMicrojoules
        (setup.figure.plottedPotentialEnergyAt alignedAngle) = -2
  leftAntiAlignedPotentialReadout :
    energyInMicrojoules
        (setup.figure.plottedPotentialEnergyAt (-antiAlignedAngle)) = 2
  rightAntiAlignedPotentialReadout :
    energyInMicrojoules
        (setup.figure.plottedPotentialEnergyAt antiAlignedAngle) = 2
  plottedTraceWithinVerticalRange :
    ∀ angle,
      -2 ≤ energyInMicrojoules
          (setup.figure.plottedPotentialEnergyAt angle) ∧
        energyInMicrojoules
            (setup.figure.plottedPotentialEnergyAt angle) ≤ 2

/--
The prose statement that the dipole oscillates between `±60°`.  The two
endpoints are turning points, so their kinetic energy vanishes; alignment lies
on the traversed arc.  These facts are initial/trajectory data, not the current
conclusion.
-/
structure OscillatesBetweenSixtyDegrees
    (setup : OscillatingElectricDipole) : Prop where
  uniformExternalField : setup.externalFieldModel = .uniform
  turningAngleIsSixtyDegrees :
    setup.turningAngleMagnitude = sixtyDegrees
  alignedConfigurationIsTraversed : setup.traversedAngle alignedAngle
  positiveTurningPointIsTraversed :
    setup.traversedAngle setup.turningAngleMagnitude
  negativeTurningPointIsTraversed :
    setup.traversedAngle (-setup.turningAngleMagnitude)
  positiveTurningPointHasZeroKineticEnergy :
    energyInJoules
        (setup.kineticEnergyAt setup.turningAngleMagnitude) = 0
  negativeTurningPointHasZeroKineticEnergy :
    energyInJoules
        (setup.kineticEnergyAt (-setup.turningAngleMagnitude)) = 0

/-!
The governing electrostatic and mechanical laws.  The potential-energy law is
`U(φ) = -p E cos φ`; conservation and kinetic-energy nonnegativity are asserted
on the configurations actually traversed by the oscillation.  No field below
mentions the requested value `1 μJ`.
-/
structure SatisfiesElectricDipoleOscillationLaws
    (setup : OscillatingElectricDipole) : Prop where
  positiveDipoleMoment :
    0 < dipoleMomentInCoulombMeters setup.dipoleMomentMagnitude
  positiveElectricFieldStrength :
    0 < electricFieldStrengthInNewtonsPerCoulomb
      setup.electricFieldStrength
  uniformFieldDipolePotentialEnergy :
    ∀ angle,
      energyInJoules (setup.potentialEnergyAt angle) =
        -(dipoleMomentInCoulombMeters setup.dipoleMomentMagnitude *
            electricFieldStrengthInNewtonsPerCoulomb
              setup.electricFieldStrength *
            Real.Angle.cos angle)
  mechanicalEnergyConservation :
    ∀ angle,
      setup.traversedAngle angle →
        energyInJoules (setup.kineticEnergyAt angle) +
            energyInJoules (setup.potentialEnergyAt angle) =
          energyInJoules setup.totalMechanicalEnergy
  kineticEnergyNonnegative :
    ∀ angle,
      setup.traversedAngle angle →
        0 ≤ energyInJoules (setup.kineticEnergyAt angle)

/-! ## Displayed answers and current target -/

/-- Labels of the four kinetic-energy choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kinetic-energy readout, in microjoules, printed beside each choice. -/
def displayedKineticEnergyInMicrojoules : AnswerChoice → ℝ
  | .A => 11 / 10
  | .B => 6 / 5
  | .C => 13 / 10
  | .D => 1

/-- The answer label recorded by the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice matches the independently modeled aligned energy. -/
def AnswerMatchesAlignedKineticEnergy
    (setup : OscillatingElectricDipole) (choice : AnswerChoice) : Prop :=
  energyInMicrojoules (setup.kineticEnergyAt alignedAngle) =
    displayedKineticEnergyInMicrojoules choice

/--
At a `60°` turning point, `K = 0` and the negative-cosine potential is
`U(60°) = -1 μJ`.  At alignment the figure gives `U(0°) = -2 μJ`, so
conservation of mechanical energy yields `K(0°) = 1 μJ`, answer D.

This is the declaration for `thm:physics:phyx_mini_0856:target`.  Both the
numeric value and its match to the recorded answer occur only in the
conclusion.
-/
theorem kineticEnergyWhenAligned_eq_one_microjoule
    (setup : OscillatingElectricDipole)
    (hFigure : MatchesPrimaryFigure setup)
    (hOscillation : OscillatesBetweenSixtyDegrees setup)
    (hLaws : SatisfiesElectricDipoleOscillationLaws setup) :
    energyInMicrojoules (setup.kineticEnergyAt alignedAngle) = 1 ∧
      AnswerMatchesAlignedKineticEnergy setup recordedDatasetAnswer := by
  have hAlignedPotentialMicrojoules :
      energyInMicrojoules (setup.potentialEnergyAt alignedAngle) = -2 := by
    rw [← hFigure.plottedCurveRepresentsPhysicalPotential alignedAngle]
    exact hFigure.alignedPotentialReadout
  have hCosSixtyDegrees : Real.Angle.cos sixtyDegrees = 1 / 2 := by
    rw [sixtyDegrees, degreesToAngle, Real.Angle.cos_coe]
    have hAngle : (60 : ℝ) * Real.pi / 180 = Real.pi / 3 := by ring
    rw [hAngle, Real.cos_pi_div_three]
  have hAlignedPotentialJoules :=
    hLaws.uniformFieldDipolePotentialEnergy alignedAngle
  have hTurningPotentialJoules :=
    hLaws.uniformFieldDipolePotentialEnergy setup.turningAngleMagnitude
  rw [hOscillation.turningAngleIsSixtyDegrees, hCosSixtyDegrees] at hTurningPotentialJoules
  have hAlignedConservation :=
    hLaws.mechanicalEnergyConservation alignedAngle
      hOscillation.alignedConfigurationIsTraversed
  have hTurningConservation :=
    hLaws.mechanicalEnergyConservation setup.turningAngleMagnitude
      hOscillation.positiveTurningPointIsTraversed
  rw [hOscillation.positiveTurningPointHasZeroKineticEnergy, zero_add] at hTurningConservation
  rw [hOscillation.turningAngleIsSixtyDegrees] at hTurningConservation
  have hAlignedKineticEnergy :
      energyInMicrojoules (setup.kineticEnergyAt alignedAngle) = 1 := by
    norm_num [alignedAngle, energyInMicrojoules] at hAlignedPotentialMicrojoules
    norm_num [alignedAngle] at hAlignedPotentialJoules hAlignedConservation
    norm_num [alignedAngle, energyInMicrojoules]
    nlinarith [hTurningPotentialJoules, hAlignedConservation,
      hTurningConservation]
  exact ⟨hAlignedKineticEnergy, by
    simpa [AnswerMatchesAlignedKineticEnergy, recordedDatasetAnswer,
      displayedKineticEnergyInMicrojoules] using hAlignedKineticEnergy⟩

end PhyXMiniProblems.ProblemPhyXMini0856

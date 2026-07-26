import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0969

open Dimension MeasureTheory

/-!
# Magnetic field at the center of a rotating charged cylindrical shell

The primary image `969.png` shows a cylindrical side shell of radius `R` and
axial length `W`, centered at `O` with its axis along `x`. A total charge `Q`
is distributed uniformly on the shell and rotates with angular speed `ω`.
The highlighted strip of axial width `dx` is a circular ring carrying the
conventional current `dI`.

Lengths, charge, angular speed, current, permeability, and magnetic-flux
density are represented by Physlib unit-independent quantities. Real scalars
and vectors occur only at coherent-SI readout boundaries and in the displayed
answer expressions. In particular, the magnetic field at `O` is an independent
observable constrained by the ring Biot--Savart and superposition laws below;
it is not defined to equal any answer choice.
-/

/-! ## Physical dimensions, quantities, and coherent-SI readouts -/

/-- Angular speed has inverse-time dimension; radians are dimensionless. -/
def angularSpeedDimension : Dimension := T𝓭⁻¹

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Surface charge density has dimension charge per area. -/
def surfaceChargeDensityDimension : Dimension :=
  C𝓭 * L𝓭⁻¹ * L𝓭⁻¹

/-- Axial linear charge density has dimension charge per length. -/
def linearChargeDensityDimension : Dimension := C𝓭 * L𝓭⁻¹

/-- Ring current per unit axial length has dimension current per length. -/
def currentPerLengthDimension : Dimension :=
  electricCurrentDimension * L𝓭⁻¹

/-- Vacuum permeability has SI dimension `N A⁻² = M L C⁻²`. -/
def vacuumPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density has the tesla dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent coordinate along the cylinder axis. -/
abbrev AxialPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative total electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative angular-speed magnitude. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative conventional-current magnitude. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative surface charge density. -/
abbrev SurfaceChargeDensityQuantity : Type :=
  Dimensionful (WithDim surfaceChargeDensityDimension NNReal)

/-- A nonnegative charge per unit axial length. -/
abbrev LinearChargeDensityQuantity : Type :=
  Dimensionful (WithDim linearChargeDensityDimension NNReal)

/-- A nonnegative ring current per unit axial length. -/
abbrev RingCurrentPerLengthQuantity : Type :=
  Dimensionful (WithDim currentPerLengthDimension NNReal)

/-- A nonnegative magnetic permeability. -/
abbrev VacuumPermeabilityQuantity : Type :=
  Dimensionful (WithDim vacuumPermeabilityDimension NNReal)

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A coherent-SI three-dimensional vector readout. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Coherent-SI scalar readout of a nonnegative dimensionful quantity. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  coherentSIReadout length

/-- Read a signed axial coordinate in metres. -/
def axialPositionInMeters (position : AxialPositionQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Read a charge magnitude in coulombs. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  coherentSIReadout charge

/-- Read angular speed in radians per second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  coherentSIReadout angularSpeed

/-- Read a conventional-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  coherentSIReadout current

/-- Read surface charge density in coulombs per square metre. -/
def surfaceChargeDensityInCoulombsPerSquareMeter
    (density : SurfaceChargeDensityQuantity) : ℝ :=
  coherentSIReadout density

/-- Read axial charge density in coulombs per metre. -/
def linearChargeDensityInCoulombsPerMeter
    (density : LinearChargeDensityQuantity) : ℝ :=
  coherentSIReadout density

/-- Read ring current per axial metre in amperes per metre. -/
def ringCurrentPerLengthInAmperesPerMeter
    (density : RingCurrentPerLengthQuantity) : ℝ :=
  coherentSIReadout density

/-- Read vacuum permeability in newtons per ampere squared. -/
def vacuumPermeabilityInNewtonsPerAmpereSquared
    (permeability : VacuumPermeabilityQuantity) : ℝ :=
  coherentSIReadout permeability

/-- Read a magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityQuantity) : ℝ :=
  coherentSIReadout density

/-! ## Coordinates and primary-image vocabulary -/

/-- The three Cartesian axes, of which `x` is the cylinder axis. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Standard unit vector associated with a Cartesian axis. -/
def axisVector : CoordinateAxis → SpatialVector
  | .x => EuclideanSpace.single (0 : Fin 3) 1
  | .y => EuclideanSpace.single (1 : Fin 3) 1
  | .z => EuclideanSpace.single (2 : Fin 3) 1

/-- The coordinate origin carrying the label `O`. -/
def coordinateOrigin : Space 3 :=
  ⟨fun _ => 0⟩

/-- The physical part of the cylinder on which the charge resides. -/
inductive CylindricalShellPart where
  | curvedSideSurface
  | solidVolume
  | endCapsAndSide
  deriving DecidableEq, Repr

/-- Axial distribution of charge on the shell. -/
inductive ChargeDistribution where
  | uniformOnSideSurface
  | nonuniform
  deriving DecidableEq, Repr

/-- Time dependence of the rotation. -/
inductive RotationRegime where
  | constantAngularSpeed
  | timeDependent
  deriving DecidableEq, Repr

/-- Oriented sense of rotation about the displayed `x`-axis. -/
inductive RotationSense where
  | positiveAboutXAxis
  | negativeAboutXAxis
  deriving DecidableEq, Repr

/-- Vertical direction of an arrow as it appears in the side-view raster. -/
inductive SideViewArrowDirection where
  | downward
  | upward
  deriving DecidableEq, Repr

/-- Literal labels visible in image `969.png`. -/
inductive FigureLabel where
  | totalChargeQ
  | radiusR
  | axialLengthW
  | centerO
  | xCoordinate
  | angularSpeedOmega
  | differentialWidthDx
  | differentialCurrentDI
  deriving DecidableEq, Fintype, Repr

/-!
Presentation data read from the primary image. The dimensionful label values
are kept separate from the physical setup and calibrated below. The `dx` and
`dI` fields represent the highlighted narrow circular ring.
-/
structure RotatingChargedCylinderFigure where
  labelShown : FigureLabel → Bool
  cylindricalSideShellShown : Bool
  axisDrawnHorizontally : Bool
  highlightedRingSliceShown : Bool
  radiusLabel : LengthQuantity
  axialLengthLabel : LengthQuantity
  totalChargeLabel : ChargeMagnitudeQuantity
  angularSpeedLabel : AngularSpeedQuantity
  centerLabelPosition : Space 3
  axisLabel : CoordinateAxis
  highlightedSliceAxialPosition : AxialPositionQuantity
  highlightedSliceWidth : LengthQuantity
  highlightedSliceCurrent : ElectricCurrentQuantity
  angularSpeedArrowDirection : SideViewArrowDirection
  differentialCurrentArrowDirection : SideViewArrowDirection

/-!
Independent physical data for the rotating shell. The scalar function
`axialFieldContributionTeslasPerMeter` is the coherent-SI contribution density
of the ring at coordinate `x`; its value is constrained by Biot--Savart below.
-/
structure RotatingChargedCylindricalShellSetup where
  shellPart : CylindricalShellPart
  chargeDistribution : ChargeDistribution
  rotationRegime : RotationRegime
  rotationSense : RotationSense
  radius : LengthQuantity
  axialLength : LengthQuantity
  totalCharge : ChargeMagnitudeQuantity
  angularSpeed : AngularSpeedQuantity
  surfaceChargeDensity : SurfaceChargeDensityQuantity
  axialLinearChargeDensity : LinearChargeDensityQuantity
  ringCurrentPerAxialLength : RingCurrentPerLengthQuantity
  vacuumPermeability : VacuumPermeabilityQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  centerMagneticFluxDensity : MagneticFluxDensityQuantity
  magneticField : Electromagnetism.MagneticField 3
  observationTime : Time
  center : Space 3
  axis : CoordinateAxis
  highlightedSliceAxialPosition : AxialPositionQuantity
  highlightedSliceWidth : LengthQuantity
  highlightedSliceCurrent : ElectricCurrentQuantity
  axialFieldContributionTeslasPerMeter : ℝ → ℝ
  figure : RotatingChargedCylinderFigure

/-! ## Written scenario, figure readouts, geometry, and governing laws -/

/-- Qualitative and geometric information stated in the written problem. -/
structure MatchesWrittenRotatingChargedCylinderScenario
    (setup : RotatingChargedCylindricalShellSetup) : Prop where
  chargeLivesOnCurvedShell : setup.shellPart = .curvedSideSurface
  chargeIsUniform : setup.chargeDistribution = .uniformOnSideSurface
  rotationHasConstantAngularSpeed :
    setup.rotationRegime = .constantAngularSpeed
  centerIsOrigin : setup.center = coordinateOrigin
  cylinderAxisIsXAxis : setup.axis = .x

/-- Literal image evidence and calibration of all labelled quantities. -/
structure MatchesSuppliedRotatingChargedCylinderFigure
    (setup : RotatingChargedCylindricalShellSetup) : Prop where
  everyLabelIsShown : ∀ label, setup.figure.labelShown label = true
  cylindricalSideShellIsShown : setup.figure.cylindricalSideShellShown = true
  xAxisIsHorizontal : setup.figure.axisDrawnHorizontally = true
  differentialRingIsHighlighted :
    setup.figure.highlightedRingSliceShown = true
  radiusLabelAgrees : setup.figure.radiusLabel = setup.radius
  axialLengthLabelAgrees :
    setup.figure.axialLengthLabel = setup.axialLength
  totalChargeLabelAgrees :
    setup.figure.totalChargeLabel = setup.totalCharge
  angularSpeedLabelAgrees :
    setup.figure.angularSpeedLabel = setup.angularSpeed
  centerOLabelAgrees : setup.figure.centerLabelPosition = setup.center
  xAxisLabelAgrees : setup.figure.axisLabel = setup.axis
  slicePositionAgrees :
    setup.figure.highlightedSliceAxialPosition =
      setup.highlightedSliceAxialPosition
  dxLabelAgrees :
    setup.figure.highlightedSliceWidth = setup.highlightedSliceWidth
  dILabelAgrees :
    setup.figure.highlightedSliceCurrent = setup.highlightedSliceCurrent
  omegaArrowPointsDownInSideView :
    setup.figure.angularSpeedArrowDirection = .downward
  dIArrowPointsDownInSideView :
    setup.figure.differentialCurrentArrowDirection = .downward
  downwardArrowsEncodePositiveXAxisSense :
    setup.rotationSense = .positiveAboutXAxis

/-- Positivity and nondegeneracy conditions implicit in a physical shell. -/
structure HasPhysicalRotatingChargedCylinderParameters
    (setup : RotatingChargedCylindricalShellSetup) : Prop where
  radiusPositive : 0 < lengthInMeters setup.radius
  axialLengthPositive : 0 < lengthInMeters setup.axialLength
  totalChargePositive : 0 < chargeInCoulombs setup.totalCharge
  angularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond setup.angularSpeed
  vacuumPermeabilityPositive :
    0 < vacuumPermeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability
  highlightedSliceWidthPositive :
    0 < lengthInMeters setup.highlightedSliceWidth
  highlightedSliceLiesOnShell :
    |axialPositionInMeters setup.highlightedSliceAxialPosition| ≤
      lengthInMeters setup.axialLength / 2
  highlightedSliceFitsAxially :
    lengthInMeters setup.highlightedSliceWidth ≤
      lengthInMeters setup.axialLength

/-!
Physlib's `EMSystem.μ₀` is a coherent-coordinate scalar. This assumption
calibrates it to the separate dimensionful vacuum-permeability quantity.
-/
structure UsesCoherentSIVacuumPermeability
    (setup : RotatingChargedCylindricalShellSetup) : Prop where
  permeabilityReadoutAgreesWithEMSystem :
    vacuumPermeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability =
      setup.electromagneticSystem.μ₀

/-!
Uniform-charge and rotation laws. The curved surface area is `2πRW`, the
charge per axial length is `2πRσ = Q/W`, and a ring of charge `dq` rotating
with angular speed `ω` carries current `dI = ω dq/(2π)`. The final field is
not mentioned here.
-/
structure SatisfiesUniformRotatingSurfaceChargeModel
    (setup : RotatingChargedCylindricalShellSetup) : Prop where
  uniformSurfaceChargeDensity :
    surfaceChargeDensityInCoulombsPerSquareMeter setup.surfaceChargeDensity =
      chargeInCoulombs setup.totalCharge /
        (2 * Real.pi * lengthInMeters setup.radius *
          lengthInMeters setup.axialLength)
  axialLinearDensityFromSurfaceDensity :
    linearChargeDensityInCoulombsPerMeter setup.axialLinearChargeDensity =
      2 * Real.pi * lengthInMeters setup.radius *
        surfaceChargeDensityInCoulombsPerSquareMeter
          setup.surfaceChargeDensity
  ringCurrentDensityFromRotation :
    ringCurrentPerLengthInAmperesPerMeter setup.ringCurrentPerAxialLength =
      linearChargeDensityInCoulombsPerMeter setup.axialLinearChargeDensity *
        angularSpeedInRadiansPerSecond setup.angularSpeed /
          (2 * Real.pi)
  highlightedDifferentialRingCurrent :
    currentInAmperes setup.highlightedSliceCurrent =
      ringCurrentPerLengthInAmperesPerMeter
          setup.ringCurrentPerAxialLength *
        lengthInMeters setup.highlightedSliceWidth

/-!
For a circular ring at axial coordinate `x`, Biot--Savart gives the axial
field kernel

`dB/dx = μ₀ (dI/dx) R² / (2 (R² + x²)^(3/2))`.

The center field is the superposition of all rings from `-W/2` to `W/2`.
These hypotheses retain the unevaluated integrals and hence do not assume the
closed form requested by the problem.
-/
structure SatisfiesRingBiotSavartAndSuperposition
    (setup : RotatingChargedCylindricalShellSetup) : Prop where
  ringBiotSavartKernel : ∀ x : ℝ,
    x ∈ Set.Icc
        (-lengthInMeters setup.axialLength / 2)
        (lengthInMeters setup.axialLength / 2) →
      setup.axialFieldContributionTeslasPerMeter x =
        vacuumPermeabilityInNewtonsPerAmpereSquared
            setup.vacuumPermeability *
          ringCurrentPerLengthInAmperesPerMeter
            setup.ringCurrentPerAxialLength *
          lengthInMeters setup.radius ^ 2 /
          (2 *
            (Real.sqrt
              (lengthInMeters setup.radius ^ 2 + x ^ 2)) ^ 3)
  contributionIsIntervalIntegrable :
    IntervalIntegrable setup.axialFieldContributionTeslasPerMeter
      volume
      (-lengthInMeters setup.axialLength / 2)
      (lengthInMeters setup.axialLength / 2)
  centerMagnitudeIsRingSuperposition :
    magneticFluxDensityInTeslas setup.centerMagneticFluxDensity =
      ∫ x in
          (-lengthInMeters setup.axialLength / 2)..
            (lengthInMeters setup.axialLength / 2),
        setup.axialFieldContributionTeslasPerMeter x
  centerVectorIsRingSuperposition :
    setup.magneticField setup.observationTime setup.center =
      ∫ x in
          (-lengthInMeters setup.axialLength / 2)..
            (lengthInMeters setup.axialLength / 2),
        setup.axialFieldContributionTeslasPerMeter x •
          axisVector setup.axis

/-! ## Integral evaluation and displayed answer choices -/

/-!
The calculus identity used after substituting the uniform charge and rotation
relations. It is a conclusion to be proved, rather than a physical premise.
-/
lemma rotatingCylinderRingKernelIntegral
    (muZero charge angularSpeed radius axialLength : ℝ)
    (hRadius : 0 < radius)
    (hLength : 0 < axialLength) :
    (∫ x in (-axialLength / 2)..(axialLength / 2),
        muZero *
            (charge / axialLength * angularSpeed / (2 * Real.pi)) *
          radius ^ 2 /
          (2 * (Real.sqrt (radius ^ 2 + x ^ 2)) ^ 3)) =
      muZero / (2 * Real.pi) *
        (charge * angularSpeed /
          Real.sqrt (axialLength ^ 2 + 4 * radius ^ 2)) := by
  have hRadiusSq : 0 < radius ^ 2 := sq_pos_of_pos hRadius
  have hArgPos (x : ℝ) : 0 < radius ^ 2 + x ^ 2 :=
    add_pos_of_pos_of_nonneg hRadiusSq (sq_nonneg x)
  have hDerivative (x : ℝ) :
      HasDerivAt (fun y : ℝ => y / Real.sqrt (radius ^ 2 + y ^ 2))
        (radius ^ 2 / (Real.sqrt (radius ^ 2 + x ^ 2)) ^ 3) x := by
    have hsqrt_ne : Real.sqrt (radius ^ 2 + x ^ 2) ≠ 0 :=
      (Real.sqrt_pos.2 (hArgPos x)).ne'
    have hInner :
        HasDerivAt (fun y : ℝ => radius ^ 2 + y ^ 2) (2 * x) x := by
      convert! ((hasDerivAt_id x).pow 2).const_add (radius ^ 2) using 1
      all_goals norm_num
    have hSqrt :
        HasDerivAt (fun y : ℝ => Real.sqrt (radius ^ 2 + y ^ 2))
          (x / Real.sqrt (radius ^ 2 + x ^ 2)) x := by
      convert hInner.sqrt (ne_of_gt (hArgPos x)) using 1
      all_goals ring
    refine ((hasDerivAt_id x).div hSqrt hsqrt_ne).congr_deriv ?_
    simp only [id_eq]
    field_simp [hsqrt_ne]
    nlinarith [Real.sq_sqrt (le_of_lt (hArgPos x))]
  have hKernelContinuous :
      Continuous
        (fun x : ℝ =>
          radius ^ 2 / (Real.sqrt (radius ^ 2 + x ^ 2)) ^ 3) := by
    apply Continuous.div continuous_const
      ((continuous_const.add (continuous_id.pow 2)).sqrt.pow 3)
    intro x
    exact pow_ne_zero 3 (Real.sqrt_pos.2 (hArgPos x)).ne'
  have hKernelIntegral :
      (∫ x in (-axialLength / 2)..(axialLength / 2),
          radius ^ 2 / (Real.sqrt (radius ^ 2 + x ^ 2)) ^ 3) =
        (axialLength / 2) /
            Real.sqrt (radius ^ 2 + (axialLength / 2) ^ 2) -
          (-axialLength / 2) /
            Real.sqrt (radius ^ 2 + (-axialLength / 2) ^ 2) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hDerivative x)
      (hKernelContinuous.intervalIntegrable _ _)
  have hRadicandPos : 0 < axialLength ^ 2 + 4 * radius ^ 2 := by
    positivity
  have hSqrtRadicandPos :
      0 < Real.sqrt (axialLength ^ 2 + 4 * radius ^ 2) :=
    Real.sqrt_pos.2 hRadicandPos
  have hEndpointSqrt :
      Real.sqrt (radius ^ 2 + (axialLength / 2) ^ 2) =
        Real.sqrt (axialLength ^ 2 + 4 * radius ^ 2) / 2 := by
    rw [show radius ^ 2 + (axialLength / 2) ^ 2 =
        (axialLength ^ 2 + 4 * radius ^ 2) / 4 by ring]
    rw [Real.sqrt_div (le_of_lt hRadicandPos)]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2
      norm_num]
  rw [show
      (fun x : ℝ =>
          muZero *
              (charge / axialLength * angularSpeed / (2 * Real.pi)) *
            radius ^ 2 /
            (2 * (Real.sqrt (radius ^ 2 + x ^ 2)) ^ 3)) =
        fun x : ℝ =>
          (muZero *
              (charge / axialLength * angularSpeed / (2 * Real.pi)) / 2) *
            (radius ^ 2 /
              (Real.sqrt (radius ^ 2 + x ^ 2)) ^ 3) by
      funext x
      ring]
  rw [intervalIntegral.integral_const_mul, hKernelIntegral]
  rw [show radius ^ 2 + (-axialLength / 2) ^ 2 =
      radius ^ 2 + (axialLength / 2) ^ 2 by ring, hEndpointSqrt]
  field_simp [hLength.ne', Real.pi_ne_zero, hSqrtRadicandPos.ne']
  ring

/-- The four answer labels printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Choice C is printed as a scalar, while A, B, and D carry an explicit
`i`-hat. This sum type preserves that distinction rather than silently
turning every choice into a vector.
-/
inductive DisplayedMagneticFieldExpression where
  | axialVector (coefficientInTeslas : ℝ)
  | scalarMagnitude (magnitudeInTeslas : ℝ)

/-- The magnetic-field expression printed beside each answer label. -/
def AnswerChoice.displayedExpression
    (choice : AnswerChoice)
    (setup : RotatingChargedCylindricalShellSetup) :
    DisplayedMagneticFieldExpression :=
  match choice with
  | .A => .axialVector
      (setup.electromagneticSystem.μ₀ / (2 * Real.pi) *
        (chargeInCoulombs setup.totalCharge *
          angularSpeedInRadiansPerSecond setup.angularSpeed /
          Real.sqrt
            (lengthInMeters setup.axialLength ^ 2 +
              lengthInMeters setup.radius ^ 2)))
  | .B => .axialVector
      (setup.electromagneticSystem.μ₀ / (2 * Real.pi) *
        (chargeInCoulombs setup.totalCharge *
          angularSpeedInRadiansPerSecond setup.angularSpeed /
          Real.sqrt
            (lengthInMeters setup.axialLength ^ 2 +
              4 * lengthInMeters setup.radius ^ 2)))
  | .C => .scalarMagnitude
      (setup.electromagneticSystem.μ₀ /
          (2 * Real.pi * lengthInMeters setup.radius) *
        chargeInCoulombs setup.totalCharge *
        angularSpeedInRadiansPerSecond setup.angularSpeed)
  | .D => .axialVector
      (setup.electromagneticSystem.μ₀ *
          chargeInCoulombs setup.totalCharge *
          angularSpeedInRadiansPerSecond setup.angularSpeed /
        (2 * Real.pi * lengthInMeters setup.radius))

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed expression agrees with the independent modeled center field. -/
def MatchesModeledCenterField
    (setup : RotatingChargedCylindricalShellSetup)
    (choice : AnswerChoice) : Prop :=
  match choice.displayedExpression setup with
  | .axialVector coefficient =>
      setup.magneticField setup.observationTime setup.center =
        coefficient • axisVector .x
  | .scalarMagnitude magnitude =>
      magneticFluxDensityInTeslas setup.centerMagneticFluxDensity = magnitude

/-!
The uniformly charged rotating shell is the superposition of circular rings.
Evaluating the ring kernel yields

`B(O) = μ₀ Q ω / (2π √(W² + 4R²)) i`,

which is the vector expression printed as choice B. Both the closed form and
its match with the recorded choice are conclusions, not assumptions.

This declaration formalizes `thm:physics:phyx_mini_0969:target`.
-/
theorem problem_phyx_mini_0969
    (setup : RotatingChargedCylindricalShellSetup)
    (hScenario : MatchesWrittenRotatingChargedCylinderScenario setup)
    (hFigure : MatchesSuppliedRotatingChargedCylinderFigure setup)
    (hPhysical : HasPhysicalRotatingChargedCylinderParameters setup)
    (hPermeability : UsesCoherentSIVacuumPermeability setup)
    (hChargeRotation : SatisfiesUniformRotatingSurfaceChargeModel setup)
    (hBiotSavart : SatisfiesRingBiotSavartAndSuperposition setup) :
    magneticFluxDensityInTeslas setup.centerMagneticFluxDensity =
        setup.electromagneticSystem.μ₀ / (2 * Real.pi) *
          (chargeInCoulombs setup.totalCharge *
            angularSpeedInRadiansPerSecond setup.angularSpeed /
            Real.sqrt
              (lengthInMeters setup.axialLength ^ 2 +
                4 * lengthInMeters setup.radius ^ 2)) ∧
      setup.magneticField setup.observationTime setup.center =
        (setup.electromagneticSystem.μ₀ / (2 * Real.pi) *
          (chargeInCoulombs setup.totalCharge *
            angularSpeedInRadiansPerSecond setup.angularSpeed /
            Real.sqrt
              (lengthInMeters setup.axialLength ^ 2 +
                4 * lengthInMeters setup.radius ^ 2))) •
          axisVector .x ∧
      MatchesModeledCenterField setup recordedDatasetAnswer := by
  have hBounds :
      -lengthInMeters setup.axialLength / 2 ≤
        lengthInMeters setup.axialLength / 2 := by
    linarith [hPhysical.axialLengthPositive]
  have hLinearDensity :
      linearChargeDensityInCoulombsPerMeter setup.axialLinearChargeDensity =
        chargeInCoulombs setup.totalCharge /
          lengthInMeters setup.axialLength := by
    rw [hChargeRotation.axialLinearDensityFromSurfaceDensity,
      hChargeRotation.uniformSurfaceChargeDensity]
    field_simp [Real.pi_ne_zero, hPhysical.radiusPositive.ne',
      hPhysical.axialLengthPositive.ne']
  have hCurrentDensity :
      ringCurrentPerLengthInAmperesPerMeter
          setup.ringCurrentPerAxialLength =
        chargeInCoulombs setup.totalCharge /
            lengthInMeters setup.axialLength *
          angularSpeedInRadiansPerSecond setup.angularSpeed /
            (2 * Real.pi) := by
    rw [hChargeRotation.ringCurrentDensityFromRotation, hLinearDensity]
  have hKernelAgreement :
      Set.EqOn setup.axialFieldContributionTeslasPerMeter
        (fun x : ℝ =>
          setup.electromagneticSystem.μ₀ *
              (chargeInCoulombs setup.totalCharge /
                  lengthInMeters setup.axialLength *
                angularSpeedInRadiansPerSecond setup.angularSpeed /
                  (2 * Real.pi)) *
            lengthInMeters setup.radius ^ 2 /
            (2 *
              (Real.sqrt
                (lengthInMeters setup.radius ^ 2 + x ^ 2)) ^ 3))
        (Set.uIcc
          (-lengthInMeters setup.axialLength / 2)
          (lengthInMeters setup.axialLength / 2)) := by
    intro x hx
    rw [Set.uIcc_of_le hBounds] at hx
    rw [hBiotSavart.ringBiotSavartKernel x hx,
      hPermeability.permeabilityReadoutAgreesWithEMSystem,
      hCurrentDensity]
  have hRawIntegral :
      (∫ x in
          (-lengthInMeters setup.axialLength / 2)..
            (lengthInMeters setup.axialLength / 2),
          setup.axialFieldContributionTeslasPerMeter x) =
        setup.electromagneticSystem.μ₀ / (2 * Real.pi) *
          (chargeInCoulombs setup.totalCharge *
            angularSpeedInRadiansPerSecond setup.angularSpeed /
              Real.sqrt
                (lengthInMeters setup.axialLength ^ 2 +
                  4 * lengthInMeters setup.radius ^ 2)) := by
    calc
      (∫ x in
          (-lengthInMeters setup.axialLength / 2)..
            (lengthInMeters setup.axialLength / 2),
          setup.axialFieldContributionTeslasPerMeter x) =
          ∫ x in
            (-lengthInMeters setup.axialLength / 2)..
              (lengthInMeters setup.axialLength / 2),
            setup.electromagneticSystem.μ₀ *
                (chargeInCoulombs setup.totalCharge /
                    lengthInMeters setup.axialLength *
                  angularSpeedInRadiansPerSecond setup.angularSpeed /
                    (2 * Real.pi)) *
              lengthInMeters setup.radius ^ 2 /
              (2 *
                (Real.sqrt
                  (lengthInMeters setup.radius ^ 2 + x ^ 2)) ^ 3) :=
        intervalIntegral.integral_congr hKernelAgreement
      _ = setup.electromagneticSystem.μ₀ / (2 * Real.pi) *
          (chargeInCoulombs setup.totalCharge *
            angularSpeedInRadiansPerSecond setup.angularSpeed /
              Real.sqrt
                (lengthInMeters setup.axialLength ^ 2 +
                  4 * lengthInMeters setup.radius ^ 2)) :=
        rotatingCylinderRingKernelIntegral
          setup.electromagneticSystem.μ₀
          (chargeInCoulombs setup.totalCharge)
          (angularSpeedInRadiansPerSecond setup.angularSpeed)
          (lengthInMeters setup.radius)
          (lengthInMeters setup.axialLength)
          hPhysical.radiusPositive hPhysical.axialLengthPositive
  have hMagnitude :
      magneticFluxDensityInTeslas setup.centerMagneticFluxDensity =
        setup.electromagneticSystem.μ₀ / (2 * Real.pi) *
          (chargeInCoulombs setup.totalCharge *
            angularSpeedInRadiansPerSecond setup.angularSpeed /
              Real.sqrt
                (lengthInMeters setup.axialLength ^ 2 +
                  4 * lengthInMeters setup.radius ^ 2)) := by
    rw [hBiotSavart.centerMagnitudeIsRingSuperposition, hRawIntegral]
  have hVector :
      setup.magneticField setup.observationTime setup.center =
        (setup.electromagneticSystem.μ₀ / (2 * Real.pi) *
          (chargeInCoulombs setup.totalCharge *
            angularSpeedInRadiansPerSecond setup.angularSpeed /
              Real.sqrt
                (lengthInMeters setup.axialLength ^ 2 +
                  4 * lengthInMeters setup.radius ^ 2))) •
          axisVector .x := by
    rw [hBiotSavart.centerVectorIsRingSuperposition,
      intervalIntegral.integral_smul_const, hRawIntegral,
      hScenario.cylinderAxisIsXAxis]
  refine ⟨hMagnitude, hVector, ?_⟩
  simpa [MatchesModeledCenterField, recordedDatasetAnswer,
    AnswerChoice.displayedExpression] using hVector

end PhyXMiniProblems.ProblemPhyXMini0969

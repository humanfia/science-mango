import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0852

open Dimension

/-!
# Charge on the inner surface of a concentric conducting shell

The primary raster shows a solid conducting sphere of radius `5 cm`, centered
inside a conducting spherical shell whose inner and outer radii are `10 cm`
and `15 cm`.  It also shows radial electric-field samples of magnitude
`15,000 N/C` at radii `8 cm` and `17 cm`.  Both arrows point radially outward;
the auxiliary caption's claim that the exterior arrow points inward is not
consistent with the image.

Physical lengths, signed charges, field magnitudes, and vacuum permittivity
are unit-independent Physlib `Dimensionful` quantities.  Real numbers occur
only as coherent-SI readouts or as numbers printed in the figure and answer
choices.  The full electric field retains Physlib's spacetime-dependent
vector-field type.

Assumption/target split:

* governing laws: electrostatic fields vanish in conducting material, charge
  on the hollow conductor decomposes into its two surface charges, and
  spherical Gauss-law balances hold at the cavity, in the shell material, and
  outside the shell;
* previous-part results: none;
* figure/data readouts: conducting and concentric sphere labels; radii
  `5 cm`, `10 cm`, and `15 cm`; sampling radii `8 cm` and `17 cm`; and two
  radially outward field arrows labelled `15,000 N/C`;
* current target conclusions: the SI readout of the hollow sphere's inner-
  surface charge is the negative Gauss-law charge determined by the pictured
  `8 cm`, `15,000 N/C` cavity sample; consequently it is strictly negative
  and differs from the recorded answer D, namely `0 C`.

The usual Gauss-law interpretation of the nonzero cavity field makes the
central charge positive and the induced inner-surface charge its negative.
Thus the recorded answer is physically inconsistent with the primary figure.
The declarations retain it only as source metadata and state the physically
supported result, as required by the autoformalization retry protocol.
-/

/-! ## Dimensionful electrostatic quantities and SI readouts -/

/-- The physical dimension `M L T^-2 C^-1` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `C^2 T^2 M^-1 L^-3` of permittivity. -/
def electricPermittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative, unit-independent vacuum permittivity. -/
abbrev ElectricPermittivityQuantity : Type :=
  Dimensionful (WithDim electricPermittivityDimension NNReal)

/-- Coherent-SI readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by all five distance labels in the raster. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI readout of a signed electric charge, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Coherent-SI readout of field magnitude, in newtons per coulomb. -/
def fieldMagnitudeInNewtonsPerCoulomb
    (magnitude : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of electric permittivity. -/
def electricPermittivityInSI
    (permittivity : ElectricPermittivityQuantity) : ℝ :=
  ((permittivity UnitChoices.SI).val : ℝ)

/-! ## Geometric and figure labels -/

/-- The three spherical boundaries explicitly labelled in the image. -/
inductive SphereBoundary where
  | centralSphere
  | hollowInnerSurface
  | hollowOuterSurface
  deriving DecidableEq, Fintype, Repr

/-- The two black-dot locations at which electric-field arrows are drawn. -/
inductive RadialFieldSample where
  | inCavity
  | outsideShell
  deriving DecidableEq, Fintype, Repr

/-- Orientation of a field arrow relative to the radius through its point. -/
inductive RadialArrowOrientation where
  | outward
  | inward
  deriving DecidableEq, Repr

/-!
Typed content of the supplied raster.  Distance and field labels are physical
quantities; their printed numerical readouts are stated separately below.
-/
structure ConcentricConductingSpheresFigure where
  sphereBoundaryShown : SphereBoundary → Bool
  boundaryRadiusLabel : SphereBoundary → LengthQuantity
  fieldSampleShown : RadialFieldSample → Bool
  fieldSampleRadiusLabel : RadialFieldSample → LengthQuantity
  fieldMagnitudeLabel : RadialFieldSample → ElectricFieldMagnitudeQuantity
  fieldArrowOrientation : RadialFieldSample → RadialArrowOrientation
  showsConductingSpheresAnnotation : Bool
  conductingAnnotationTargets : SphereBoundary → Bool

/-!
Independent physical objects in the concentric-sphere experiment.  In
particular, `hollowInnerSurfaceCharge` is an unconstrained physical field: it
is not defined from answer D or from zero.
-/
structure ConcentricConductingSpheresSetup where
  centralSphereRadius : LengthQuantity
  hollowSphereInnerRadius : LengthQuantity
  hollowSphereOuterRadius : LengthQuantity
  cavitySampleRadius : LengthQuantity
  exteriorSampleRadius : LengthQuantity
  centralSphereCharge : SignedChargeQuantity
  hollowInnerSurfaceCharge : SignedChargeQuantity
  hollowOuterSurfaceCharge : SignedChargeQuantity
  hollowSphereTotalCharge : SignedChargeQuantity
  vacuumPermittivity : ElectricPermittivityQuantity
  electricField : Electromagnetism.ElectricField 3
  samplePoint : RadialFieldSample → Space 3
  outwardRadialUnit : RadialFieldSample → EuclideanSpace ℝ (Fin 3)
  sampledFieldMagnitude : RadialFieldSample → ElectricFieldMagnitudeQuantity
  centralConductingRegion : Set (Space 3)
  shellConductingRegion : Set (Space 3)
  figure : ConcentricConductingSpheresFigure

/-- The physical radius associated with either field-sampling point. -/
def sampleRadius
    (setup : ConcentricConductingSpheresSetup) : RadialFieldSample → LengthQuantity
  | .inCavity => setup.cavitySampleRadius
  | .outsideShell => setup.exteriorSampleRadius

/-!
For a radial field of magnitude `E` on a sphere of radius `r`, the outward
electric flux is `4 π r² E`.  This helper is only the flux expression; Gauss's
law is imposed independently in `SatisfiesSphericalGaussLaw`.
-/
def sphericalFluxInNewtonSquareMetersPerCoulomb
    (setup : ConcentricConductingSpheresSetup)
    (sample : RadialFieldSample) : ℝ :=
  4 * Real.pi * lengthInMeters (sampleRadius setup sample) ^ 2 *
    fieldMagnitudeInNewtonsPerCoulomb (setup.sampledFieldMagnitude sample)

/-! ## Scenario, primary-image evidence, geometry, and governing laws -/

/-- The qualitative material and nesting claims made by the problem prose. -/
structure MatchesConcentricConductingSphereScenario
    (setup : ConcentricConductingSpheresSetup) : Prop where
  centralSphereIsConducting :
    setup.figure.conductingAnnotationTargets .centralSphere = true
  hollowShellIsConductingAtInnerBoundary :
    setup.figure.conductingAnnotationTargets .hollowInnerSurface = true
  hollowShellIsConductingAtOuterBoundary :
    setup.figure.conductingAnnotationTargets .hollowOuterSurface = true
  conductingAnnotationShown :
    setup.figure.showsConductingSpheresAnnotation = true

/-!
Primary-raster evidence, including both radially outward arrows.  Each printed
label is first identified with an independent physical quantity and is only
then assigned its centimetre or `N/C` readout.
-/
structure MatchesPrimaryConcentricSpheresFigure
    (setup : ConcentricConductingSpheresSetup) : Prop where
  centralBoundaryShown :
    setup.figure.sphereBoundaryShown .centralSphere = true
  innerShellBoundaryShown :
    setup.figure.sphereBoundaryShown .hollowInnerSurface = true
  outerShellBoundaryShown :
    setup.figure.sphereBoundaryShown .hollowOuterSurface = true
  cavitySampleShown : setup.figure.fieldSampleShown .inCavity = true
  exteriorSampleShown : setup.figure.fieldSampleShown .outsideShell = true
  centralRadiusLabelIsPhysical :
    setup.figure.boundaryRadiusLabel .centralSphere = setup.centralSphereRadius
  innerShellRadiusLabelIsPhysical :
    setup.figure.boundaryRadiusLabel .hollowInnerSurface =
      setup.hollowSphereInnerRadius
  outerShellRadiusLabelIsPhysical :
    setup.figure.boundaryRadiusLabel .hollowOuterSurface =
      setup.hollowSphereOuterRadius
  cavitySampleRadiusLabelIsPhysical :
    setup.figure.fieldSampleRadiusLabel .inCavity = setup.cavitySampleRadius
  exteriorSampleRadiusLabelIsPhysical :
    setup.figure.fieldSampleRadiusLabel .outsideShell = setup.exteriorSampleRadius
  cavityFieldLabelIsPhysical :
    setup.figure.fieldMagnitudeLabel .inCavity =
      setup.sampledFieldMagnitude .inCavity
  exteriorFieldLabelIsPhysical :
    setup.figure.fieldMagnitudeLabel .outsideShell =
      setup.sampledFieldMagnitude .outsideShell
  centralRadiusIsFiveCentimeters :
    lengthInCentimeters setup.centralSphereRadius = 5
  innerShellRadiusIsTenCentimeters :
    lengthInCentimeters setup.hollowSphereInnerRadius = 10
  outerShellRadiusIsFifteenCentimeters :
    lengthInCentimeters setup.hollowSphereOuterRadius = 15
  cavitySampleRadiusIsEightCentimeters :
    lengthInCentimeters setup.cavitySampleRadius = 8
  exteriorSampleRadiusIsSeventeenCentimeters :
    lengthInCentimeters setup.exteriorSampleRadius = 17
  cavityFieldLabelIsFifteenThousand :
    fieldMagnitudeInNewtonsPerCoulomb
      (setup.sampledFieldMagnitude .inCavity) = 15000
  exteriorFieldLabelIsFifteenThousand :
    fieldMagnitudeInNewtonsPerCoulomb
      (setup.sampledFieldMagnitude .outsideShell) = 15000
  cavityArrowPointsRadiallyOutward :
    setup.figure.fieldArrowOrientation .inCavity = .outward
  exteriorArrowPointsRadiallyOutward :
    setup.figure.fieldArrowOrientation .outsideShell = .outward

/-!
The concentric radial geometry encoded by the five labelled radii.  The
conducting regions are described by distance from the common center, chosen
as the origin of `Space 3`.
-/
structure SatisfiesConcentricSphericalGeometry
    (setup : ConcentricConductingSpheresSetup) : Prop where
  radiiStrictlyNested :
    0 < lengthInMeters setup.centralSphereRadius ∧
      lengthInMeters setup.centralSphereRadius <
        lengthInMeters setup.cavitySampleRadius ∧
      lengthInMeters setup.cavitySampleRadius <
        lengthInMeters setup.hollowSphereInnerRadius ∧
      lengthInMeters setup.hollowSphereInnerRadius <
        lengthInMeters setup.hollowSphereOuterRadius ∧
      lengthInMeters setup.hollowSphereOuterRadius <
        lengthInMeters setup.exteriorSampleRadius
  samplePointHasLabelledRadius : ∀ sample,
    ‖setup.samplePoint sample‖ = lengthInMeters (sampleRadius setup sample)
  outwardRadialDirectionsAreUnit : ∀ sample,
    ‖setup.outwardRadialUnit sample‖ = 1
  centralRegionIsBall : ∀ point,
    point ∈ setup.centralConductingRegion ↔
      ‖point‖ ≤ lengthInMeters setup.centralSphereRadius
  shellRegionIsAnnulus : ∀ point,
    point ∈ setup.shellConductingRegion ↔
      lengthInMeters setup.hollowSphereInnerRadius ≤ ‖point‖ ∧
        ‖point‖ ≤ lengthInMeters setup.hollowSphereOuterRadius

/-!
The dimensionful field magnitudes calibrate the Physlib vector field at the
two black-dot samples.  The positive scalar multiple records radial outward
orientation independently of the pictorial arrow fields.
-/
structure FieldSamplesCalibrateElectricField
    (setup : ConcentricConductingSpheresSetup) : Prop where
  sampledFieldIsRadiallyOutward : ∀ time sample,
    setup.electricField time (setup.samplePoint sample) =
      fieldMagnitudeInNewtonsPerCoulomb
          (setup.sampledFieldMagnitude sample) •
        setup.outwardRadialUnit sample

/-!
Electrostatic equilibrium of both conductors.  The total charge of the hollow
sphere is decomposed into independent inner- and outer-surface charges; no
surface charge is assigned the requested numerical answer here.
-/
structure SatisfiesElectrostaticConductorEquilibrium
    (setup : ConcentricConductingSpheresSetup) : Prop where
  fieldVanishesInCentralConductor : ∀ time point,
    point ∈ setup.centralConductingRegion →
      setup.electricField time point = 0
  fieldVanishesInShellMaterial : ∀ time point,
    point ∈ setup.shellConductingRegion →
      setup.electricField time point = 0
  hollowChargeIsSurfaceChargeSum :
    chargeInCoulombs setup.hollowSphereTotalCharge =
      chargeInCoulombs setup.hollowInnerSurfaceCharge +
        chargeInCoulombs setup.hollowOuterSurfaceCharge

/-!
Spherical Gauss-law balances in coherent SI units.  The middle equation is
the zero-flux Gaussian surface lying in the metal of the shell.  It states
the standard induced-charge cancellation law, not the requested `0 C`
answer.  The exterior balance retains all three surface contributions.
-/
structure SatisfiesSphericalGaussLaw
    (setup : ConcentricConductingSpheresSetup) : Prop where
  cavityGaussianSphere :
    electricPermittivityInSI setup.vacuumPermittivity *
        sphericalFluxInNewtonSquareMetersPerCoulomb setup .inCavity =
      chargeInCoulombs setup.centralSphereCharge
  gaussianSphereInsideShellMetal :
    chargeInCoulombs setup.centralSphereCharge +
        chargeInCoulombs setup.hollowInnerSurfaceCharge = 0
  exteriorGaussianSphere :
    electricPermittivityInSI setup.vacuumPermittivity *
        sphericalFluxInNewtonSquareMetersPerCoulomb setup .outsideShell =
      chargeInCoulombs setup.centralSphereCharge +
        chargeInCoulombs setup.hollowInnerSurfaceCharge +
          chargeInCoulombs setup.hollowOuterSurfaceCharge

/-- Positivity of the vacuum permittivity used by the Gauss-law balances. -/
structure HasPhysicalElectrostaticParameters
    (setup : ConcentricConductingSpheresSetup) : Prop where
  vacuumPermittivityPositive :
    0 < electricPermittivityInSI setup.vacuumPermittivity

/-! ## Displayed answer choices and formalized conclusions -/

/-- Labels of the four charge choices printed in the source record. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Coulomb number printed beside each answer choice. -/
def answerChargeInCoulombs : AnswerChoice → ℝ
  | .A => 80
  | .B => 10
  | .C => 20
  | .D => 0

/-- The answer label recorded by the dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The conductor/Gauss-law model forces the inner-surface charge to cancel the
central sphere's charge.  This physically grounded intermediate conclusion
contains no occurrence of the recorded answer.
-/
lemma hollow_inner_surface_charge_cancels_central
    (setup : ConcentricConductingSpheresSetup)
    (hGauss : SatisfiesSphericalGaussLaw setup) :
    chargeInCoulombs setup.hollowInnerSurfaceCharge =
      -chargeInCoulombs setup.centralSphereCharge := by
  linarith [hGauss.gaussianSphereInsideShellMetal]

/-!
The nonzero outward cavity field, positive radius, and positive permittivity
make the central sphere's charge positive.  Together with the preceding
lemma, this exposes the conflict between the primary figure and answer D.
-/
lemma central_sphere_charge_is_positive
    (setup : ConcentricConductingSpheresSetup)
    (hFigure : MatchesPrimaryConcentricSpheresFigure setup)
    (hGeometry : SatisfiesConcentricSphericalGeometry setup)
    (hPhysical : HasPhysicalElectrostaticParameters setup)
    (hGauss : SatisfiesSphericalGaussLaw setup) :
    0 < chargeInCoulombs setup.centralSphereCharge := by
  have hRadius :
      lengthInMeters setup.cavitySampleRadius = (8 / 100 : ℝ) := by
    have hRadiusInCentimeters :=
      hFigure.cavitySampleRadiusIsEightCentimeters
    change 100 * lengthInMeters setup.cavitySampleRadius = 8 at hRadiusInCentimeters
    linarith
  have hFluxPositive :
      0 < sphericalFluxInNewtonSquareMetersPerCoulomb setup .inCavity := by
    simp only [sphericalFluxInNewtonSquareMetersPerCoulomb, sampleRadius]
    rw [hRadius, hFigure.cavityFieldLabelIsFifteenThousand]
    positivity
  rw [← hGauss.cavityGaussianSphere]
  exact mul_pos hPhysical.vacuumPermittivityPositive hFluxPositive

/-!
The physically supported total charge on the inside surface is obtained by
combining two independent Gauss-law balances: the `8 cm`, `15,000 N/C`
cavity sample determines the positive central charge, and a Gaussian sphere
inside the shell material forces the induced inner-surface charge to cancel
it.  Hence the inner charge is

`-ε₀ · 4π · (8/100 m)² · (15000 N/C)`,

which is strictly negative and therefore is not recorded answer D (`0 C`).

This declaration formalizes `thm:physics:phyx_mini_0852:target`.  Neither the
exact charge expression, its negative sign, nor its disagreement with D
occurs in a premise.
-/
theorem problem_phyx_mini_0852
    (setup : ConcentricConductingSpheresSetup)
    (hScenario : MatchesConcentricConductingSphereScenario setup)
    (hFigure : MatchesPrimaryConcentricSpheresFigure setup)
    (hGeometry : SatisfiesConcentricSphericalGeometry setup)
    (hCalibration : FieldSamplesCalibrateElectricField setup)
    (hEquilibrium : SatisfiesElectrostaticConductorEquilibrium setup)
    (hPhysical : HasPhysicalElectrostaticParameters setup)
    (hGauss : SatisfiesSphericalGaussLaw setup) :
    chargeInCoulombs setup.hollowInnerSurfaceCharge =
        -(electricPermittivityInSI setup.vacuumPermittivity *
          (4 * Real.pi * (8 / 100 : ℝ) ^ 2 * 15000)) ∧
      chargeInCoulombs setup.hollowInnerSurfaceCharge < 0 ∧
      chargeInCoulombs setup.hollowInnerSurfaceCharge ≠
        answerChargeInCoulombs recordedDatasetAnswer := by
  have hRadius :
      lengthInMeters setup.cavitySampleRadius = (8 / 100 : ℝ) := by
    have hRadiusInCentimeters :=
      hFigure.cavitySampleRadiusIsEightCentimeters
    change 100 * lengthInMeters setup.cavitySampleRadius = 8 at hRadiusInCentimeters
    linarith
  have hCentral :
      chargeInCoulombs setup.centralSphereCharge =
        electricPermittivityInSI setup.vacuumPermittivity *
          (4 * Real.pi * (8 / 100 : ℝ) ^ 2 * 15000) := by
    rw [← hGauss.cavityGaussianSphere]
    simp only [sphericalFluxInNewtonSquareMetersPerCoulomb, sampleRadius]
    rw [hRadius, hFigure.cavityFieldLabelIsFifteenThousand]
  have hInner :=
    hollow_inner_surface_charge_cancels_central setup hGauss
  rw [hCentral] at hInner
  have hInnerNegative :
      chargeInCoulombs setup.hollowInnerSurfaceCharge < 0 := by
    have hCentralPositive :=
      central_sphere_charge_is_positive setup hFigure hGeometry hPhysical hGauss
    linarith
  refine ⟨hInner, hInnerNegative, ?_⟩
  simpa [recordedDatasetAnswer, answerChargeInCoulombs] using
    ne_of_lt hInnerNegative

end PhyXMiniProblems.ProblemPhyXMini0852

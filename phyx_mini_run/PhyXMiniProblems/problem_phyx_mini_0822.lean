import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.ClassicalMechanics.RigidBody.Basic
import Physlib.Units.WithDim.Basic

/-!
# Axial moment of inertia of a uniform hollow cylinder

The cylinder has uniform volume mass density `ρ`, axial length `L`, inner
radius `R₁`, and outer radius `R₂`.  The supplied figure also identifies the
central symmetry axis and a representative coaxial shell of radius `r` and
thickness `dr`.

Physical mass, length, density, and moment of inertia are represented by
Physlib dimensionful quantities.  The radial coordinate and integrands below
are coherent-SI scalar readouts used to express the shell integration law.
The requested factor `1/2` occurs only in the conclusion and in the printed
answer-choice metadata, never in a governing-law premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0822

open Dimension

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for `L`, `R₁`, and `R₂`. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative volume mass density, with dimension mass per length cubed. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A scalar moment of inertia, with dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical mass in coherent SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in coherent SI meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a volume mass density in coherent SI kilograms per cubic meter. -/
def massDensityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in coherent SI kilogram meters squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-! ## Primary-figure vocabulary -/

/-- Physical features visibly distinguished in the supplied diagram. -/
inductive FigureFeature where
  | annularCylinder
  | centralBore
  | representativeRadialShell
  deriving DecidableEq, Repr

/-- Text and mathematical labels printed in the supplied diagram. -/
inductive FigureLabel where
  | axis
  | lengthL
  | innerRadiusR1
  | outerRadiusR2
  | shellRadiusR
  | shellThicknessDr
  deriving DecidableEq, Repr

/-- The two geometrically relevant directions in the cylinder. -/
inductive CylinderDirection where
  | axial
  | radial
  deriving DecidableEq, Repr

/-- Direct qualitative and label data transcribed from the primary image. -/
structure HollowCylinderFigure where
  showsFeature : FigureFeature → Bool
  showsLabel : FigureLabel → Bool
  axisIsCentralSymmetryAxis : Bool
  lengthDirection : CylinderDirection
  innerRadiusDirection : CylinderDirection
  outerRadiusDirection : CylinderDirection
  shellRadiusDirection : CylinderDirection
  shellThicknessDirection : CylinderDirection
  innerRadiusEndsAtBore : Bool
  outerRadiusEndsAtOuterSurface : Bool

/-! ## Independent physical setup and supplied data -/

/-- Mass-distribution models distinguished by the problem statement. -/
inductive CylinderDensityModel where
  | uniformVolumeDensity
  | nonuniformVolumeDensity
  deriving DecidableEq, Repr

/-- Geometric models for the material region of the cylinder. -/
inductive CylinderGeometry where
  | rightCircularAnnulus
  | other
  deriving DecidableEq, Repr

/-!
All dimensionful quantities are independent fields.  In particular,
`axialMomentOfInertia` is not defined from the answer formula.  The scalar
function is the SI readout of the mass in a coaxial shell per unit increment
of its meter-valued radial coordinate.
-/
structure UniformHollowCylinderSetup where
  figure : HollowCylinderFigure
  materialMassDensity : MassDensityQuantity
  axialLength : LengthQuantity
  innerRadius : LengthQuantity
  outerRadius : LengthQuantity
  totalMass : MassQuantity
  axialMomentOfInertia : MomentOfInertiaQuantity
  rigidBodySI : RigidBody 3
  symmetryAxis : Fin 3
  radialShellMassPerUnitRadiusInKilogramsPerMeter : ℝ → ℝ
  densityModel : CylinderDensityModel
  geometry : CylinderGeometry

/-!
Problem-text and primary-image facts.  No field gives the cylinder's moment
of inertia or selects an answer choice.
-/
structure MatchesProblemAndFigure
    (setup : UniformHollowCylinderSetup) : Prop where
  densityIsUniform :
    setup.densityModel = .uniformVolumeDensity
  materialRegionIsAnnularCylinder :
    setup.geometry = .rightCircularAnnulus
  allFeaturesAreShown :
    ∀ feature : FigureFeature, setup.figure.showsFeature feature = true
  allLabelsAreShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  markedAxisIsCentralSymmetryAxis :
    setup.figure.axisIsCentralSymmetryAxis = true
  lengthLabelIsAxial :
    setup.figure.lengthDirection = .axial
  innerRadiusLabelIsRadial :
    setup.figure.innerRadiusDirection = .radial
  outerRadiusLabelIsRadial :
    setup.figure.outerRadiusDirection = .radial
  shellRadiusLabelIsRadial :
    setup.figure.shellRadiusDirection = .radial
  shellThicknessLabelIsRadial :
    setup.figure.shellThicknessDirection = .radial
  innerRadiusTerminatesAtCentralBore :
    setup.figure.innerRadiusEndsAtBore = true
  outerRadiusTerminatesAtOuterSurface :
    setup.figure.outerRadiusEndsAtOuterSurface = true

/-- Positivity and nondegeneracy of the independent cylinder parameters. -/
structure HasPhysicalCylinderParameters
    (setup : UniformHollowCylinderSetup) : Prop where
  densityPositive :
    0 < massDensityInKilogramsPerCubicMeter setup.materialMassDensity
  axialLengthPositive :
    0 < lengthInMeters setup.axialLength
  innerRadiusPositive :
    0 < lengthInMeters setup.innerRadius
  innerRadiusLessThanOuterRadius :
    lengthInMeters setup.innerRadius < lengthInMeters setup.outerRadius
  totalMassPositive :
    0 < massInKilograms setup.totalMass
  shellMassProfileNonnegative :
    ∀ r ∈ Set.Icc (lengthInMeters setup.innerRadius)
        (lengthInMeters setup.outerRadius),
      0 ≤ setup.radialShellMassPerUnitRadiusInKilogramsPerMeter r

/-!
General shell-integration laws for a uniform annular cylinder.

At a radius `r`, the differential shell volume per radial increment is
`2 π r L`, so its mass per radial increment is `ρ (2 π r L)`.  Total mass
is the radial integral of this shell profile, and axial moment of inertia is
its radial second moment.  The two bridge equalities connect these physical
quantities to Physlib's `RigidBody.mass` and diagonal `inertiaTensor` entry.

These premises are valid for arbitrary radii and contain neither the final
closed form nor its factor `1/2`.
-/
structure SatisfiesUniformAnnularCylinderLaws
    (setup : UniformHollowCylinderSetup) : Prop where
  rigidBodyMassMatchesTotalMass :
    setup.rigidBodySI.mass = massInKilograms setup.totalMass
  axialInertiaIsSymmetryAxisTensorEntry :
    setup.rigidBodySI.inertiaTensor setup.symmetryAxis setup.symmetryAxis =
      momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia
  uniformCoaxialShellMassLaw :
    ∀ r ∈ Set.Icc (lengthInMeters setup.innerRadius)
        (lengthInMeters setup.outerRadius),
      setup.radialShellMassPerUnitRadiusInKilogramsPerMeter r =
        massDensityInKilogramsPerCubicMeter setup.materialMassDensity *
          (2 * Real.pi * r * lengthInMeters setup.axialLength)
  totalMassIsIntegralOfCoaxialShells :
    massInKilograms setup.totalMass =
      ∫ r in (lengthInMeters setup.innerRadius)..
          (lengthInMeters setup.outerRadius),
        setup.radialShellMassPerUnitRadiusInKilogramsPerMeter r
  axialInertiaIsRadialSecondMoment :
    momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
      ∫ r in (lengthInMeters setup.innerRadius)..
          (lengthInMeters setup.outerRadius),
        r ^ 2 * setup.radialShellMassPerUnitRadiusInKilogramsPerMeter r

/-! ## Printed answer choices and target -/

/-- Labels of the four alternatives printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The coefficient multiplying `M (R₁² + R₂²)` in each printed choice. -/
def AnswerChoice.coefficient : AnswerChoice → ℝ
  | .A => 1 / 3
  | .B => 1 / 2
  | .C => 1 / 4
  | .D => 1 / 5

/-- A displayed choice agrees with the cylinder's independent inertia field. -/
def MatchesAnswerChoice
    (setup : UniformHollowCylinderSetup) (choice : AnswerChoice) : Prop :=
  momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
    choice.coefficient * massInKilograms setup.totalMass *
      (lengthInMeters setup.innerRadius ^ 2 +
        lengthInMeters setup.outerRadius ^ 2)

/-!
The moment of inertia of the uniform hollow cylinder about its central
symmetry axis is `I = (1/2) M (R₁² + R₂²)`, hence printed choice B.

This formalizes `thm:physics:phyx_mini_0822:target`.
-/
theorem problem_phyx_mini_0822
    (setup : UniformHollowCylinderSetup)
    (_problemAndFigure : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalCylinderParameters setup)
    (_shellLaws : SatisfiesUniformAnnularCylinderLaws setup) :
    momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
        (1 / 2 : ℝ) * massInKilograms setup.totalMass *
          (lengthInMeters setup.innerRadius ^ 2 +
            lengthInMeters setup.outerRadius ^ 2) ∧
      MatchesAnswerChoice setup .B := by
  let a : ℝ := lengthInMeters setup.innerRadius
  let b : ℝ := lengthInMeters setup.outerRadius
  let K : ℝ :=
    massDensityInKilogramsPerCubicMeter setup.materialMassDensity *
      (2 * Real.pi * lengthInMeters setup.axialLength)
  have hab : a ≤ b := by
    exact le_of_lt _physical.innerRadiusLessThanOuterRadius
  have hIntegralOne :
      (∫ r in a..b, r) = (b ^ 2 - a ^ 2) / 2 := by
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      intro x _hx
      simpa [id_eq] using ((hasDerivAt_id x).pow 2).div_const 2
    have hint :
        IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume a b :=
      continuous_id.intervalIntegrable a b
    simpa only [sub_div] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hIntegralThree :
      (∫ r in a..b, r ^ 3) = (b ^ 4 - a ^ 4) / 4 := by
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ => y ^ 4 / 4) (x ^ 3) x := by
      intro x _hx
      simpa [id_eq] using ((hasDerivAt_id x).pow 4).div_const 4
    have hint :
        IntervalIntegrable (fun x : ℝ => x ^ 3) MeasureTheory.volume a b :=
      (continuous_pow 3).intervalIntegrable a b
    simpa only [sub_div] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hMass :
      massInKilograms setup.totalMass =
        K * ((b ^ 2 - a ^ 2) / 2) := by
    calc
      massInKilograms setup.totalMass =
          ∫ r in a..b,
            setup.radialShellMassPerUnitRadiusInKilogramsPerMeter r := by
        simpa only [a, b] using
          _shellLaws.totalMassIsIntegralOfCoaxialShells
      _ = ∫ r in a..b, K * r := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : r ∈ Set.Icc a b := by
          simpa only [Set.uIcc_of_le hab] using hr
        have hrPhysical :
            r ∈ Set.Icc (lengthInMeters setup.innerRadius)
              (lengthInMeters setup.outerRadius) := by
          simpa only [a, b] using hr'
        change
          setup.radialShellMassPerUnitRadiusInKilogramsPerMeter r =
            K * r
        rw [_shellLaws.uniformCoaxialShellMassLaw r hrPhysical]
        dsimp only [K]
        ring
      _ = K * ∫ r in a..b, r := by
        rw [intervalIntegral.integral_const_mul]
      _ = K * ((b ^ 2 - a ^ 2) / 2) := by
        rw [hIntegralOne]
  have hInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.axialMomentOfInertia =
        K * ((b ^ 4 - a ^ 4) / 4) := by
    calc
      momentOfInertiaInKilogramMetersSquared
          setup.axialMomentOfInertia =
          ∫ r in a..b,
            r ^ 2 *
              setup.radialShellMassPerUnitRadiusInKilogramsPerMeter r := by
        simpa only [a, b] using
          _shellLaws.axialInertiaIsRadialSecondMoment
      _ = ∫ r in a..b, K * r ^ 3 := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : r ∈ Set.Icc a b := by
          simpa only [Set.uIcc_of_le hab] using hr
        have hrPhysical :
            r ∈ Set.Icc (lengthInMeters setup.innerRadius)
              (lengthInMeters setup.outerRadius) := by
          simpa only [a, b] using hr'
        change
          r ^ 2 *
              setup.radialShellMassPerUnitRadiusInKilogramsPerMeter r =
            K * r ^ 3
        rw [_shellLaws.uniformCoaxialShellMassLaw r hrPhysical]
        dsimp only [K]
        ring
      _ = K * ∫ r in a..b, r ^ 3 := by
        rw [intervalIntegral.integral_const_mul]
      _ = K * ((b ^ 4 - a ^ 4) / 4) := by
        rw [hIntegralThree]
  have hClosedForm :
      momentOfInertiaInKilogramMetersSquared
          setup.axialMomentOfInertia =
        (1 / 2 : ℝ) * massInKilograms setup.totalMass *
          (a ^ 2 + b ^ 2) := by
    rw [hInertia, hMass]
    ring
  constructor
  · simpa only [a, b] using hClosedForm
  · simpa [MatchesAnswerChoice, AnswerChoice.coefficient, a, b] using
      hClosedForm

end PhyXMiniProblems.ProblemPhyXMini0822

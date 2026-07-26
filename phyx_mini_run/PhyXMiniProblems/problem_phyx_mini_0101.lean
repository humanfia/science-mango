import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Basic

/-!
# Apparent displacement of the Sun at the horizon

This file formalizes the concentric Earth--atmosphere ray diagram in
`phyx_mini_0101`.  The radii and atmospheric height are unit-aware physical
lengths.  Refractive indices and the scalar readouts of angles in radians are
dimensionless real numbers.

The source gives the atmospheric height and refractive index but only labels
the Earth radius as `R`.  The standard mean-Earth-radius calibration needed
for a numerical answer is therefore kept in a separate hypothesis interface.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0101

/-! ## Physical quantities and figure labels -/

/-- A signed physical length, represented independently of a choice of units. -/
abbrev DimLength : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- Read a physical length as a real scalar in the specified length unit. -/
def lengthValueIn (unit : LengthUnit) (length : DimLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The kilometre readout used for the labelled radii `R`, `h`, and `R + h`. -/
def lengthInKilometers (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.kilometers length

/-- Convert the radian scalar used by `Real.sin` to a degree readout. -/
def radiansToDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-- The homogeneous optical regions on the two sides of the atmosphere's top. -/
inductive OpticalRegion where
  | outerSpace
  | atmosphere
  deriving DecidableEq, Repr

/-- The two solar positions distinguished by the horizon-refraction diagram. -/
inductive SolarPosition where
  | truePosition
  | apparentPosition
  deriving DecidableEq, Repr

/--
Physical objects and scalar angle readouts in the primary figure.

Angles of incidence and refraction are measured from the inward radial normal
at the point where the solar ray enters the atmosphere.  The deviation angle
is the labelled `δ` between the incoming ray and the horizontal apparent ray.
-/
structure AtmosphericHorizonSetup where
  /-- Figure label `R`: physical mean radius of the Earth. -/
  earthRadius : DimLength
  /-- Figure label `h`: physical height of the idealized atmosphere. -/
  atmosphereHeight : DimLength
  /-- Figure label `R + h`: radius of the top of the atmosphere. -/
  atmosphereOuterRadius : DimLength
  /-- Dimensionless refractive index of each homogeneous optical region. -/
  refractiveIndex : OpticalRegion → ℝ
  /-- Incidence angle of the incoming sunlight at the top of the atmosphere. -/
  incidenceAngleRadians : ℝ
  /-- Refraction angle of the ray inside the atmosphere. -/
  refractionAngleRadians : ℝ
  /-- Figure label `δ`: angular displacement of the apparent solar position. -/
  deviationAngleRadians : ℝ
  /-- True or apparent altitude of the Sun relative to the local horizon. -/
  solarAltitudeRadians : SolarPosition → ℝ

/-! ## Problem data, geometric relations, and governing optics -/

/-- The numerical data explicitly stated in the problem. -/
structure MatchesStatedAtmosphereData
    (setup : AtmosphericHorizonSetup) : Prop where
  atmosphereHeightReadout :
    lengthInKilometers setup.atmosphereHeight = 20
  outerSpaceIndexReadout :
    setup.refractiveIndex .outerSpace = 1
  atmosphereIndexReadout :
    setup.refractiveIndex .atmosphere = (10003 / 10000 : ℝ)

/--
The numerical calibration for the figure label `R`.  It is separated from
`MatchesStatedAtmosphereData` because the source itself does not print a value
for `R`; `6371 km` is the standard mean-Earth-radius approximation used here.
-/
structure UsesMeanEarthRadiusCalibration
    (setup : AtmosphericHorizonSetup) : Prop where
  earthRadiusReadout :
    lengthInKilometers setup.earthRadius = 6371

/-- Positivity and principal-branch conditions of the geometrical-optics model. -/
structure HasPhysicalAtmosphericParameters
    (setup : AtmosphericHorizonSetup) : Prop where
  earthRadiusPositive :
    0 < lengthInKilometers setup.earthRadius
  atmosphereHeightPositive :
    0 < lengthInKilometers setup.atmosphereHeight
  atmosphereOuterRadiusPositive :
    0 < lengthInKilometers setup.atmosphereOuterRadius
  refractiveIndicesPositive :
    ∀ region, 0 < setup.refractiveIndex region
  atmosphereOpticallyDenser :
    setup.refractiveIndex .outerSpace < setup.refractiveIndex .atmosphere
  incidenceAngleOnPrincipalBranch :
    0 ≤ setup.incidenceAngleRadians ∧
      setup.incidenceAngleRadians < Real.pi / 2
  refractionAngleOnPrincipalBranch :
    0 ≤ setup.refractionAngleRadians ∧
      setup.refractionAngleRadians < Real.pi / 2
  deviationAngleNonnegative :
    0 ≤ setup.deviationAngleRadians

/--
Relations read from the concentric-circle figure.  The ray seen on the local
horizon is tangent to the Earth at the observer.  The resulting right triangle
has hypotenuse `R + h` and side opposite the refraction angle equal to `R`.
The remaining fields identify the labelled bending angle with the difference
between ray angles and with the separation of apparent and true solar altitude.
-/
structure SatisfiesConcentricHorizonGeometry
    (setup : AtmosphericHorizonSetup) : Prop where
  outerRadiusIsEarthRadiusPlusHeight :
    lengthInKilometers setup.atmosphereOuterRadius =
      lengthInKilometers setup.earthRadius +
        lengthInKilometers setup.atmosphereHeight
  tangentRayRightTriangle :
    Real.sin setup.refractionAngleRadians =
      lengthInKilometers setup.earthRadius /
        lengthInKilometers setup.atmosphereOuterRadius
  deviationIsRayBending :
    setup.deviationAngleRadians =
      setup.incidenceAngleRadians - setup.refractionAngleRadians
  apparentSunIsOnHorizon :
    setup.solarAltitudeRadians .apparentPosition = 0
  deviationSeparatesApparentAndTruePositions :
    setup.deviationAngleRadians =
      setup.solarAltitudeRadians .apparentPosition -
        setup.solarAltitudeRadians .truePosition

/--
Snell's law at the outer-space--atmosphere boundary,
`n_space sin i = n_atmosphere sin r`.
-/
def SatisfiesSnellsLawAtAtmosphere
    (setup : AtmosphericHorizonSetup) : Prop :=
  setup.refractiveIndex .outerSpace *
      Real.sin setup.incidenceAngleRadians =
    setup.refractiveIndex .atmosphere *
      Real.sin setup.refractionAngleRadians

/-! ## Symbolic and multiple-choice conclusions -/

/--
The inverse-sine expression obtained from tangent-ray geometry and Snell's law.
This is a derived conclusion, not a premise of the physical model.
-/
def predictedDeviationRadians (setup : AtmosphericHorizonSetup) : ℝ :=
  Real.arcsin
      (setup.refractiveIndex .atmosphere /
          setup.refractiveIndex .outerSpace *
        (lengthInKilometers setup.earthRadius /
          lengthInKilometers setup.atmosphereOuterRadius)) -
    Real.arcsin
      (lengthInKilometers setup.earthRadius /
        lengthInKilometers setup.atmosphereOuterRadius)

/-- The four displayed multiple-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The angular displacement in degrees printed beside each answer choice. -/
def AnswerChoice.angleDegrees : AnswerChoice → ℝ
  | .A => 23 / 100
  | .B => 30 / 100
  | .C => 20 / 100
  | .D => 25 / 100

/-- Dataset metadata: the recorded answer label, never used as a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- The predicted angle is within one hundredth of a degree of a displayed choice. -/
def MatchesWithinHundredthDegree
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |radiansToDegrees angleRadians - choice.angleDegrees| < 1 / 100

/-- A choice is at least as close to the predicted degree readout as every option. -/
def IsClosestAnswerChoice
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |radiansToDegrees angleRadians - choice.angleDegrees| ≤
      |radiansToDegrees angleRadians - other.angleDegrees|

/--
Tangent-ray geometry, Snell's law, and the principal angle branches give the
inverse-sine expression for the deviation angle.
-/
lemma deviation_eq_predictedDeviationRadians
    (setup : AtmosphericHorizonSetup)
    (hPhysical : HasPhysicalAtmosphericParameters setup)
    (hGeometry : SatisfiesConcentricHorizonGeometry setup)
    (hSnell : SatisfiesSnellsLawAtAtmosphere setup) :
    setup.deviationAngleRadians = predictedDeviationRadians setup := by
  have hOuterIndexNe :
      setup.refractiveIndex .outerSpace ≠ 0 :=
    ne_of_gt (hPhysical.refractiveIndicesPositive .outerSpace)
  have hSnell' :
      Real.sin setup.incidenceAngleRadians =
        setup.refractiveIndex .atmosphere /
            setup.refractiveIndex .outerSpace *
          Real.sin setup.refractionAngleRadians := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hOuterIndexNe).2
    simpa [SatisfiesSnellsLawAtAtmosphere, mul_comm] using hSnell
  rw [hGeometry.tangentRayRightTriangle] at hSnell'
  rw [hGeometry.deviationIsRayBending, predictedDeviationRadians,
    ← hSnell', ← hGeometry.tangentRayRightTriangle]
  congr 1
  · exact (Real.arcsin_sin
      (by
        linarith [hPhysical.incidenceAngleOnPrincipalBranch.1,
          Real.pi_pos])
      hPhysical.incidenceAngleOnPrincipalBranch.2.le).symm
  · exact (Real.arcsin_sin
      (by
        linarith [hPhysical.refractionAngleOnPrincipalBranch.1,
          Real.pi_pos])
      hPhysical.refractionAngleOnPrincipalBranch.2.le).symm

/--
With `n = 1.0003`, `h = 20 km`, and the standard `R = 6371 km` calibration,
the atmospheric displacement is given by the derived inverse-sine formula,
lies within `0.01°` of `0.23°`, and is closest to answer A.

Blueprint: `thm:physics:phyx_mini_0101:target`.
-/
theorem atmosphericRefractionMakesAnswerAClosest
    (setup : AtmosphericHorizonSetup)
    (hData : MatchesStatedAtmosphereData setup)
    (hEarthRadius : UsesMeanEarthRadiusCalibration setup)
    (hPhysical : HasPhysicalAtmosphericParameters setup)
    (hGeometry : SatisfiesConcentricHorizonGeometry setup)
    (hSnell : SatisfiesSnellsLawAtAtmosphere setup) :
    setup.deviationAngleRadians = predictedDeviationRadians setup ∧
      MatchesWithinHundredthDegree setup.deviationAngleRadians .A ∧
      IsClosestAnswerChoice setup.deviationAngleRadians .A := by
  have hDeviation :=
    deviation_eq_predictedDeviationRadians setup hPhysical hGeometry hSnell
  have hOuterRadius :
      lengthInKilometers setup.atmosphereOuterRadius = 6391 := by
    rw [hGeometry.outerRadiusIsEarthRadiusPlusHeight,
      hEarthRadius.earthRadiusReadout, hData.atmosphereHeightReadout]
    norm_num
  have hSinRefraction :
      Real.sin setup.refractionAngleRadians = (6371 / 6391 : ℝ) := by
    rw [hGeometry.tangentRayRightTriangle,
      hEarthRadius.earthRadiusReadout, hOuterRadius]
  have hSinIncidence :
      Real.sin setup.incidenceAngleRadians =
        (10003 / 10000 : ℝ) * (6371 / 6391 : ℝ) := by
    have hSnell' := hSnell
    rw [SatisfiesSnellsLawAtAtmosphere,
      hData.outerSpaceIndexReadout, hData.atmosphereIndexReadout,
      hSinRefraction] at hSnell'
    norm_num at hSnell' ⊢
    exact hSnell'
  have hCosRefractionPositive :
      0 < Real.cos setup.refractionAngleRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨by
        linarith [hPhysical.refractionAngleOnPrincipalBranch.1,
          Real.pi_pos],
        hPhysical.refractionAngleOnPrincipalBranch.2⟩
  have hCosIncidencePositive :
      0 < Real.cos setup.incidenceAngleRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨by
        linarith [hPhysical.incidenceAngleOnPrincipalBranch.1,
          Real.pi_pos],
        hPhysical.incidenceAngleOnPrincipalBranch.2⟩
  have hRefractionPythagorean :=
    Real.sin_sq_add_cos_sq setup.refractionAngleRadians
  have hIncidencePythagorean :=
    Real.sin_sq_add_cos_sq setup.incidenceAngleRadians
  rw [hSinRefraction] at hRefractionPythagorean
  rw [hSinIncidence] at hIncidencePythagorean
  have hCosRefractionBounds :
      (7905 / 100000 : ℝ) < Real.cos setup.refractionAngleRadians ∧
        Real.cos setup.refractionAngleRadians < (7906 / 100000 : ℝ) := by
    constructor <;>
      nlinarith only [hCosRefractionPositive, hRefractionPythagorean]
  have hCosIncidenceBounds :
      (7518 / 100000 : ℝ) < Real.cos setup.incidenceAngleRadians ∧
        Real.cos setup.incidenceAngleRadians < (7519 / 100000 : ℝ) := by
    constructor <;>
      nlinarith only [hCosIncidencePositive, hIncidencePythagorean]
  have hSinDeviationBounds :
      (3871 / 1000000 : ℝ) <
          Real.sin setup.deviationAngleRadians ∧
        Real.sin setup.deviationAngleRadians <
          (3892 / 1000000 : ℝ) := by
    rw [hGeometry.deviationIsRayBending, Real.sin_sub,
      hSinRefraction, hSinIncidence]
    constructor <;>
      nlinarith only [hCosRefractionBounds.1, hCosRefractionBounds.2,
        hCosIncidenceBounds.1, hCosIncidenceBounds.2]
  have hSinLowerTest :
      Real.sin (387 / 100000 : ℝ) < (3871 / 1000000 : ℝ) := by
    have hBound :=
      Real.sin_bound (x := (387 / 100000 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 387 / 100000),
      abs_le] at hBound
    nlinarith only [hBound.1, hBound.2]
  have hSinUpperTest :
      (3892 / 1000000 : ℝ) < Real.sin (418 / 100000 : ℝ) := by
    have hBound :=
      Real.sin_bound (x := (418 / 100000 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 418 / 100000),
      abs_le] at hBound
    nlinarith only [hBound.1, hBound.2]
  have hDeviationUpperPrincipal :
      setup.deviationAngleRadians < Real.pi / 2 := by
    rw [hGeometry.deviationIsRayBending]
    linarith [hPhysical.incidenceAngleOnPrincipalBranch.2,
      hPhysical.refractionAngleOnPrincipalBranch.1]
  have hLowerTestOnPrincipalBranch :
      -(Real.pi / 2) ≤ (387 / 100000 : ℝ) ∧
        (387 / 100000 : ℝ) ≤ Real.pi / 2 := by
    constructor
    · linarith [Real.pi_pos]
    · nlinarith only [Real.two_le_pi]
  have hUpperTestOnPrincipalBranch :
      -(Real.pi / 2) ≤ (418 / 100000 : ℝ) ∧
        (418 / 100000 : ℝ) ≤ Real.pi / 2 := by
    constructor
    · linarith [Real.pi_pos]
    · nlinarith only [Real.two_le_pi]
  have hDeviationOnPrincipalBranch :
      -(Real.pi / 2) ≤ setup.deviationAngleRadians ∧
        setup.deviationAngleRadians ≤ Real.pi / 2 := by
    constructor
    · linarith [hPhysical.deviationAngleNonnegative, Real.pi_pos]
    · exact hDeviationUpperPrincipal.le
  have hDeviationLower :
      (387 / 100000 : ℝ) < setup.deviationAngleRadians := by
    calc
      (387 / 100000 : ℝ) =
          Real.arcsin (Real.sin (387 / 100000 : ℝ)) :=
        (Real.arcsin_sin hLowerTestOnPrincipalBranch.1
          hLowerTestOnPrincipalBranch.2).symm
      _ < Real.arcsin (Real.sin setup.deviationAngleRadians) :=
        Real.arcsin_lt_arcsin
          (Real.neg_one_le_sin _)
          (hSinLowerTest.trans hSinDeviationBounds.1)
          (Real.sin_le_one _)
      _ = setup.deviationAngleRadians :=
        Real.arcsin_sin hDeviationOnPrincipalBranch.1
          hDeviationOnPrincipalBranch.2
  have hDeviationUpper :
      setup.deviationAngleRadians < (418 / 100000 : ℝ) := by
    calc
      setup.deviationAngleRadians =
          Real.arcsin (Real.sin setup.deviationAngleRadians) :=
        (Real.arcsin_sin hDeviationOnPrincipalBranch.1
          hDeviationOnPrincipalBranch.2).symm
      _ < Real.arcsin (Real.sin (418 / 100000 : ℝ)) :=
        Real.arcsin_lt_arcsin
          (Real.neg_one_le_sin _)
          (hSinDeviationBounds.2.trans hSinUpperTest)
          (Real.sin_le_one _)
      _ = (418 / 100000 : ℝ) :=
        Real.arcsin_sin hUpperTestOnPrincipalBranch.1
          hUpperTestOnPrincipalBranch.2
  have hPiLower : (157 / 50 : ℝ) < Real.pi := by
    have hCosBase :=
      Real.cos_bound (x := (157 / 3200 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 157 / 3200),
      abs_le] at hCosBase
    have h0 :
        (998796 / 1000000 : ℝ) < Real.cos (157 / 3200 : ℝ) := by
      nlinarith only [hCosBase.1]
    have h1 :
        (9951868 / 10000000 : ℝ) < Real.cos (157 / 1600 : ℝ) := by
      rw [show (157 / 1600 : ℝ) = 2 * (157 / 3200 : ℝ) by
          norm_num,
        Real.cos_two_mul]
      nlinarith only [h0]
    have h2 :
        (9807935 / 10000000 : ℝ) < Real.cos (157 / 800 : ℝ) := by
      rw [show (157 / 800 : ℝ) = 2 * (157 / 1600 : ℝ) by
          norm_num,
        Real.cos_two_mul]
      nlinarith only [h1]
    have h3 :
        (9239117 / 10000000 : ℝ) < Real.cos (157 / 400 : ℝ) := by
      rw [show (157 / 400 : ℝ) = 2 * (157 / 800 : ℝ) by
          norm_num,
        Real.cos_two_mul]
      nlinarith only [h2]
    have h4 :
        (7072256 / 10000000 : ℝ) < Real.cos (157 / 200 : ℝ) := by
      rw [show (157 / 200 : ℝ) = 2 * (157 / 400 : ℝ) by
          norm_num,
        Real.cos_two_mul]
      nlinarith only [h3]
    have hSqrtTwoSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      norm_num
    have hSqrtTwoNonnegative : 0 ≤ Real.sqrt 2 :=
      Real.sqrt_nonneg 2
    have hCosPiFourUpper :
        Real.cos (Real.pi / 4) < (7072 / 10000 : ℝ) := by
      rw [Real.cos_pi_div_four]
      nlinarith only [hSqrtTwoSq, hSqrtTwoNonnegative]
    have hCosComparison :
        Real.cos (Real.pi / 4) < Real.cos (157 / 200 : ℝ) := by
      linarith only [h4, hCosPiFourUpper]
    have hAngleMem :
        (157 / 200 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · norm_num
      · linarith only [Real.two_le_pi]
    have hPiFourMem :
        Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · positivity
      · nlinarith only [Real.pi_pos]
    by_contra h
    have hOrder : Real.pi / 4 ≤ (157 / 200 : ℝ) := by
      linarith only [h]
    have hCosOrder :=
      Real.strictAntiOn_cos.antitoneOn hPiFourMem hAngleMem hOrder
    linarith only [hCosOrder, hCosComparison]
  have hPiUpper : Real.pi < (63 / 20 : ℝ) := by
    have hCosHalf :=
      Real.cos_bound (x := (63 / 160 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 63 / 160),
      abs_le] at hCosHalf
    have hCosHalfUpper :
        Real.cos (63 / 160 : ℝ) < (9238 / 10000 : ℝ) := by
      nlinarith only [hCosHalf.2]
    have hCosHalfPositive : 0 < Real.cos (63 / 160 : ℝ) := by
      nlinarith only [hCosHalf.1]
    have hCosFullUpper :
        Real.cos (63 / 80 : ℝ) < (707 / 1000 : ℝ) := by
      rw [show (63 / 80 : ℝ) = 2 * (63 / 160 : ℝ) by
          norm_num,
        Real.cos_two_mul]
      nlinarith only [hCosHalfUpper, hCosHalfPositive]
    have hSqrtTwoSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      norm_num
    have hSqrtTwoNonnegative : 0 ≤ Real.sqrt 2 :=
      Real.sqrt_nonneg 2
    have hCosPiFourLower :
        (707 / 1000 : ℝ) < Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
      nlinarith only [hSqrtTwoSq, hSqrtTwoNonnegative]
    have hCosComparison :
        Real.cos (63 / 80 : ℝ) < Real.cos (Real.pi / 4) := by
      linarith only [hCosFullUpper, hCosPiFourLower]
    have hAngleMem :
        (63 / 80 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · norm_num
      · linarith only [Real.two_le_pi]
    have hPiFourMem :
        Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · positivity
      · nlinarith only [Real.pi_pos]
    by_contra h
    have hOrder : (63 / 80 : ℝ) ≤ Real.pi / 4 := by
      linarith only [h]
    have hCosOrder :=
      Real.strictAntiOn_cos.antitoneOn hAngleMem hPiFourMem hOrder
    linarith only [hCosOrder, hCosComparison]
  have hDegreeLower :
      (22 / 100 : ℝ) <
        radiansToDegrees setup.deviationAngleRadians := by
    unfold radiansToDegrees
    apply (lt_div_iff₀ Real.pi_pos).2
    nlinarith only [hDeviationLower, hPiUpper]
  have hDegreeUpper :
      radiansToDegrees setup.deviationAngleRadians <
        (24 / 100 : ℝ) := by
    unfold radiansToDegrees
    apply (div_lt_iff₀ Real.pi_pos).2
    nlinarith only [hDeviationUpper, hPiLower]
  have hMatches :
      MatchesWithinHundredthDegree setup.deviationAngleRadians .A := by
    rw [MatchesWithinHundredthDegree, AnswerChoice.angleDegrees, abs_lt]
    constructor <;> linarith
  refine ⟨hDeviation, hMatches, ?_⟩
  intro other
  have hAbsA :
      |radiansToDegrees setup.deviationAngleRadians - (23 / 100 : ℝ)| <
        (1 / 100 : ℝ) := hMatches
  cases other with
  | A =>
      rfl
  | B =>
      change
        |radiansToDegrees setup.deviationAngleRadians - (23 / 100 : ℝ)| ≤
          |radiansToDegrees setup.deviationAngleRadians - (30 / 100 : ℝ)|
      rw [abs_of_nonpos (by linarith : radiansToDegrees
        setup.deviationAngleRadians - (30 / 100 : ℝ) ≤ 0)]
      linarith
  | C =>
      change
        |radiansToDegrees setup.deviationAngleRadians - (23 / 100 : ℝ)| ≤
          |radiansToDegrees setup.deviationAngleRadians - (20 / 100 : ℝ)|
      rw [abs_of_nonneg (by linarith : 0 ≤ radiansToDegrees
        setup.deviationAngleRadians - (20 / 100 : ℝ))]
      linarith
  | D =>
      change
        |radiansToDegrees setup.deviationAngleRadians - (23 / 100 : ℝ)| ≤
          |radiansToDegrees setup.deviationAngleRadians - (25 / 100 : ℝ)|
      rw [abs_of_nonpos (by linarith : radiansToDegrees
        setup.deviationAngleRadians - (25 / 100 : ℝ) ≤ 0)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0101

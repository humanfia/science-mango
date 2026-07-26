import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Two-ray interference with a variable material path

This file formalizes the two reflected rays, their common screen point `P`,
the variable material length `L` in ray 2, and the intensity graph from the
problem.  Lengths are dimensionful Physlib quantities.  Refractive indices,
intensities, nanometer graph coordinates, and multi-turn phase readouts in
radians are dimensionless real scalars.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0088

open CarriesDimension Dimension

/-- A physical length with a real scalar carrier. -/
abbrev DimLength := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices used by the figure's horizontal axis, which is labelled in nanometers. -/
def nanometerUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.nanometers }

/-- Construct a physical length from its nanometer readout. -/
noncomputable def lengthInNanometers (value : ℝ) : DimLength :=
  toDimensionful nanometerUnitChoices ⟨value⟩

/-- The scalar nanometer readout of a physical length. -/
def nanometersValue (length : DimLength) : ℝ :=
  (length nanometerUnitChoices).val

/-- The Euclidean plane containing the two reflected ray routes. -/
abbrev DiagramPlane := EuclideanSpace ℝ (Fin 2)

/-- Labels `1` and `2` for the two rays in the problem statement. -/
inductive RayLabel where
  | rayOne
  | rayTwo
  deriving DecidableEq, Repr

/-- The two optical media relevant to the variable path segment. -/
inductive OpticalMedium where
  | air
  | insertedMaterial
  deriving DecidableEq, Repr

/--
A ray route with the source, the mirror at which it is reflected, and its
destination on the screen.
-/
structure ReflectedRayRoute where
  sourcePoint : DiagramPlane
  mirrorPoint : DiagramPlane
  destinationPoint : DiagramPlane

/--
The physical quantities and labelled readouts of the variable-length
two-ray interference experiment.

The arguments to `materialLengthTraversed`, `opticalPathDifference`,
`phaseDifferenceRadiansAtP`, and `intensityAtP` are the nanometer readout of
the controlled material length `L`.  Their names make this scalar projection
explicit; the corresponding physical lengths remain values of `DimLength`.
-/
structure TwoRayInterferenceExperiment where
  /-- The reflected route followed by each labelled ray. -/
  route : RayLabel → ReflectedRayRoute
  /-- Figure label `P`, the common observation point on the screen. -/
  screenPointP : DiagramPlane
  /-- Wavelength in air carried by each ray before the material is inserted. -/
  wavelengthInAir : RayLabel → DimLength
  /-- Initial phase readout of each ray, in radians. -/
  initialPhaseRadians : RayLabel → ℝ
  /-- Dimensionless refractive index of each optical medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Physical length that each ray traverses inside the inserted material. -/
  materialLengthTraversed : RayLabel → ℝ → DimLength
  /-- Largest allowed material length, stated as `2400 nm`. -/
  maximumMaterialLength : DimLength
  /-- Figure-axis endpoint `L_s`, stated as `900 nm`. -/
  graphEndLengthLs : DimLength
  /-- Nanometer coordinate of the first intensity minimum read from the graph. -/
  firstMinimumLengthNm : ℝ
  /-- Physical optical-path difference of ray 2 relative to ray 1 at `P`. -/
  opticalPathDifference : ℝ → DimLength
  /-- Unwrapped phase difference at `P`, as a multi-turn radian readout. -/
  phaseDifferenceRadiansAtP : ℝ → ℝ
  /-- Intensity measured at `P` as the material length is varied. -/
  intensityAtP : ℝ → ℝ
  /-- Intensity contributed at `P` by either ray separately. -/
  singleRayIntensityAtP : ℝ

/-- A function has a maximum at `x` on the specified scalar domain. -/
def IsMaximumOn (f : ℝ → ℝ) (domain : Set ℝ) (x : ℝ) : Prop :=
  x ∈ domain ∧ ∀ y ∈ domain, f y ≤ f x

/--
`x` is the first strict minimum of `f` after zero on `[0, stop]`: it is a
global minimum there, and all earlier positive coordinates have larger value.
-/
def IsFirstStrictMinimumAfterZero
    (f : ℝ → ℝ) (stop x : ℝ) : Prop :=
  x ∈ Set.Ioc 0 stop ∧
    (∀ y ∈ Set.Icc 0 stop, f x ≤ f y) ∧
    (∀ y ∈ Set.Ioc 0 x, f x < f y)

/--
Textual setup data: both rays reach `P`, begin in phase with the same positive
air wavelength, ray 1 avoids the material, ray 2 traverses its controlled
length, and the available range is `0` through `2400 nm`.
-/
structure MatchesProblemSetup
    (experiment : TwoRayInterferenceExperiment) : Prop where
  bothRoutesReachP :
    ∀ ray, (experiment.route ray).destinationPoint = experiment.screenPointP
  initiallyInPhase :
    experiment.initialPhaseRadians .rayOne =
      experiment.initialPhaseRadians .rayTwo
  sameWavelengthInAir :
    experiment.wavelengthInAir .rayOne = experiment.wavelengthInAir .rayTwo
  wavelengthPositive :
    0 < nanometersValue (experiment.wavelengthInAir .rayOne)
  airIndexReadout : experiment.refractiveIndex .air = 1
  materialIndexGreaterThanAir :
    experiment.refractiveIndex .air <
      experiment.refractiveIndex .insertedMaterial
  maximumLengthReadout :
    experiment.maximumMaterialLength = lengthInNanometers 2400
  rayOneAvoidsMaterial :
    ∀ lengthNm ∈ Set.Icc (0 : ℝ) 2400,
      experiment.materialLengthTraversed .rayOne lengthNm =
        lengthInNanometers 0
  rayTwoTraversesControlledLength :
    ∀ lengthNm ∈ Set.Icc (0 : ℝ) 2400,
      experiment.materialLengthTraversed .rayTwo lengthNm =
        lengthInNanometers lengthNm
  singleRayIntensityPositive : 0 < experiment.singleRayIntensityAtP

/--
Data read from the supplied graph.  The interval from `0` to `L_s` is divided
into six equal horizontal cells; the unique first minimum is at the fifth
gridline, so its coordinate is `(5/6) L_s`.  The curve starts at a maximum and
has risen again by `L_s`.
-/
structure MatchesIntensityFigure
    (experiment : TwoRayInterferenceExperiment) : Prop where
  graphEndReadout : experiment.graphEndLengthLs = lengthInNanometers 900
  minimumAtFifthOfSixGridCells :
    experiment.firstMinimumLengthNm =
      (5 / 6 : ℝ) * nanometersValue experiment.graphEndLengthLs
  startsAtMaximum :
    IsMaximumOn experiment.intensityAtP (Set.Icc 0 900) 0
  firstMinimumReadout :
    IsFirstStrictMinimumAfterZero
      experiment.intensityAtP 900 experiment.firstMinimumLengthNm
  risesAfterMinimum :
    experiment.intensityAtP experiment.firstMinimumLengthNm <
      experiment.intensityAtP 900

/--
The governing optical laws for the experiment.

Replacing an air segment of length `L` by material adds optical path
`(n_material - n_air) L`.  The unwrapped phase is `2π` times optical path
difference divided by wavelength.  Equal coherent beams then obey the
standard cosine interference-intensity law.
-/
structure ObeysTwoRayInterferenceLaws
    (experiment : TwoRayInterferenceExperiment) : Prop where
  opticalPathIncrement :
    ∀ lengthNm ∈ Set.Icc (0 : ℝ) 2400,
      nanometersValue (experiment.opticalPathDifference lengthNm) =
        (experiment.refractiveIndex .insertedMaterial -
            experiment.refractiveIndex .air) *
          nanometersValue
            (experiment.materialLengthTraversed .rayTwo lengthNm)
  phaseFromOpticalPath :
    ∀ lengthNm ∈ Set.Icc (0 : ℝ) 2400,
      experiment.phaseDifferenceRadiansAtP lengthNm =
        2 * Real.pi *
          nanometersValue (experiment.opticalPathDifference lengthNm) /
            nanometersValue (experiment.wavelengthInAir .rayOne)
  equalBeamInterferenceIntensity :
    ∀ lengthNm ∈ Set.Icc (0 : ℝ) 2400,
      experiment.intensityAtP lengthNm =
        2 * experiment.singleRayIntensityAtP *
          (1 + Real.cos (experiment.phaseDifferenceRadiansAtP lengthNm))

/-- The four multiples of the air wavelength printed as answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless wavelength multiple displayed by each answer choice. -/
def answerWavelengthMultiple : AnswerChoice → ℝ
  | .A => 2 / 5
  | .B => 6 / 5
  | .C => 4 / 5
  | .D => 8 / 5

/--
The first destructive-interference minimum in the graph calibrates the added
optical path to one half of the common air wavelength.  This is an
intermediate consequence of the figure and governing laws, not input data.
-/
lemma firstMinimum_hasHalfWavelengthOpticalPath
    (experiment : TwoRayInterferenceExperiment)
    (hSetup : MatchesProblemSetup experiment)
    (hFigure : MatchesIntensityFigure experiment)
    (hLaws : ObeysTwoRayInterferenceLaws experiment) :
    nanometersValue
        (experiment.opticalPathDifference experiment.firstMinimumLengthNm) =
      (1 / 2 : ℝ) *
        nanometersValue (experiment.wavelengthInAir .rayOne) := by
  have hNanometers (x : ℝ) :
      nanometersValue (lengthInNanometers x) = x := by
    simp [nanometersValue, lengthInNanometers, toDimensionful]
  have hMinimumLength : experiment.firstMinimumLengthNm = 750 := by
    rw [hFigure.minimumAtFifthOfSixGridCells,
      hFigure.graphEndReadout, hNanometers]
    norm_num
  have hMinimumInRange :
      experiment.firstMinimumLengthNm ∈ Set.Icc (0 : ℝ) 2400 := by
    rw [hMinimumLength]
    norm_num
  have hWavelengthPositive :
      0 < nanometersValue (experiment.wavelengthInAir .rayOne) :=
    hSetup.wavelengthPositive
  have hIndexIncrementPositive :
      0 <
        experiment.refractiveIndex .insertedMaterial -
          experiment.refractiveIndex .air :=
    sub_pos.mpr hSetup.materialIndexGreaterThanAir
  let phaseRate : ℝ :=
    2 * Real.pi *
        (experiment.refractiveIndex .insertedMaterial -
          experiment.refractiveIndex .air) /
      nanometersValue (experiment.wavelengthInAir .rayOne)
  have hPhaseRatePositive : 0 < phaseRate := by
    dsimp [phaseRate]
    positivity
  have hOpticalPath (lengthNm : ℝ)
      (hLength : lengthNm ∈ Set.Icc (0 : ℝ) 2400) :
      nanometersValue (experiment.opticalPathDifference lengthNm) =
        (experiment.refractiveIndex .insertedMaterial -
          experiment.refractiveIndex .air) * lengthNm := by
    rw [hLaws.opticalPathIncrement lengthNm hLength,
      hSetup.rayTwoTraversesControlledLength lengthNm hLength,
      hNanometers]
  have hPhase (lengthNm : ℝ)
      (hLength : lengthNm ∈ Set.Icc (0 : ℝ) 2400) :
      experiment.phaseDifferenceRadiansAtP lengthNm =
        phaseRate * lengthNm := by
    rw [hLaws.phaseFromOpticalPath lengthNm hLength,
      hOpticalPath lengthNm hLength]
    dsimp [phaseRate]
    ring
  have hIntensity (lengthNm : ℝ)
      (hLength : lengthNm ∈ Set.Icc (0 : ℝ) 2400) :
      experiment.intensityAtP lengthNm =
        2 * experiment.singleRayIntensityAtP *
          (1 + Real.cos (experiment.phaseDifferenceRadiansAtP lengthNm)) :=
    hLaws.equalBeamInterferenceIntensity lengthNm hLength
  have hNineHundredInRange : (900 : ℝ) ∈ Set.Icc (0 : ℝ) 2400 := by
    norm_num
  have hPhaseMinimum :=
    hPhase experiment.firstMinimumLengthNm hMinimumInRange
  have hPhaseNineHundred := hPhase 900 hNineHundredInRange
  have hIntensityMinimum :=
    hIntensity experiment.firstMinimumLengthNm hMinimumInRange
  have hIntensityNineHundred := hIntensity 900 hNineHundredInRange
  let firstPiLength : ℝ := Real.pi / phaseRate
  have hFirstPiLengthPositive : 0 < firstPiLength := by
    dsimp [firstPiLength]
    exact div_pos Real.pi_pos hPhaseRatePositive
  have hFirstPiLengthAtMostNineHundred : firstPiLength ≤ 900 := by
    by_contra hNot
    have hNineHundredLtFirstPi : (900 : ℝ) < firstPiLength :=
      lt_of_not_ge hNot
    have hPhaseNineHundredLtPi :
        experiment.phaseDifferenceRadiansAtP 900 < Real.pi := by
      rw [hPhaseNineHundred]
      dsimp [firstPiLength] at hNineHundredLtFirstPi
      have hRateBound :
          (900 : ℝ) * phaseRate < Real.pi :=
        (lt_div_iff₀ hPhaseRatePositive).mp hNineHundredLtFirstPi
      nlinarith
    have hPhaseMinimumNonnegative :
        0 ≤
          experiment.phaseDifferenceRadiansAtP
            experiment.firstMinimumLengthNm := by
      rw [hPhaseMinimum, hMinimumLength]
      positivity
    have hPhaseMinimumLtNineHundred :
        experiment.phaseDifferenceRadiansAtP
            experiment.firstMinimumLengthNm <
          experiment.phaseDifferenceRadiansAtP 900 := by
      rw [hPhaseMinimum, hPhaseNineHundred, hMinimumLength]
      nlinarith
    have hCosNineHundredLtMinimum :
        Real.cos (experiment.phaseDifferenceRadiansAtP 900) <
          Real.cos
            (experiment.phaseDifferenceRadiansAtP
              experiment.firstMinimumLengthNm) :=
      Real.strictAntiOn_cos
        ⟨hPhaseMinimumNonnegative,
          (hPhaseMinimumLtNineHundred.trans
            hPhaseNineHundredLtPi).le⟩
        ⟨(hPhaseMinimumNonnegative.trans hPhaseMinimumLtNineHundred.le),
          hPhaseNineHundredLtPi.le⟩
        hPhaseMinimumLtNineHundred
    have hIntensityNineHundredLtMinimum :
        experiment.intensityAtP 900 <
          experiment.intensityAtP experiment.firstMinimumLengthNm := by
      calc
        experiment.intensityAtP 900 =
            2 * experiment.singleRayIntensityAtP *
              (1 + Real.cos
                (experiment.phaseDifferenceRadiansAtP 900)) :=
          hIntensityNineHundred
        _ <
            2 * experiment.singleRayIntensityAtP *
              (1 + Real.cos
                (experiment.phaseDifferenceRadiansAtP
                  experiment.firstMinimumLengthNm)) := by
          exact mul_lt_mul_of_pos_left
            (by linarith)
            (mul_pos (by norm_num) hSetup.singleRayIntensityPositive)
        _ = experiment.intensityAtP experiment.firstMinimumLengthNm :=
          hIntensityMinimum.symm
    exact (lt_asymm hIntensityNineHundredLtMinimum
      hFigure.risesAfterMinimum)
  have hFirstPiLengthInFigureRange :
      firstPiLength ∈ Set.Icc (0 : ℝ) 900 :=
    ⟨hFirstPiLengthPositive.le, hFirstPiLengthAtMostNineHundred⟩
  have hFirstPiLengthInLawRange :
      firstPiLength ∈ Set.Icc (0 : ℝ) 2400 :=
    ⟨hFirstPiLengthPositive.le,
      hFirstPiLengthAtMostNineHundred.trans (by norm_num)⟩
  have hPhaseFirstPiLength :
      experiment.phaseDifferenceRadiansAtP firstPiLength = Real.pi := by
    rw [hPhase firstPiLength hFirstPiLengthInLawRange]
    dsimp [firstPiLength]
    field_simp [ne_of_gt hPhaseRatePositive]
  have hIntensityFirstPiLength :
      experiment.intensityAtP firstPiLength = 0 := by
    rw [hIntensity firstPiLength hFirstPiLengthInLawRange,
      hPhaseFirstPiLength, Real.cos_pi]
    ring
  rcases hFigure.firstMinimumReadout with
    ⟨_, hMinimumIsGlobal, hMinimumIsFirst⟩
  have hIntensityMinimumNonnegative :
      0 ≤ experiment.intensityAtP experiment.firstMinimumLengthNm := by
    rw [hIntensityMinimum]
    have hCosineLowerBound :=
      Real.neg_one_le_cos
        (experiment.phaseDifferenceRadiansAtP
          experiment.firstMinimumLengthNm)
    exact mul_nonneg
      (mul_nonneg (by norm_num) hSetup.singleRayIntensityPositive.le)
      (by linarith)
  have hIntensityMinimumZero :
      experiment.intensityAtP experiment.firstMinimumLengthNm = 0 := by
    apply le_antisymm
    · rw [← hIntensityFirstPiLength]
      exact hMinimumIsGlobal firstPiLength hFirstPiLengthInFigureRange
    · exact hIntensityMinimumNonnegative
  have hMinimumLengthLeFirstPi :
      experiment.firstMinimumLengthNm ≤ firstPiLength := by
    by_contra hNot
    have hFirstPiLtMinimum :
        firstPiLength < experiment.firstMinimumLengthNm :=
      lt_of_not_ge hNot
    have hStrictAtFirstPi :=
      hMinimumIsFirst firstPiLength
        ⟨hFirstPiLengthPositive, hFirstPiLtMinimum.le⟩
    rw [hIntensityMinimumZero, hIntensityFirstPiLength] at hStrictAtFirstPi
    exact (lt_irrefl 0 hStrictAtFirstPi)
  have hPhaseRateTimesFirstPi : phaseRate * firstPiLength = Real.pi := by
    dsimp [firstPiLength]
    field_simp [ne_of_gt hPhaseRatePositive]
  have hPhaseMinimumInPrincipalInterval :
      experiment.phaseDifferenceRadiansAtP
          experiment.firstMinimumLengthNm ∈
        Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · rw [hPhaseMinimum, hMinimumLength]
      positivity
    · rw [hPhaseMinimum]
      calc
        phaseRate * experiment.firstMinimumLengthNm ≤
            phaseRate * firstPiLength :=
          mul_le_mul_of_nonneg_left hMinimumLengthLeFirstPi
            hPhaseRatePositive.le
        _ = Real.pi := hPhaseRateTimesFirstPi
  have hOnePlusCosMinimumZero :
      1 +
          Real.cos
            (experiment.phaseDifferenceRadiansAtP
              experiment.firstMinimumLengthNm) =
        0 := by
    have hProductZero :
        2 * experiment.singleRayIntensityAtP *
            (1 +
              Real.cos
                (experiment.phaseDifferenceRadiansAtP
                  experiment.firstMinimumLengthNm)) =
          0 := by
      calc
        2 * experiment.singleRayIntensityAtP *
              (1 +
                Real.cos
                  (experiment.phaseDifferenceRadiansAtP
                    experiment.firstMinimumLengthNm)) =
            experiment.intensityAtP experiment.firstMinimumLengthNm :=
          hIntensityMinimum.symm
        _ = 0 := hIntensityMinimumZero
    rcases mul_eq_zero.mp hProductZero with hFactorZero | hCosineZero
    · exact False.elim
        ((ne_of_gt
          (mul_pos (by norm_num) hSetup.singleRayIntensityPositive))
          hFactorZero)
    · exact hCosineZero
  have hCosMinimum :
      Real.cos
          (experiment.phaseDifferenceRadiansAtP
            experiment.firstMinimumLengthNm) =
        -1 := by
    linarith
  have hPhaseMinimumIsPi :
      experiment.phaseDifferenceRadiansAtP
          experiment.firstMinimumLengthNm = Real.pi := by
    apply Real.injOn_cos hPhaseMinimumInPrincipalInterval
      ⟨le_of_lt Real.pi_pos, le_rfl⟩
    rw [hCosMinimum, Real.cos_pi]
  rw [hOpticalPath experiment.firstMinimumLengthNm hMinimumInRange]
  have hPhaseEquation :
      phaseRate * experiment.firstMinimumLengthNm = Real.pi := by
    rw [← hPhaseMinimum, hPhaseMinimumIsPi]
  dsimp [phaseRate] at hPhaseEquation
  field_simp [ne_of_gt hWavelengthPositive] at hPhaseEquation
  nlinarith [Real.pi_pos]

/--
At `L = 1200 nm`, the optical-path difference is `0.80 λ`, answer choice C.
Equivalently, the unwrapped phase difference is `1.60π = 8π/5` radians.

Blueprint: `thm:physics:phyx_mini_0088:target`.
-/
theorem phaseDifferenceAtTwelveHundredNm_isChoiceC
    (experiment : TwoRayInterferenceExperiment)
    (hSetup : MatchesProblemSetup experiment)
    (hFigure : MatchesIntensityFigure experiment)
    (hLaws : ObeysTwoRayInterferenceLaws experiment) :
    nanometersValue (experiment.opticalPathDifference 1200) =
        answerWavelengthMultiple .C *
          nanometersValue (experiment.wavelengthInAir .rayOne) ∧
      experiment.phaseDifferenceRadiansAtP 1200 = 8 * Real.pi / 5 := by
  have hNanometers (x : ℝ) :
      nanometersValue (lengthInNanometers x) = x := by
    simp [nanometersValue, lengthInNanometers, toDimensionful]
  have hMinimumLength : experiment.firstMinimumLengthNm = 750 := by
    rw [hFigure.minimumAtFifthOfSixGridCells,
      hFigure.graphEndReadout, hNanometers]
    norm_num
  have hSevenHundredFiftyInRange :
      (750 : ℝ) ∈ Set.Icc (0 : ℝ) 2400 := by
    norm_num
  have hTwelveHundredInRange :
      (1200 : ℝ) ∈ Set.Icc (0 : ℝ) 2400 := by
    norm_num
  have hMinimumOpticalPath :=
    firstMinimum_hasHalfWavelengthOpticalPath
      experiment hSetup hFigure hLaws
  rw [hMinimumLength] at hMinimumOpticalPath
  have hOpticalPathSevenHundredFifty :
      nanometersValue (experiment.opticalPathDifference 750) =
        (experiment.refractiveIndex .insertedMaterial -
          experiment.refractiveIndex .air) * 750 := by
    rw [hLaws.opticalPathIncrement 750 hSevenHundredFiftyInRange,
      hSetup.rayTwoTraversesControlledLength
        750 hSevenHundredFiftyInRange,
      hNanometers]
  have hOpticalPathTwelveHundred :
      nanometersValue (experiment.opticalPathDifference 1200) =
        (experiment.refractiveIndex .insertedMaterial -
          experiment.refractiveIndex .air) * 1200 := by
    rw [hLaws.opticalPathIncrement 1200 hTwelveHundredInRange,
      hSetup.rayTwoTraversesControlledLength
        1200 hTwelveHundredInRange,
      hNanometers]
  have hChoiceC :
      nanometersValue (experiment.opticalPathDifference 1200) =
        answerWavelengthMultiple .C *
          nanometersValue (experiment.wavelengthInAir .rayOne) := by
    rw [hOpticalPathTwelveHundred]
    change
      (experiment.refractiveIndex .insertedMaterial -
            experiment.refractiveIndex .air) *
          1200 =
        (4 / 5 : ℝ) *
          nanometersValue (experiment.wavelengthInAir .rayOne)
    nlinarith [hMinimumOpticalPath, hOpticalPathSevenHundredFifty]
  constructor
  · exact hChoiceC
  · rw [hLaws.phaseFromOpticalPath 1200 hTwelveHundredInRange,
      hChoiceC]
    change
      2 * Real.pi *
            ((4 / 5 : ℝ) *
              nanometersValue (experiment.wavelengthInAir .rayOne)) /
          nanometersValue (experiment.wavelengthInAir .rayOne) =
        8 * Real.pi / 5
    field_simp [ne_of_gt hSetup.wavelengthPositive]; norm_num

end PhyXMiniProblems.ProblemPhyXMini0088

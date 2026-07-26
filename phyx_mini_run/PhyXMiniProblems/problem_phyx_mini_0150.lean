import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0150

open Dimension

/-!
# Two-wavelength refraction through an equilateral flint-glass prism

The primary figure shows a parallel incident beam containing wavelengths
`λ₁ = 455 nm` and `λ₂ = 642 nm`.  It enters an equilateral prism at `45°` to
the entry-face normal.  The two outgoing rays are measured from the exit-face
normal and labeled `θ₁` and `θ₂`.  The source records choice C, `68.1°`, but
does not provide the silicate-flint dispersion table needed to derive that
number.  Consequently the target below gives the source-supported symbolic
Snell-law prediction in terms of the wavelength-dependent refractive indices.

Wavelengths are represented by Physlib dimensionful length quantities.
Refractive indices and degree readouts are dimensionless real numbers, while
the physical angles themselves use Mathlib's `Real.Angle`.
-/

/-- A physical length represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a scalar in the requested length unit. -/
def lengthValueIn (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The scalar nanometre readout used for the two stated wavelengths. -/
def nanometersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- Interpret a numerical degree readout as a physical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- The two monochromatic components of the incident parallel beam. -/
inductive BeamLabel where
  | lambdaOne455nm
  | lambdaTwo642nm
  deriving DecidableEq, Repr

/-- The homogeneous media on the two sides of each prism face. -/
inductive OpticalMedium where
  | air
  | silicateFlintGlass
  deriving DecidableEq, Repr

/-- The three `60°` vertex labels explicitly shown on the triangular prism. -/
inductive PrismVertex where
  | apex
  | lowerLeft
  | lowerRight
  deriving DecidableEq, Repr

/-- The two angles printed beside the emerging rays in the source figure. -/
inductive ExitAngleLabel where
  | thetaOne
  | thetaTwo
  deriving DecidableEq, Repr

/-- The three normal-based angles used to trace one beam through the prism. -/
structure PrismRayAngles where
  /-- Refraction angle inside the glass at the first face. -/
  firstRefractionToNormal : Real.Angle
  /-- Incidence angle inside the glass at the second face. -/
  secondIncidenceToNormal : Real.Angle
  /-- Emergence angle in air, measured from the exit-face normal. -/
  emergenceToNormal : Real.Angle

/--
Physical and figure-derived data for the two-wavelength prism experiment.
The refractive index is a dimensionless material readout depending on both
medium and wavelength.
-/
structure PrismExperiment where
  wavelength : BeamLabel → LengthQuantity
  refractiveIndex : OpticalMedium → BeamLabel → ℝ
  entryIncidenceToNormal : Real.Angle
  apexAngle : Real.Angle
  rayAngles : BeamLabel → PrismRayAngles
  shownInteriorAngle : PrismVertex → Real.Angle
  shownExitAngleToNormal : ExitAngleLabel → Real.Angle

/-- The dimensional and angular values printed in the problem and figure. -/
structure HasStatedReadouts (experiment : PrismExperiment) : Prop where
  lambda_one_nanometers :
    nanometersValue (experiment.wavelength .lambdaOne455nm) = 455
  lambda_two_nanometers :
    nanometersValue (experiment.wavelength .lambdaTwo642nm) = 642
  entry_angle_to_normal : experiment.entryIncidenceToNormal = degrees 45
  equilateral_angles : ∀ vertex, experiment.shownInteriorAngle vertex = degrees 60
  apex_matches_figure :
    experiment.apexAngle = experiment.shownInteriorAngle .apex

/-- The acute principal branch for an angle measured from a face normal. -/
def IsPhysicalNormalAngle (angle : Real.Angle) : Prop :=
  0 ≤ angle.toReal ∧ angle.toReal ≤ Real.pi / 2

/--
Snell's law at both faces together with the geometry of an equilateral prism.
No requested numerical emergence angle occurs in these governing laws.
-/
structure SatisfiesPrismRayLaws
    (experiment : PrismExperiment) (beam : BeamLabel) : Prop where
  air_index_positive : 0 < experiment.refractiveIndex .air beam
  glass_index_positive : 0 < experiment.refractiveIndex .silicateFlintGlass beam
  entry_incidence_physical :
    IsPhysicalNormalAngle experiment.entryIncidenceToNormal
  first_refraction_physical :
    IsPhysicalNormalAngle
      (experiment.rayAngles beam).firstRefractionToNormal
  second_incidence_physical :
    IsPhysicalNormalAngle
      (experiment.rayAngles beam).secondIncidenceToNormal
  emergence_physical :
    IsPhysicalNormalAngle (experiment.rayAngles beam).emergenceToNormal
  snell_at_entry :
    experiment.refractiveIndex .air beam *
        Real.Angle.sin experiment.entryIncidenceToNormal =
      experiment.refractiveIndex .silicateFlintGlass beam *
        Real.Angle.sin (experiment.rayAngles beam).firstRefractionToNormal
  equilateral_prism_geometry :
    (experiment.rayAngles beam).firstRefractionToNormal +
        (experiment.rayAngles beam).secondIncidenceToNormal =
      experiment.apexAngle
  snell_at_exit :
    experiment.refractiveIndex .silicateFlintGlass beam *
        Real.Angle.sin (experiment.rayAngles beam).secondIncidenceToNormal =
      experiment.refractiveIndex .air beam *
        Real.Angle.sin (experiment.rayAngles beam).emergenceToNormal

/-- The two figure labels denote the emergence angles of `λ₁` and `λ₂`. -/
structure MatchesShownExitLabels (experiment : PrismExperiment) : Prop where
  theta_one_is_lambda_one :
    experiment.shownExitAngleToNormal .thetaOne =
      (experiment.rayAngles .lambdaOne455nm).emergenceToNormal
  theta_two_is_lambda_two :
    experiment.shownExitAngleToNormal .thetaTwo =
      (experiment.rayAngles .lambdaTwo642nm).emergenceToNormal

/--
The emergence angle, in radians on the acute branch, predicted by applying
Snell's law at entry, the prism-angle relation, and Snell's law at exit.

The refractive indices remain symbolic because the source gives no numerical
dispersion calibration for the named glass.
-/
def snellPredictedEmergenceRadians
    (experiment : PrismExperiment) (beam : BeamLabel) : ℝ :=
  Real.arcsin
    (experiment.refractiveIndex .silicateFlintGlass beam /
        experiment.refractiveIndex .air beam *
      Real.sin
        (experiment.apexAngle.toReal -
          Real.arcsin
            (experiment.refractiveIndex .air beam /
                experiment.refractiveIndex .silicateFlintGlass beam *
              Real.Angle.sin experiment.entryIncidenceToNormal)))

/--
For both wavelength components, the two Snell-law refractions through the
shown equilateral prism determine the exit-normal angle by the symbolic
forward model above.  The recorded numerical answer is intentionally not a
conclusion: without a source-grounded dispersion table, neither refractive
index, and hence neither numerical exit angle, is determined by the source.

Blueprint: `thm:physics:phyx_mini_0150:target`.
-/
theorem both_exit_angles_from_normal
    (experiment : PrismExperiment)
    (h_readouts : HasStatedReadouts experiment)
    (h_ray_laws : ∀ beam, SatisfiesPrismRayLaws experiment beam)
    (h_exit_labels : MatchesShownExitLabels experiment) :
    (experiment.shownExitAngleToNormal .thetaOne).toReal =
        snellPredictedEmergenceRadians experiment .lambdaOne455nm ∧
      (experiment.shownExitAngleToNormal .thetaTwo).toReal =
        snellPredictedEmergenceRadians experiment .lambdaTwo642nm := by
  have forward_model (beam : BeamLabel) :
      (experiment.rayAngles beam).emergenceToNormal.toReal =
        snellPredictedEmergenceRadians experiment beam := by
    have h_laws := h_ray_laws beam
    have h_air_ne :
        experiment.refractiveIndex .air beam ≠ 0 :=
      ne_of_gt h_laws.air_index_positive
    have h_glass_ne :
        experiment.refractiveIndex .silicateFlintGlass beam ≠ 0 :=
      ne_of_gt h_laws.glass_index_positive
    have h_entry_ratio :
        experiment.refractiveIndex .air beam /
              experiment.refractiveIndex .silicateFlintGlass beam *
            Real.Angle.sin experiment.entryIncidenceToNormal =
          Real.Angle.sin
            (experiment.rayAngles beam).firstRefractionToNormal := by
      calc
        experiment.refractiveIndex .air beam /
                experiment.refractiveIndex .silicateFlintGlass beam *
              Real.Angle.sin experiment.entryIncidenceToNormal =
            (experiment.refractiveIndex .air beam *
                Real.Angle.sin experiment.entryIncidenceToNormal) /
              experiment.refractiveIndex .silicateFlintGlass beam := by
                ring
        _ = (experiment.refractiveIndex .silicateFlintGlass beam *
                Real.Angle.sin
                  (experiment.rayAngles beam).firstRefractionToNormal) /
              experiment.refractiveIndex .silicateFlintGlass beam := by
                rw [h_laws.snell_at_entry]
        _ = Real.Angle.sin
              (experiment.rayAngles beam).firstRefractionToNormal := by
                field_simp
    have h_entry_arcsin :
        Real.arcsin
            (experiment.refractiveIndex .air beam /
                experiment.refractiveIndex .silicateFlintGlass beam *
              Real.Angle.sin experiment.entryIncidenceToNormal) =
          (experiment.rayAngles beam).firstRefractionToNormal.toReal := by
      rw [h_entry_ratio, ← Real.Angle.sin_toReal]
      apply Real.arcsin_sin
      · nlinarith
          [h_laws.first_refraction_physical.1, Real.pi_pos]
      · exact h_laws.first_refraction_physical.2
    have h_sum_toReal :
        ((experiment.rayAngles beam).firstRefractionToNormal +
            (experiment.rayAngles beam).secondIncidenceToNormal).toReal =
          (experiment.rayAngles beam).firstRefractionToNormal.toReal +
            (experiment.rayAngles beam).secondIncidenceToNormal.toReal := by
      calc
        ((experiment.rayAngles beam).firstRefractionToNormal +
              (experiment.rayAngles beam).secondIncidenceToNormal).toReal =
            ((((experiment.rayAngles beam).firstRefractionToNormal.toReal :
                  Real.Angle) +
                ((experiment.rayAngles beam).secondIncidenceToNormal.toReal :
                  Real.Angle))).toReal := by
                    rw [Real.Angle.coe_toReal, Real.Angle.coe_toReal]
        _ = ((((experiment.rayAngles beam).firstRefractionToNormal.toReal +
                (experiment.rayAngles beam).secondIncidenceToNormal.toReal :
                  ℝ) : Real.Angle)).toReal := by
                    rfl
        _ = (experiment.rayAngles beam).firstRefractionToNormal.toReal +
              (experiment.rayAngles beam).secondIncidenceToNormal.toReal := by
                apply Real.Angle.toReal_coe_eq_self_iff.mpr
                constructor <;>
                  nlinarith
                    [h_laws.first_refraction_physical.1,
                      h_laws.first_refraction_physical.2,
                      h_laws.second_incidence_physical.1,
                      h_laws.second_incidence_physical.2,
                      Real.pi_pos]
    have h_prism_geometry :
        experiment.apexAngle.toReal -
            (experiment.rayAngles beam).firstRefractionToNormal.toReal =
          (experiment.rayAngles beam).secondIncidenceToNormal.toReal := by
      have h_geometry_real :=
        congrArg Real.Angle.toReal h_laws.equilateral_prism_geometry
      rw [h_sum_toReal] at h_geometry_real
      linarith
    have h_exit_ratio :
        experiment.refractiveIndex .silicateFlintGlass beam /
              experiment.refractiveIndex .air beam *
            Real.Angle.sin
              (experiment.rayAngles beam).secondIncidenceToNormal =
          Real.Angle.sin (experiment.rayAngles beam).emergenceToNormal := by
      calc
        experiment.refractiveIndex .silicateFlintGlass beam /
                experiment.refractiveIndex .air beam *
              Real.Angle.sin
                (experiment.rayAngles beam).secondIncidenceToNormal =
            (experiment.refractiveIndex .silicateFlintGlass beam *
                Real.Angle.sin
                  (experiment.rayAngles beam).secondIncidenceToNormal) /
              experiment.refractiveIndex .air beam := by
                ring
        _ = (experiment.refractiveIndex .air beam *
                Real.Angle.sin
                  (experiment.rayAngles beam).emergenceToNormal) /
              experiment.refractiveIndex .air beam := by
                rw [h_laws.snell_at_exit]
        _ = Real.Angle.sin
              (experiment.rayAngles beam).emergenceToNormal := by
                field_simp
    rw [snellPredictedEmergenceRadians, h_entry_arcsin, h_prism_geometry,
      Real.Angle.sin_toReal, h_exit_ratio, ← Real.Angle.sin_toReal]
    symm
    apply Real.arcsin_sin
    · nlinarith [h_laws.emergence_physical.1, Real.pi_pos]
    · exact h_laws.emergence_physical.2
  constructor
  · exact
      (congrArg Real.Angle.toReal
          h_exit_labels.theta_one_is_lambda_one).trans
        (forward_model .lambdaOne455nm)
  · exact
      (congrArg Real.Angle.toReal
          h_exit_labels.theta_two_is_lambda_two).trans
        (forward_model .lambdaTwo642nm)

end PhyXMiniProblems.ProblemPhyXMini0150

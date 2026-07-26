import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.Units.WithDim.Basic

/-!
# Small-angle period of a uniform rod carrying a uniform disk

A uniform rod is pivoted at its upper end and attached at its lower end to the
rim of a uniform disk.  The primary figure labels the pivot-to-rim rod length
by `L` and the rim-to-center disk radius by `r`.  Those segments are collinear,
so the disk center is a distance `L + r` below the pivot.

The displayed value is the zero-amplitude, tangent-linearized period.  It is
not asserted to be the exact period at every finite amplitude.  The model
therefore records the exact sinusoidal restoring torque, its derivative and
little-o remainder at the stable equilibrium, and convergence of nonlinear
periods to the linearized period as the peak angle tends to zero.

Dimensionful physical quantities use Physlib.  Real numbers occur only as
coherent SI readouts, signed angles in radians, an angular-frequency readout,
and displayed numerical values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0262

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A moment of inertia about an axis, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/--
The nonnegative coefficient `κ` in the exact gravitational restoring torque
`τ(θ) = -κ sin θ`.  Radian measure is dimensionless, so `κ` has dimension
`M L² T⁻²`.
-/
abbrev RestoringTorqueCoefficientQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A signed torque, with dimension `M L² T⁻²`. -/
abbrev TorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical duration in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in kilogram meter squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a restoring-torque coefficient in newton meters. -/
def restoringCoefficientInNewtonMeters
    (coefficient : RestoringTorqueCoefficientQuantity) : ℝ :=
  ((coefficient UnitChoices.SI).val : ℝ)

/-- Read a signed torque in newton meters. -/
def torqueInNewtonMeters (torque : TorqueQuantity) : ℝ :=
  (torque UnitChoices.SI).val

/-! ## Physical roles and primary-figure labels -/

/-- The two massive components of the compound pendulum. -/
inductive PendulumComponent where
  | uniformRod
  | uniformDisk
  deriving DecidableEq, Repr

/-- Distinguished locations used by the dimension arrows in the image. -/
inductive FigurePoint where
  | fixedPivot
  | rodLowerEndAtDiskRim
  | diskCenter
  deriving DecidableEq, Repr

/-- The two mathematical labels printed in the primary image. -/
inductive FigureLabel where
  | rodLengthL
  | diskRadiusR
  deriving DecidableEq, Repr

/-- Idealized mass distribution of the rod. -/
inductive RodMassDistribution where
  | uniformSlenderRod
  deriving DecidableEq, Repr

/-- Idealized mass distribution of the wheel-like body. -/
inductive DiskMassDistribution where
  | uniformThinDisk
  deriving DecidableEq, Repr

/-- How the lower end of the rod is joined to the disk. -/
inductive RodDiskAttachment where
  | atDiskRimAlongRadius
  deriving DecidableEq, Repr

/-- Qualitative evidence and dimension endpoints visible in the image. -/
structure CompoundPendulumFigure where
  showsFixedSupport : Bool
  showsPivot : Bool
  showsRod : Bool
  showsDisk : Bool
  showsDiskCenterPoint : Bool
  rodMeetsDiskAtRim : Bool
  rodAxisPassesThroughDiskCenter : Bool
  rodLengthLabel : FigureLabel
  diskRadiusLabel : FigureLabel
  rodLengthDimensionStart : FigurePoint
  rodLengthDimensionEnd : FigurePoint
  diskRadiusDimensionStart : FigurePoint
  diskRadiusDimensionEnd : FigurePoint

/-!
Physical quantities for the rod--disk compound pendulum.  The nonlinear
period function and its tangent-linearized zero-amplitude limit are distinct
fields.  Neither is defined using a displayed answer.
-/
structure RodDiskPendulumSetup where
  figure : CompoundPendulumFigure
  componentMass : PendulumComponent → MassQuantity
  rodLength_L : LengthQuantity
  diskRadius_r : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  rodCenterOfMassDistanceBelowPivot : LengthQuantity
  diskCenterDistanceBelowPivot : LengthQuantity
  rodMomentOfInertiaAboutPivot : MomentOfInertiaQuantity
  diskMomentOfInertiaAboutCenter : MomentOfInertiaQuantity
  diskMomentOfInertiaAboutPivot : MomentOfInertiaQuantity
  totalMomentOfInertiaAboutPivot : MomentOfInertiaQuantity
  gravitationalRestoringCoefficient : RestoringTorqueCoefficientQuantity
  gravitationalRestoringTorque : ℝ → TorqueQuantity
  nonlinearOscillationPeriodAtPeakAngleRadians : ℝ → TimeQuantity
  linearizedAngularFrequencyRadiansPerSecond : ℝ
  linearizedSmallOscillationPeriod : TimeQuantity
  rodMassDistribution : RodMassDistribution
  diskMassDistribution : DiskMassDistribution
  attachment : RodDiskAttachment

/-! ## Figure/data readouts -/

/-!
Primary-image readout.  The `L` arrow runs from the fixed pivot to the
rod--disk rim attachment, while the `r` arrow continues from that rim point
to the disk center.  The resulting lever arm `L + r` is geometry, not the
requested period.
-/
structure MatchesPrimaryRodDiskFigure (setup : RodDiskPendulumSetup) : Prop where
  fixedSupportVisible : setup.figure.showsFixedSupport = true
  pivotVisible : setup.figure.showsPivot = true
  rodVisible : setup.figure.showsRod = true
  diskVisible : setup.figure.showsDisk = true
  diskCenterPointVisible : setup.figure.showsDiskCenterPoint = true
  rimAttachmentVisible : setup.figure.rodMeetsDiskAtRim = true
  radialAlignmentVisible : setup.figure.rodAxisPassesThroughDiskCenter = true
  rodLengthLabelIsL : setup.figure.rodLengthLabel = .rodLengthL
  diskRadiusLabelIsR : setup.figure.diskRadiusLabel = .diskRadiusR
  rodLengthStartsAtPivot :
    setup.figure.rodLengthDimensionStart = .fixedPivot
  rodLengthEndsAtRim :
    setup.figure.rodLengthDimensionEnd = .rodLowerEndAtDiskRim
  diskRadiusStartsAtRim :
    setup.figure.diskRadiusDimensionStart = .rodLowerEndAtDiskRim
  diskRadiusEndsAtCenter :
    setup.figure.diskRadiusDimensionEnd = .diskCenter
  rimAttachmentModel : setup.attachment = .atDiskRimAlongRadius
  diskCenterLeverArmGeometry :
    lengthInMeters setup.diskCenterDistanceBelowPivot =
      lengthInMeters setup.rodLength_L +
        lengthInMeters setup.diskRadius_r

/-!
Numerical and qualitative data supplied by the problem.  Centimeters,
millimeters, and grams are converted to coherent SI readouts.  The standard
value `9.81 m/s²` is the environmental datum used to compare the displayed
choices.
-/
structure HasRodDiskPendulumProblemData (setup : RodDiskPendulumSetup) : Prop where
  rodLengthMeters : lengthInMeters setup.rodLength_L = 1 / 2
  diskRadiusMeters : lengthInMeters setup.diskRadius_r = 1 / 10
  rodMassKilograms :
    massInKilograms (setup.componentMass .uniformRod) = 27 / 100
  diskMassKilograms :
    massInKilograms (setup.componentMass .uniformDisk) = 1 / 2
  gravitationalAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude = 981 / 100
  rodIsUniform : setup.rodMassDistribution = .uniformSlenderRod
  diskIsUniform : setup.diskMassDistribution = .uniformThinDisk

/-! ## Exact nonlinear and tangent-linearized governing laws -/

/-!
Rigid-body, gravitational, and local small-oscillation relations.  The rod
has pivot inertia `m L² / 3`.  The disk has central inertia `m r² / 2`, and
the parallel-axis theorem translates it through `d = L + r`.  The exact
signed gravitational torque is `-κ sin θ`.

The `HasDerivAt` and little-o fields make the replacement of that torque by
`-κ θ` explicitly local at the stable equilibrium.  The frequency and period
laws refer only to the tangent-linearized oscillator.  The final field relates
the nonlinear periods to it by a zero-amplitude limit, rather than asserting
an exact amplitude-independent nonlinear period.
-/
structure SatisfiesRodDiskCompoundPendulumLaws
    (setup : RodDiskPendulumSetup) : Prop where
  rodCenterOfMassLeverArm :
    lengthInMeters setup.rodCenterOfMassDistanceBelowPivot =
      lengthInMeters setup.rodLength_L / 2
  uniformRodPivotInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.rodMomentOfInertiaAboutPivot =
      massInKilograms (setup.componentMass .uniformRod) *
        (lengthInMeters setup.rodLength_L) ^ 2 / 3
  uniformDiskCentralInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.diskMomentOfInertiaAboutCenter =
      massInKilograms (setup.componentMass .uniformDisk) *
        (lengthInMeters setup.diskRadius_r) ^ 2 / 2
  parallelAxisLawForDisk :
    momentOfInertiaInKilogramMetersSquared
        setup.diskMomentOfInertiaAboutPivot =
      momentOfInertiaInKilogramMetersSquared
          setup.diskMomentOfInertiaAboutCenter +
        massInKilograms (setup.componentMass .uniformDisk) *
          (lengthInMeters setup.diskCenterDistanceBelowPivot) ^ 2
  totalInertiaIsComponentSum :
    momentOfInertiaInKilogramMetersSquared
        setup.totalMomentOfInertiaAboutPivot =
      momentOfInertiaInKilogramMetersSquared
          setup.rodMomentOfInertiaAboutPivot +
        momentOfInertiaInKilogramMetersSquared
          setup.diskMomentOfInertiaAboutPivot
  gravitationalRestoringCoefficientLaw :
    restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient =
      accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude *
        (massInKilograms (setup.componentMass .uniformRod) *
            lengthInMeters setup.rodCenterOfMassDistanceBelowPivot +
          massInKilograms (setup.componentMass .uniformDisk) *
            lengthInMeters setup.diskCenterDistanceBelowPivot)
  exactNonlinearRestoringTorqueLaw :
    ∀ angleRadians : ℝ,
      torqueInNewtonMeters
          (setup.gravitationalRestoringTorque angleRadians) =
        -restoringCoefficientInNewtonMeters
            setup.gravitationalRestoringCoefficient *
          Real.sin angleRadians
  restoringTorqueHasDerivativeAtStableEquilibrium :
    HasDerivAt
      (fun angleRadians : ℝ =>
        torqueInNewtonMeters
          (setup.gravitationalRestoringTorque angleRadians))
      (-restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient)
      0
  restoringTorqueNonlinearRemainderIsLittleO :
    Asymptotics.IsLittleO (nhds 0)
      (fun angleRadians : ℝ =>
        torqueInNewtonMeters
            (setup.gravitationalRestoringTorque angleRadians) +
          restoringCoefficientInNewtonMeters
              setup.gravitationalRestoringCoefficient * angleRadians)
      (fun angleRadians : ℝ => angleRadians)
  linearizedAngularFrequencyPositive :
    0 < setup.linearizedAngularFrequencyRadiansPerSecond
  linearizedAngularFrequencySquaredLaw :
    setup.linearizedAngularFrequencyRadiansPerSecond ^ 2 =
      restoringCoefficientInNewtonMeters
          setup.gravitationalRestoringCoefficient /
        momentOfInertiaInKilogramMetersSquared
          setup.totalMomentOfInertiaAboutPivot
  linearizedPeriodFrequencyLaw :
    timeInSeconds setup.linearizedSmallOscillationPeriod =
      2 * Real.pi / setup.linearizedAngularFrequencyRadiansPerSecond
  nonlinearPeriodTendsToLinearizedPeriodAtZeroAmplitude :
    Filter.Tendsto
      (fun peakAngleRadians : ℝ =>
        timeInSeconds
          (setup.nonlinearOscillationPeriodAtPeakAngleRadians
            peakAngleRadians))
      (nhds 0)
      (nhds (timeInSeconds setup.linearizedSmallOscillationPeriod))

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed period choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The period in seconds printed beside each answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 1
  | .B => 6 / 5
  | .C => 3 / 2
  | .D => 9 / 5

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with an answer displayed to the nearest tenth of a second. -/
def MatchesDisplayedPeriod
    (period : TimeQuantity) (choice : AnswerChoice) : Prop :=
  |timeInSeconds period - choice.seconds| < 1 / 20

/-!
Eliminating the intermediate inertias and restoring coefficient gives the
zero-amplitude, tangent-linearized compound-pendulum period.  At the stated
data its value is about `1.498 s`, which rounds to `1.5 s`, answer C, and C is
a closest displayed choice.

No equality is claimed for a finite-amplitude nonlinear period; the local and
limiting relation is recorded in `SatisfiesRodDiskCompoundPendulumLaws`.
This formalizes `thm:physics:phyx_mini_0262:target`.
-/
theorem rodDiskLinearizedPeriod_matches_recordedAnswerC
    (setup : RodDiskPendulumSetup)
    (h_figure : MatchesPrimaryRodDiskFigure setup)
    (h_data : HasRodDiskPendulumProblemData setup)
    (h_laws : SatisfiesRodDiskCompoundPendulumLaws setup) :
    timeInSeconds setup.linearizedSmallOscillationPeriod =
        2 * Real.pi *
          Real.sqrt
            ((massInKilograms (setup.componentMass .uniformRod) *
                  (lengthInMeters setup.rodLength_L) ^ 2 / 3 +
                massInKilograms (setup.componentMass .uniformDisk) *
                  (lengthInMeters setup.diskRadius_r) ^ 2 / 2 +
                massInKilograms (setup.componentMass .uniformDisk) *
                  (lengthInMeters setup.rodLength_L +
                    lengthInMeters setup.diskRadius_r) ^ 2) /
              (accelerationInMetersPerSecondSquared
                  setup.gravitationalAccelerationMagnitude *
                (massInKilograms (setup.componentMass .uniformRod) *
                    (lengthInMeters setup.rodLength_L / 2) +
                  massInKilograms (setup.componentMass .uniformDisk) *
                    (lengthInMeters setup.rodLength_L +
                      lengthInMeters setup.diskRadius_r)))) ∧
      MatchesDisplayedPeriod
        setup.linearizedSmallOscillationPeriod recordedAnswerChoice ∧
      ∀ choice : AnswerChoice,
        |timeInSeconds setup.linearizedSmallOscillationPeriod -
            recordedAnswerChoice.seconds| ≤
          |timeInSeconds setup.linearizedSmallOscillationPeriod -
            choice.seconds| := by
  have h_diskCenter :
      lengthInMeters setup.diskCenterDistanceBelowPivot = (3 : ℝ) / 5 := by
    rw [h_figure.diskCenterLeverArmGeometry, h_data.rodLengthMeters,
      h_data.diskRadiusMeters]
    norm_num
  have h_rodCenter :
      lengthInMeters setup.rodCenterOfMassDistanceBelowPivot = (1 : ℝ) / 4 := by
    rw [h_laws.rodCenterOfMassLeverArm, h_data.rodLengthMeters]
    norm_num
  have h_rodInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.rodMomentOfInertiaAboutPivot = (9 : ℝ) / 400 := by
    rw [h_laws.uniformRodPivotInertia, h_data.rodMassKilograms,
      h_data.rodLengthMeters]
    norm_num
  have h_diskCentralInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.diskMomentOfInertiaAboutCenter = (1 : ℝ) / 400 := by
    rw [h_laws.uniformDiskCentralInertia, h_data.diskMassKilograms,
      h_data.diskRadiusMeters]
    norm_num
  have h_diskPivotInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.diskMomentOfInertiaAboutPivot = (73 : ℝ) / 400 := by
    rw [h_laws.parallelAxisLawForDisk, h_diskCentralInertia,
      h_data.diskMassKilograms, h_diskCenter]
    norm_num
  have h_totalInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.totalMomentOfInertiaAboutPivot = (41 : ℝ) / 200 := by
    rw [h_laws.totalInertiaIsComponentSum, h_rodInertia,
      h_diskPivotInertia]
    norm_num
  have h_restoringCoefficient :
      restoringCoefficientInNewtonMeters
          setup.gravitationalRestoringCoefficient =
        (144207 : ℝ) / 40000 := by
    rw [h_laws.gravitationalRestoringCoefficientLaw,
      h_data.gravitationalAccelerationMetersPerSecondSquared,
      h_data.rodMassKilograms, h_rodCenter, h_data.diskMassKilograms,
      h_diskCenter]
    norm_num
  have h_frequencySq :
      setup.linearizedAngularFrequencyRadiansPerSecond ^ 2 =
        (144207 : ℝ) / 8200 := by
    rw [h_laws.linearizedAngularFrequencySquaredLaw,
      h_restoringCoefficient, h_totalInertia]
    norm_num
  have h_frequency :
      setup.linearizedAngularFrequencyRadiansPerSecond =
        Real.sqrt ((144207 : ℝ) / 8200) := by
    calc
      setup.linearizedAngularFrequencyRadiansPerSecond =
          |setup.linearizedAngularFrequencyRadiansPerSecond| :=
        (abs_of_pos h_laws.linearizedAngularFrequencyPositive).symm
      _ = Real.sqrt
          (setup.linearizedAngularFrequencyRadiansPerSecond ^ 2) :=
        (Real.sqrt_sq_eq_abs
          setup.linearizedAngularFrequencyRadiansPerSecond).symm
      _ = Real.sqrt ((144207 : ℝ) / 8200) := by rw [h_frequencySq]
  have h_sqrtFrequency_pos :
      0 < Real.sqrt ((144207 : ℝ) / 8200) :=
    Real.sqrt_pos.2 (by norm_num)
  have h_reciprocalSqrtProduct :
      Real.sqrt ((144207 : ℝ) / 8200) *
          Real.sqrt ((8200 : ℝ) / 144207) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    norm_num
  have h_reciprocalSqrt :
      (Real.sqrt ((144207 : ℝ) / 8200))⁻¹ =
        Real.sqrt ((8200 : ℝ) / 144207) := by
    rw [← one_div]
    apply (div_eq_iff h_sqrtFrequency_pos.ne').2
    simp
  have h_period :
      timeInSeconds setup.linearizedSmallOscillationPeriod =
        2 * Real.pi * Real.sqrt ((8200 : ℝ) / 144207) := by
    calc
      timeInSeconds setup.linearizedSmallOscillationPeriod =
          2 * Real.pi /
            setup.linearizedAngularFrequencyRadiansPerSecond :=
        h_laws.linearizedPeriodFrequencyLaw
      _ = 2 * Real.pi / Real.sqrt ((144207 : ℝ) / 8200) := by
        rw [h_frequency]
      _ = 2 * Real.pi * Real.sqrt ((8200 : ℝ) / 144207) := by
        rw [div_eq_mul_inv, h_reciprocalSqrt]
  have h_sin_61_over_20_pos : 0 < Real.sin ((61 : ℝ) / 20) := by
    have h_sin_upper :
        Real.sin ((61 : ℝ) / 80) < (707 : ℝ) / 1000 := by
      have h_bound :=
        Real.sin_bound (x := (61 : ℝ) / 80) (by norm_num)
      have h_upper := (abs_le.mp h_bound).2
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 61 / 80)] at h_upper
      norm_num at h_upper ⊢
      linarith
    have h_sin_pos : 0 < Real.sin ((61 : ℝ) / 80) := by
      have h_bound :=
        Real.sin_bound (x := (61 : ℝ) / 80) (by norm_num)
      have h_lower := (abs_le.mp h_bound).1
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 61 / 80)] at h_lower
      norm_num at h_lower ⊢
      linarith
    have h_cos_pos : 0 < Real.cos ((61 : ℝ) / 80) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.two_le_pi]
    have h_sin_sq :
        Real.sin ((61 : ℝ) / 80) ^ 2 < (1 : ℝ) / 2 := by
      nlinarith
    have h_difference_pos :
        0 <
          Real.cos ((61 : ℝ) / 80) ^ 2 -
            Real.sin ((61 : ℝ) / 80) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq ((61 : ℝ) / 80)]
    rw [show (61 : ℝ) / 20 = 2 * (2 * (61 / 80)) by norm_num,
      Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul']
    positivity
  have h_pi_lower : (61 : ℝ) / 20 < Real.pi := by
    by_contra h
    have h_pi_le : Real.pi ≤ (61 : ℝ) / 20 := le_of_not_gt h
    have h_delta_nonneg : 0 ≤ (61 : ℝ) / 20 - Real.pi := by
      linarith
    have h_delta_le_pi : (61 : ℝ) / 20 - Real.pi ≤ Real.pi := by
      nlinarith [Real.two_le_pi]
    have h_sin_delta :=
      Real.sin_nonneg_of_nonneg_of_le_pi h_delta_nonneg h_delta_le_pi
    have h_sin_shift :
        Real.sin ((61 : ℝ) / 20) =
          -Real.sin ((61 : ℝ) / 20 - Real.pi) := by
      calc
        Real.sin ((61 : ℝ) / 20) =
            Real.sin (((61 : ℝ) / 20 - Real.pi) + Real.pi) := by
          congr 1
          ring
        _ = -Real.sin ((61 : ℝ) / 20 - Real.pi) :=
          Real.sin_add_pi _
    rw [h_sin_shift] at h_sin_61_over_20_pos
    linarith
  have h_cos_8_over_5_neg : Real.cos ((8 : ℝ) / 5) < 0 := by
    have h_sin_lower :
        (387 : ℝ) / 1000 < Real.sin ((2 : ℝ) / 5) := by
      have h_bound :=
        Real.sin_bound (x := (2 : ℝ) / 5) (by norm_num)
      have h_lower := (abs_le.mp h_bound).1
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5)] at h_lower
      norm_num at h_lower ⊢
      linarith
    have h_sin_upper :
        Real.sin ((2 : ℝ) / 5) < 2 / 5 := by
      have h_bound :=
        Real.sin_bound (x := (2 : ℝ) / 5) (by norm_num)
      have h_upper := (abs_le.mp h_bound).2
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5)] at h_upper
      norm_num at h_upper ⊢
      linarith
    have h_sin_pos : 0 < Real.sin ((2 : ℝ) / 5) := by
      linarith
    have h_cos_pos : 0 < Real.cos ((2 : ℝ) / 5) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.two_le_pi]
    have h_sin_sq_lower :
        ((387 : ℝ) / 1000) ^ 2 <
          Real.sin ((2 : ℝ) / 5) ^ 2 := by
      nlinarith
    have h_sin_sq_upper :
        Real.sin ((2 : ℝ) / 5) ^ 2 < ((2 : ℝ) / 5) ^ 2 := by
      nlinarith
    have h_cos_sq_lower :
        (21 : ℝ) / 25 < Real.cos ((2 : ℝ) / 5) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq ((2 : ℝ) / 5)]
    have h_product :
        (1 : ℝ) / 8 <
          Real.sin ((2 : ℝ) / 5) ^ 2 *
            Real.cos ((2 : ℝ) / 5) ^ 2 := by
      have h_product' :
          ((387 : ℝ) / 1000) ^ 2 * (21 / 25) <
            Real.sin ((2 : ℝ) / 5) ^ 2 *
              Real.cos ((2 : ℝ) / 5) ^ 2 :=
        mul_lt_mul h_sin_sq_lower h_cos_sq_lower.le
          (by positivity) (by positivity)
      norm_num at h_product' ⊢
      linarith
    have h_cos_formula :
        Real.cos ((8 : ℝ) / 5) =
          1 - 8 *
            (Real.sin ((2 : ℝ) / 5) ^ 2 *
              Real.cos ((2 : ℝ) / 5) ^ 2) := by
      rw [show (8 : ℝ) / 5 = 2 * (2 * (2 / 5)) by norm_num,
        Real.cos_two_mul', Real.cos_two_mul', Real.sin_two_mul]
      calc
        (Real.cos ((2 : ℝ) / 5) ^ 2 -
              Real.sin ((2 : ℝ) / 5) ^ 2) ^ 2 -
            (2 * Real.sin ((2 : ℝ) / 5) *
              Real.cos ((2 : ℝ) / 5)) ^ 2 =
            (Real.sin ((2 : ℝ) / 5) ^ 2 +
              Real.cos ((2 : ℝ) / 5) ^ 2) ^ 2 -
              8 * (Real.sin ((2 : ℝ) / 5) ^ 2 *
                Real.cos ((2 : ℝ) / 5) ^ 2) := by
          ring
        _ = 1 - 8 *
            (Real.sin ((2 : ℝ) / 5) ^ 2 *
              Real.cos ((2 : ℝ) / 5) ^ 2) := by
          rw [Real.sin_sq_add_cos_sq]
          norm_num
    rw [h_cos_formula]
    linarith
  have h_pi_upper : Real.pi < (16 : ℝ) / 5 := by
    by_contra h
    have h_le : (8 : ℝ) / 5 ≤ Real.pi / 2 := by
      nlinarith
    have h_nonneg :=
      Real.cos_nonneg_of_mem_Icc (x := (8 : ℝ) / 5)
        ⟨by nlinarith [Real.pi_pos], h_le⟩
    linarith
  have h_sqrt_lower :
      (119 : ℝ) / 500 <
        Real.sqrt ((8200 : ℝ) / 144207) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 119 / 500)]
    norm_num
  have h_sqrt_upper :
      Real.sqrt ((8200 : ℝ) / 144207) < (6 : ℝ) / 25 := by
    rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 8200 / 144207)
      (by norm_num : (0 : ℝ) ≤ 6 / 25)]
    norm_num
  have h_period_lower :
      (29 : ℝ) / 20 <
        timeInSeconds setup.linearizedSmallOscillationPeriod := by
    rw [h_period]
    have h_product :
        (61 : ℝ) / 20 * (119 / 500) <
          Real.pi * Real.sqrt ((8200 : ℝ) / 144207) :=
      mul_lt_mul h_pi_lower h_sqrt_lower.le
        (by positivity) (by positivity)
    norm_num at h_product ⊢
    linarith only [h_product]
  have h_period_upper :
      timeInSeconds setup.linearizedSmallOscillationPeriod <
        (31 : ℝ) / 20 := by
    rw [h_period]
    have h_product :
        Real.pi * Real.sqrt ((8200 : ℝ) / 144207) <
          (16 : ℝ) / 5 * (6 / 25) :=
      mul_lt_mul h_pi_upper h_sqrt_upper.le
        (by positivity) (by positivity)
    norm_num at h_product ⊢
    linarith only [h_product]
  have h_matches :
      MatchesDisplayedPeriod
        setup.linearizedSmallOscillationPeriod recordedAnswerChoice := by
    rw [MatchesDisplayedPeriod, recordedAnswerChoice, AnswerChoice.seconds,
      abs_lt]
    constructor <;> linarith only [h_period_lower, h_period_upper]
  · have h_closest :
        ∀ choice : AnswerChoice,
          |timeInSeconds setup.linearizedSmallOscillationPeriod -
              recordedAnswerChoice.seconds| ≤
            |timeInSeconds setup.linearizedSmallOscillationPeriod -
              choice.seconds| := by
      intro choice
      have h_recorded_error :
        |timeInSeconds setup.linearizedSmallOscillationPeriod -
              (3 : ℝ) / 2| < 1 / 20 := by
        rw [abs_lt]
        constructor <;> linarith only [h_period_lower, h_period_upper]
      cases choice with
      | A =>
          change
            |timeInSeconds setup.linearizedSmallOscillationPeriod - 3 / 2| ≤
              |timeInSeconds setup.linearizedSmallOscillationPeriod - 1|
          calc
            |timeInSeconds setup.linearizedSmallOscillationPeriod - 3 / 2| ≤
                1 / 20 := h_recorded_error.le
            _ ≤ timeInSeconds setup.linearizedSmallOscillationPeriod - 1 := by
              linarith only [h_period_lower]
            _ ≤ |timeInSeconds setup.linearizedSmallOscillationPeriod - 1| :=
              le_abs_self _
      | B =>
          change
            |timeInSeconds setup.linearizedSmallOscillationPeriod - 3 / 2| ≤
              |timeInSeconds setup.linearizedSmallOscillationPeriod - 6 / 5|
          calc
            |timeInSeconds setup.linearizedSmallOscillationPeriod - 3 / 2| ≤
                1 / 20 := h_recorded_error.le
            _ ≤ timeInSeconds setup.linearizedSmallOscillationPeriod - 6 / 5 := by
              linarith only [h_period_lower]
            _ ≤ |timeInSeconds setup.linearizedSmallOscillationPeriod - 6 / 5| :=
              le_abs_self _
      | C =>
          rfl
      | D =>
          change
            |timeInSeconds setup.linearizedSmallOscillationPeriod - 3 / 2| ≤
              |timeInSeconds setup.linearizedSmallOscillationPeriod - 9 / 5|
          calc
            |timeInSeconds setup.linearizedSmallOscillationPeriod - 3 / 2| ≤
                1 / 20 := h_recorded_error.le
            _ ≤ -(timeInSeconds setup.linearizedSmallOscillationPeriod - 9 / 5) := by
              linarith only [h_period_upper]
            _ ≤ |timeInSeconds setup.linearizedSmallOscillationPeriod - 9 / 5| :=
              neg_le_abs _
    refine ⟨?_, h_matches, h_closest⟩
    rw [h_data.rodMassKilograms, h_data.rodLengthMeters,
      h_data.diskMassKilograms, h_data.diskRadiusMeters,
      h_data.gravitationalAccelerationMetersPerSecondSquared]
    norm_num
    rw [← Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 8200)]
    exact h_period

end PhyXMiniProblems.ProblemPhyXMini0262

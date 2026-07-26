import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Refractive index from a two-beam arrival-time delay

A laser beam is split into two equal-power branches over the `2.50 m` length
shown in the figure. One branch runs immediately above the transparent block,
while the other traverses the block. Both branches terminate at the same
detector. Their measured arrival-time difference is `6.25 ns`.

Lengths, durations, and speeds are represented by Physlib dimensionful
quantities. Refractive index and beam-power fractions are dimensionless real
readouts.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0092

open Dimension

/-- A real-valued physical length, independent of the chosen unit readout. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A real-valued physical duration, independent of the chosen unit readout. -/
abbrev OpticalDuration : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A real-valued physical speed, independent of the chosen unit readout. -/
abbrev OpticalSpeed : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Unit choices in which duration readouts are measured in nanoseconds. -/
def nanosecondUnitChoices : UnitChoices :=
  { UnitChoices.SI with time := TimeUnit.nanoseconds }

/-- The two parallel branches drawn in the source figure. -/
inductive BeamBranch where
  /-- The branch that travels immediately above the block. -/
  | directAboveBlock
  /-- The branch that travels through the transparent material. -/
  | throughMaterial
  deriving DecidableEq, Repr

/-- Named locations appearing in the source figure and its geometry. -/
inductive FigureLandmark where
  | blockEntrance
  | blockExit
  | detector
  deriving DecidableEq, Repr

/--
The physical quantities associated with the split-beam timing experiment.

The functions indexed by `BeamBranch` keep the direct and in-material paths
distinct even though the figure gives them the same geometric length and the
same destination.
-/
structure LaserBlockDelaySetup where
  /-- Horizontal length of the transparent block, labeled `2.50 m`. -/
  blockLength : OpticalLength
  /-- Distance traveled by each branch from the block entrance line to the detector. -/
  pathLength : BeamBranch → OpticalLength
  /-- Elapsed propagation time of each branch. -/
  travelTime : BeamBranch → OpticalDuration
  /-- Propagation speed of each branch in its optical medium. -/
  propagationSpeed : BeamBranch → OpticalSpeed
  /-- Later arrival time minus earlier arrival time. -/
  arrivalDelay : OpticalDuration
  /-- Fraction of the incident beam power carried by each branch. -/
  beamPowerFraction : BeamBranch → ℝ
  /-- Figure endpoint of each branch. -/
  destination : BeamBranch → FigureLandmark
  /-- Dimensionless refractive index `n` of the transparent block. -/
  materialRefractiveIndex : ℝ

/-- Read a physical length as a real number of metres. -/
def lengthInMeters (length : OpticalLength) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical duration as a real number of seconds. -/
def durationInSeconds (duration : OpticalDuration) : ℝ :=
  (duration UnitChoices.SI).val

/-- Read a physical duration as a real number of nanoseconds. -/
def durationInNanoseconds (duration : OpticalDuration) : ℝ :=
  (duration nanosecondUnitChoices).val

/-- Read a physical speed as a real number of metres per second. -/
def speedInMetersPerSecond (speed : OpticalSpeed) : ℝ :=
  (speed UnitChoices.SI).val

/--
Problem-text and primary-figure readouts. Both branches span the block's
`2.50 m` horizontal extent, carry half of the beam, and end at the detector;
the in-material branch arrives `6.25 ns` later. No refractive-index value is
included here.
-/
def MatchesProblemAndFigure (setup : LaserBlockDelaySetup) : Prop :=
  lengthInMeters setup.blockLength = 5 / 2 ∧
    (∀ branch, lengthInMeters (setup.pathLength branch) =
      lengthInMeters setup.blockLength) ∧
    setup.beamPowerFraction .directAboveBlock = 1 / 2 ∧
    setup.beamPowerFraction .throughMaterial = 1 / 2 ∧
    setup.destination .directAboveBlock = .detector ∧
    setup.destination .throughMaterial = .detector ∧
    durationInNanoseconds setup.arrivalDelay = 25 / 4

/-- Positivity conditions for the physical quantities in the experiment. -/
def HasPhysicalParameters (setup : LaserBlockDelaySetup) : Prop :=
  0 < lengthInMeters setup.blockLength ∧
    (∀ branch, 0 < lengthInMeters (setup.pathLength branch)) ∧
    (∀ branch, 0 < speedInMetersPerSecond (setup.propagationSpeed branch)) ∧
    (∀ branch, 0 ≤ durationInSeconds (setup.travelTime branch)) ∧
    0 < durationInSeconds setup.arrivalDelay ∧
    0 < setup.materialRefractiveIndex

/--
Governing laws for the idealized two-branch timing model.

The direct branch propagates at Physlib's vacuum speed of light. In the block,
`v n = c`. Constant-speed kinematics gives `t v = L` on each branch, and the
last field identifies the measured delay with the difference in arrival times.
None of these laws assumes the requested numerical value of `n`.
-/
structure SatisfiesOpticalDelayLaws (setup : LaserBlockDelaySetup) : Prop where
  directBranchSpeed :
    speedInMetersPerSecond
        (setup.propagationSpeed .directAboveBlock) =
      speedInMetersPerSecond DimSpeed.speedOfLight
  speedInMaterial :
    speedInMetersPerSecond
        (setup.propagationSpeed .throughMaterial) *
        setup.materialRefractiveIndex =
      speedInMetersPerSecond DimSpeed.speedOfLight
  constantSpeedTravel : ∀ branch,
    durationInSeconds (setup.travelTime branch) *
        speedInMetersPerSecond (setup.propagationSpeed branch) =
      lengthInMeters (setup.pathLength branch)
  arrivalDelayRelation :
    durationInSeconds (setup.travelTime .throughMaterial) =
      durationInSeconds (setup.travelTime .directAboveBlock) +
        durationInSeconds setup.arrivalDelay

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless refractive-index readout printed beside each answer label. -/
def AnswerChoice.refractiveIndexReadout : AnswerChoice → ℝ
  | .A => 7 / 4
  | .B => 53 / 25
  | .C => 183 / 100
  | .D => 49 / 25

/-- Agreement with an index displayed to the nearest hundredth. -/
def MatchesAnswerChoice
    (actualIndex : ℝ) (choice : AnswerChoice) : Prop :=
  |actualIndex - choice.refractiveIndexReadout| ≤ 1 / 200

/--
The equal-path timing laws determine the material index by
`n = 1 + c Δt / L`, using SI scalar readouts of the dimensionful quantities.
-/
lemma refractiveIndex_eq_one_add_delay_ratio
    (setup : LaserBlockDelaySetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_laws : SatisfiesOpticalDelayLaws setup) :
    setup.materialRefractiveIndex =
      1 + speedInMetersPerSecond DimSpeed.speedOfLight *
        durationInSeconds setup.arrivalDelay /
          lengthInMeters setup.blockLength := by
  rcases h_physical with ⟨hL, hpaths, hspeeds, htimes, hdelay, hn⟩
  rcases h_figure with
    ⟨hLval, hpath, hpd, hpm, hdestd, hdestm, hdelay_ns⟩
  rcases h_laws with ⟨hsd, hsm, htravel, harrival⟩
  have hdirect := htravel BeamBranch.directAboveBlock
  have hmaterial := htravel BeamBranch.throughMaterial
  rw [hpath BeamBranch.directAboveBlock] at hdirect
  rw [hpath BeamBranch.throughMaterial] at hmaterial
  have hscaled :
      durationInSeconds (setup.travelTime .throughMaterial) *
          speedInMetersPerSecond DimSpeed.speedOfLight =
        lengthInMeters setup.blockLength *
          setup.materialRefractiveIndex := by
    calc
      _ = durationInSeconds (setup.travelTime .throughMaterial) *
            (speedInMetersPerSecond
                (setup.propagationSpeed .throughMaterial) *
              setup.materialRefractiveIndex) := by rw [hsm]
      _ = (durationInSeconds (setup.travelTime .throughMaterial) *
            speedInMetersPerSecond
              (setup.propagationSpeed .throughMaterial)) *
              setup.materialRefractiveIndex := by ring
      _ = _ := by rw [hmaterial]
  have hindex_scaled :
      lengthInMeters setup.blockLength *
          setup.materialRefractiveIndex =
        lengthInMeters setup.blockLength +
          speedInMetersPerSecond DimSpeed.speedOfLight *
            durationInSeconds setup.arrivalDelay := by
    calc
      _ = durationInSeconds (setup.travelTime .throughMaterial) *
            speedInMetersPerSecond DimSpeed.speedOfLight := hscaled.symm
      _ = (durationInSeconds (setup.travelTime .directAboveBlock) +
            durationInSeconds setup.arrivalDelay) *
              speedInMetersPerSecond DimSpeed.speedOfLight := by rw [harrival]
      _ = durationInSeconds (setup.travelTime .directAboveBlock) *
            speedInMetersPerSecond
              (setup.propagationSpeed .directAboveBlock) +
                speedInMetersPerSecond DimSpeed.speedOfLight *
                  durationInSeconds setup.arrivalDelay := by
            rw [hsd]
            ring
      _ = _ := by rw [hdirect]
  field_simp [ne_of_gt hL]
  nlinarith [hindex_scaled]

/-!
The `2.50 m` equal path lengths and `6.25 ns` delay give an index near `1.75`.
Using Physlib's exact vacuum light speed gives the unrounded expression below,
which agrees with displayed answer A to the nearest hundredth.

This formalizes `thm:physics:phyx_mini_0092:target`.
-/
theorem refractiveIndex_is_answer_A
    (setup : LaserBlockDelaySetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_laws : SatisfiesOpticalDelayLaws setup) :
    setup.materialRefractiveIndex =
        1 + speedInMetersPerSecond DimSpeed.speedOfLight *
          durationInSeconds setup.arrivalDelay /
            lengthInMeters setup.blockLength ∧
      MatchesAnswerChoice setup.materialRefractiveIndex .A := by
  have h_index :=
    refractiveIndex_eq_one_add_delay_ratio setup h_physical h_figure h_laws
  constructor
  · exact h_index
  · rcases h_figure with
      ⟨h_length, h_paths, hpowd, hpowm, hdestd, hdestm, h_delay_ns⟩
    have h_conversion :
        durationInNanoseconds setup.arrivalDelay =
          1000000000 * durationInSeconds setup.arrivalDelay := by
      have h_units_val := congrArg WithDim.val
        (setup.arrivalDelay.2 UnitChoices.SI nanosecondUnitChoices)
      convert h_units_val using 1 <;>
        norm_num [durationInNanoseconds, durationInSeconds,
          nanosecondUnitChoices, UnitChoices.dimScale,
          TimeUnit.nanoseconds, TimeUnit.seconds, TimeUnit.scale,
          TimeUnit.div_eq_val, NNReal.smul_def]
      exact Or.inl rfl
    have h_delay_seconds :
        durationInSeconds setup.arrivalDelay = 1 / 160000000 := by
      nlinarith [h_conversion, h_delay_ns]
    rw [h_index, h_length, h_delay_seconds]
    norm_num [MatchesAnswerChoice, AnswerChoice.refractiveIndexReadout,
      speedInMetersPerSecond]

end PhyXMiniProblems.ProblemPhyXMini0092

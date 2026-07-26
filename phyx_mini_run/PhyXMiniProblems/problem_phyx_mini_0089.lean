import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Phase difference produced by a variable-index slab

This file formalizes problem `phyx_mini_0089`. Two initially in-phase light
rays of common air wavelength `λ` follow the depicted mirror paths to point
`P` on a screen. Ray 2 alone traverses a slab of length `L` whose refractive
index `n` can be varied. The common wavelength, slab length, air-path lengths,
and optical path difference are dimensionful physical lengths. Refractive
indices and the phase difference measured in wavelength cycles are
dimensionless real numbers; intensities are scalar instrument readouts in one
fixed but otherwise unspecified intensity unit.

The supplied image contains the apparatus but not the intensity-versus-index
plot mentioned in the text. `MatchesStatedAndGraphReadouts` makes the fringe
readout needed by the recorded answer explicit, separately from the governing
optical laws and from the target at `n = 2`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0089

open Dimension

/-! ## Dimensionful quantities and figure labels -/

/-- A signed physical length, represented independently of a choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar readout of a dimensionful length in a chosen system of units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  (length units).val

/-- The two coherent rays labelled in the optical diagram. -/
inductive RayLabel where
  | rayOne
  | rayTwo
  deriving DecidableEq, Repr

/-- The two reflecting elements that redirect the rays toward the screen. -/
inductive MirrorLabel where
  | rayOneMirror
  | rayTwoMirror
  deriving DecidableEq, Repr

/-- The common observation point labelled `P` on the screen. -/
inductive ScreenPoint where
  | P
  deriving DecidableEq, Repr

/-!
The physical quantities and measured functions in the depicted experiment.

`phaseDifferenceInWavelengthsAtP n` is the signed phase difference expressed
as an optical path difference divided by the common air wavelength. Thus one
unit of this scalar is one full wavelength cycle (equivalently `2π` radians).
-/
structure VariableIndexInterferometer where
  /-- Common wavelength `λ` of the two rays in air. -/
  airWavelength : LengthQuantity
  /-- Physical length `L` of the variable-index slab traversed by ray 2. -/
  materialLength : LengthQuantity
  /--
  Geometric source-to-`P` path length for each ray, with the slab region
  counterfactually filled by ambient air.
  -/
  ambientBaselinePathLength : RayLabel → LengthQuantity
  /-- Dimensionless refractive index of the surrounding air. -/
  ambientAirRefractiveIndex : ℝ
  /-- Lowest refractive-index setting available in the experiment. -/
  scanIndexLower : ℝ
  /-- Highest refractive-index setting available in the experiment. -/
  scanIndexUpper : ℝ
  /-- Upper endpoint `n_s` of the displayed intensity graph. -/
  graphedIndexUpper : ℝ
  /-- Initial phase of each ray, as a radian readout. -/
  initialPhaseRadians : RayLabel → ℝ
  /-- Phase shift contributed by the mirror on each ray, in radians. -/
  mirrorPhaseShiftRadians : RayLabel → ℝ
  /-- Mirror associated to each labelled ray in the figure. -/
  reflectionMirror : RayLabel → MirrorLabel
  /-- Whether a labelled ray traverses the variable-index slab. -/
  passesThroughMaterial : RayLabel → Prop
  /-- Screen point reached by each ray after reflection. -/
  arrivalPoint : RayLabel → ScreenPoint
  /-- Signed optical path difference, ray 2 minus ray 1, at index setting `n`. -/
  opticalPathDifferenceAtP : ℝ → LengthQuantity
  /-- Signed phase difference at `P`, measured in wavelength cycles. -/
  phaseDifferenceInWavelengthsAtP : ℝ → ℝ
  /-- Intensity of either ray alone at `P`, in a fixed instrument unit. -/
  singleRayIntensityReadoutAtP : RayLabel → ℝ
  /-- Combined intensity at `P` as a function of the slab index setting. -/
  combinedIntensityReadoutAtP : ℝ → ℝ

/-! ## Assumptions: layout, readouts, and governing laws -/

/-!
Categorical and geometrical information read from the apparatus figure. The
rays begin in phase, acquire equal mirror phase shifts, have equal baseline
geometric path lengths, and meet at `P`; only ray 2 traverses the slab.
-/
structure HasDepictedCoherentLayout
    (setup : VariableIndexInterferometer) : Prop where
  rayOneMirror : setup.reflectionMirror .rayOne = .rayOneMirror
  rayTwoMirror : setup.reflectionMirror .rayTwo = .rayTwoMirror
  rayOneAvoidsMaterial : ¬ setup.passesThroughMaterial .rayOne
  rayTwoTraversesMaterial : setup.passesThroughMaterial .rayTwo
  rayOneArrivesAtP : setup.arrivalPoint .rayOne = .P
  rayTwoArrivesAtP : setup.arrivalPoint .rayTwo = .P
  initiallyInPhase :
    setup.initialPhaseRadians .rayOne = setup.initialPhaseRadians .rayTwo
  equalReflectionPhaseShifts :
    setup.mirrorPhaseShiftRadians .rayOne =
      setup.mirrorPhaseShiftRadians .rayTwo
  equalAmbientBaselinePaths :
    ∀ units : UnitChoices,
      lengthReadout units (setup.ambientBaselinePathLength .rayOne) =
        lengthReadout units (setup.ambientBaselinePathLength .rayTwo)

/-!
Positivity and ordering conditions for the physical experiment. These
conditions constrain the available scan and the measured quantities but do
not assign the target phase difference at `n = 2`.
-/
structure HasPhysicalOpticalParameters
    (setup : VariableIndexInterferometer) : Prop where
  wavelengthPositive :
    ∀ units : UnitChoices, 0 < lengthReadout units setup.airWavelength
  materialLengthPositive :
    ∀ units : UnitChoices, 0 < lengthReadout units setup.materialLength
  baselinePathLengthsPositive :
    ∀ (units : UnitChoices) (ray : RayLabel),
      0 < lengthReadout units (setup.ambientBaselinePathLength ray)
  slabFitsRayTwoPath :
    ∀ units : UnitChoices,
      lengthReadout units setup.materialLength ≤
        lengthReadout units (setup.ambientBaselinePathLength .rayTwo)
  ambientIndexPositive : 0 < setup.ambientAirRefractiveIndex
  scanOrdered : setup.scanIndexLower < setup.graphedIndexUpper
  graphWithinScan : setup.graphedIndexUpper ≤ setup.scanIndexUpper
  singleRayIntensitiesPositive :
    ∀ ray : RayLabel, 0 < setup.singleRayIntensityReadoutAtP ray
  equalSingleRayIntensities :
    setup.singleRayIntensityReadoutAtP .rayOne =
      setup.singleRayIntensityReadoutAtP .rayTwo
  combinedIntensityNonnegative :
    ∀ n : ℝ, 0 ≤ setup.combinedIntensityReadoutAtP n

/-!
An index setting is the first dark fringe on the displayed scan when the
combined intensity is zero there and is strictly positive at every earlier
displayed setting. This is a predicate on the measured graph, not an optical
law and not the requested phase value at `n = 2`.
-/
def IsFirstDarkFringeOnDisplayedScan
    (setup : VariableIndexInterferometer) (darkIndex : ℝ) : Prop :=
  setup.scanIndexLower < darkIndex ∧
    darkIndex ≤ setup.graphedIndexUpper ∧
    setup.combinedIntensityReadoutAtP darkIndex = 0 ∧
    ∀ n : ℝ,
      setup.scanIndexLower ≤ n →
      n < darkIndex →
      0 < setup.combinedIntensityReadoutAtP n

/-!
Numerical data stated in the problem together with the intensity-graph
readout needed by the recorded answer: the index is tunable from `1.0` to
`2.5`, the displayed graph ends at `n_s = 1.5`, air has index one, and the
first displayed dark fringe occurs at `n = 1.4 = 7/5`.

The source image available to this project omits that graph; consequently the
`7/5` datum is isolated here so it can be corrected without changing either
the governing laws or the target theorem.
-/
structure MatchesStatedAndGraphReadouts
    (setup : VariableIndexInterferometer) : Prop where
  ambientAirIndex : setup.ambientAirRefractiveIndex = 1
  scanLowerIndex : setup.scanIndexLower = 1
  scanUpperIndex : setup.scanIndexUpper = (5 : ℝ) / 2
  graphedUpperIndex : setup.graphedIndexUpper = (3 : ℝ) / 2
  firstDarkFringeReadout :
    IsFirstDarkFringeOnDisplayedScan setup ((7 : ℝ) / 5)

/-!
Optical-path law for insertion of the slab. The ambient-baseline contribution
is `n_air` times the geometric route-length difference. Replacing a segment
of length `L` on ray 2 by index `n` then adds `(n - n_air)L`. The depicted
layout states that the baseline route-length difference vanishes.
-/
def SatisfiesOpticalPathDifferenceLaw
    (setup : VariableIndexInterferometer) : Prop :=
  ∀ (n : ℝ) (units : UnitChoices),
    lengthReadout units (setup.opticalPathDifferenceAtP n) =
      setup.ambientAirRefractiveIndex *
          (lengthReadout units (setup.ambientBaselinePathLength .rayTwo) -
            lengthReadout units (setup.ambientBaselinePathLength .rayOne)) +
        (n - setup.ambientAirRefractiveIndex) *
          lengthReadout units setup.materialLength

/-!
Total phase/path relation. The propagation contribution is `2π` times the
optical path difference divided by `λ`; the initial and reflection phase
differences are added explicitly. Multiplication through by `λ` avoids
dividing dimensionful quantities. The depicted equal-phase assumptions make
the two extra differences vanish, leaving the usual `δ/λ` relation.
Stating the equation in every unit system makes it independent of a selected
length unit.
-/
def SatisfiesPhaseDifferenceLaw
    (setup : VariableIndexInterferometer) : Prop :=
  ∀ (n : ℝ) (units : UnitChoices),
    (2 * Real.pi * setup.phaseDifferenceInWavelengthsAtP n -
        (setup.initialPhaseRadians .rayTwo -
          setup.initialPhaseRadians .rayOne) -
        (setup.mirrorPhaseShiftRadians .rayTwo -
          setup.mirrorPhaseShiftRadians .rayOne)) *
        lengthReadout units setup.airWavelength =
      2 * Real.pi *
        lengthReadout units (setup.opticalPathDifferenceAtP n)

/-!
Equal-intensity two-beam interference at `P`:
`I = 2 I₀ (1 + cos (2π δ/λ))`. Equal single-ray intensities are supplied by
`HasPhysicalOpticalParameters`; this law uses ray 1's readout as `I₀`.
-/
def SatisfiesTwoBeamInterferenceLaw
    (setup : VariableIndexInterferometer) : Prop :=
  ∀ n : ℝ,
    setup.combinedIntensityReadoutAtP n =
      2 * setup.singleRayIntensityReadoutAtP .rayOne *
        (1 + Real.cos
          (2 * Real.pi * setup.phaseDifferenceInWavelengthsAtP n))

/-! ## Derived relations and multiple-choice target -/

/-!
The first dark fringe after the in-phase setting has half a wavelength cycle
of phase difference. This is derived from the interference curve, positivity,
the first-fringe graph predicate, and the linear optical-path law; it is not a
field of any premise structure.
-/
lemma phaseDifference_at_firstDarkFringe
    (setup : VariableIndexInterferometer)
    (h_layout : HasDepictedCoherentLayout setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_readouts : MatchesStatedAndGraphReadouts setup)
    (h_path : SatisfiesOpticalPathDifferenceLaw setup)
    (h_phase : SatisfiesPhaseDifferenceLaw setup)
    (h_interference : SatisfiesTwoBeamInterferenceLaw setup) :
    setup.phaseDifferenceInWavelengthsAtP ((7 : ℝ) / 5) = (1 : ℝ) / 2 := by
  let units : UnitChoices := UnitChoices.SI
  let wavelength := lengthReadout units setup.airWavelength
  let materialLength := lengthReadout units setup.materialLength
  let phase := setup.phaseDifferenceInWavelengthsAtP
  have hwavelength : 0 < wavelength := h_physical.wavelengthPositive units
  have hmaterialLength : 0 < materialLength :=
    h_physical.materialLengthPositive units
  have hphase_path (n : ℝ) :
      phase n * wavelength = (n - 1) * materialLength := by
    have hoptical := h_path n units
    rw [h_readouts.ambientAirIndex,
      h_layout.equalAmbientBaselinePaths units] at hoptical
    norm_num at hoptical
    have hpropagation := h_phase n units
    rw [h_layout.initiallyInPhase, h_layout.equalReflectionPhaseShifts,
      hoptical] at hpropagation
    simp only [sub_self, sub_zero] at hpropagation
    change
      (2 * Real.pi * phase n) * wavelength =
        2 * Real.pi * ((n - 1) * materialLength)
      at hpropagation
    apply mul_left_cancel₀ (ne_of_gt Real.two_pi_pos)
    calc
      (2 * Real.pi) * (phase n * wavelength) =
          (2 * Real.pi * phase n) * wavelength := by ring
      _ = 2 * Real.pi * ((n - 1) * materialLength) := hpropagation
      _ = (2 * Real.pi) * ((n - 1) * materialLength) := by ring
  rcases h_readouts.firstDarkFringeReadout with
    ⟨_, _, hdarkIntensity, hpositiveBefore⟩
  have hcos :
      Real.cos (2 * Real.pi * phase ((7 : ℝ) / 5)) = -1 := by
    have hinterference := h_interference ((7 : ℝ) / 5)
    rw [hdarkIntensity] at hinterference
    have hsingle :=
      h_physical.singleRayIntensitiesPositive RayLabel.rayOne
    nlinarith
  have hdarkPhasePositive : 0 < phase ((7 : ℝ) / 5) := by
    have hdarkRelation := hphase_path ((7 : ℝ) / 5)
    have hpositiveProduct :
        0 < phase ((7 : ℝ) / 5) * wavelength := by
      rw [hdarkRelation]
      norm_num
      positivity
    exact pos_of_mul_pos_left hpositiveProduct (le_of_lt hwavelength)
  have hshiftedCos :
      Real.cos
          (2 * Real.pi * phase ((7 : ℝ) / 5) - Real.pi) = 1 := by
    rw [Real.cos_sub_pi, hcos]
    norm_num
  obtain ⟨k, hk⟩ :=
    (Real.cos_eq_one_iff
      (2 * Real.pi * phase ((7 : ℝ) / 5) - Real.pi)).mp hshiftedCos
  have hdarkPhase :
      phase ((7 : ℝ) / 5) = (k : ℝ) + (1 : ℝ) / 2 := by
    nlinarith [Real.pi_pos]
  have hkNonnegative : 0 ≤ k := by
    have hkLowerReal : (-1 : ℝ) < (k : ℝ) := by
      nlinarith [hdarkPhasePositive, hdarkPhase]
    have hkLower : (-1 : ℤ) < k := by exact_mod_cast hkLowerReal
    omega
  have hkZero : k = 0 := by
    by_contra hkNotZero
    have hkAtLeastOne : (1 : ℤ) ≤ k := by omega
    have hkAtLeastOneReal : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hkAtLeastOne
    have hdarkPhaseLarge :
        (3 : ℝ) / 2 ≤ phase ((7 : ℝ) / 5) := by
      nlinarith [hdarkPhase]
    let earlierIndex : ℝ :=
      1 + 1 / (5 * phase ((7 : ℝ) / 5))
    have hdenominatorPositive :
        0 < 5 * phase ((7 : ℝ) / 5) := by positivity
    have hearlierLower : (1 : ℝ) ≤ earlierIndex := by
      have hreciprocalPositive :
          0 < 1 / (5 * phase ((7 : ℝ) / 5)) :=
        one_div_pos.mpr hdenominatorPositive
      dsimp [earlierIndex]
      linarith
    have hreciprocalBound :
        1 / (5 * phase ((7 : ℝ) / 5)) < (2 : ℝ) / 5 := by
      rw [div_lt_iff₀ hdenominatorPositive]
      nlinarith
    have hearlierUpper : earlierIndex < (7 : ℝ) / 5 := by
      dsimp [earlierIndex]
      nlinarith
    have hmaterialFromDark :
        materialLength =
          (5 : ℝ) / 2 *
            phase ((7 : ℝ) / 5) * wavelength := by
      have hdarkRelation := hphase_path ((7 : ℝ) / 5)
      norm_num at hdarkRelation ⊢
      nlinarith
    have hearlierPhase : phase earlierIndex = (1 : ℝ) / 2 := by
      apply mul_right_cancel₀ (ne_of_gt hwavelength)
      calc
        phase earlierIndex * wavelength =
            (earlierIndex - 1) * materialLength :=
          hphase_path earlierIndex
        _ = (1 / (5 * phase ((7 : ℝ) / 5))) * materialLength := by
          dsimp [earlierIndex]
          ring
        _ = (1 / (5 * phase ((7 : ℝ) / 5))) *
            ((5 : ℝ) / 2 *
              phase ((7 : ℝ) / 5) * wavelength) := by
          rw [hmaterialFromDark]
        _ = ((1 : ℝ) / 2) * wavelength := by
          field_simp [ne_of_gt hdarkPhasePositive]
    have hearlierIntensityPositive :
        0 < setup.combinedIntensityReadoutAtP earlierIndex :=
      hpositiveBefore earlierIndex (by
        rw [h_readouts.scanLowerIndex]
        exact hearlierLower) hearlierUpper
    have hearlierPhase' :
        setup.phaseDifferenceInWavelengthsAtP earlierIndex =
          (1 : ℝ) / 2 := by
      simpa only [phase] using hearlierPhase
    have hearlierIntensityZero :
        setup.combinedIntensityReadoutAtP earlierIndex = 0 := by
      rw [h_interference earlierIndex, hearlierPhase']
      rw [show 2 * Real.pi * ((1 : ℝ) / 2) = Real.pi by ring,
        Real.cos_pi]
      ring
    exact (ne_of_gt hearlierIntensityPositive) hearlierIntensityZero
  have hdarkPhase' :
      setup.phaseDifferenceInWavelengthsAtP ((7 : ℝ) / 5) =
        (k : ℝ) + (1 : ℝ) / 2 := by
    simpa only [phase] using hdarkPhase
  rw [hdarkPhase', hkZero]
  norm_num

/-!
The graph calibration and the optical laws determine the slab length to be
`5/4` of the common air wavelength, expressed without dividing dimensionful
quantities.
-/
lemma materialLength_eq_fiveFourths_wavelength
    (setup : VariableIndexInterferometer)
    (h_layout : HasDepictedCoherentLayout setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_readouts : MatchesStatedAndGraphReadouts setup)
    (h_path : SatisfiesOpticalPathDifferenceLaw setup)
    (h_phase : SatisfiesPhaseDifferenceLaw setup)
    (h_interference : SatisfiesTwoBeamInterferenceLaw setup) :
    ∀ units : UnitChoices,
      lengthReadout units setup.materialLength =
        (5 : ℝ) / 4 * lengthReadout units setup.airWavelength := by
  intro units
  have hdarkPhase :=
    phaseDifference_at_firstDarkFringe setup h_layout h_physical h_readouts
      h_path h_phase h_interference
  have hoptical := h_path ((7 : ℝ) / 5) units
  rw [h_readouts.ambientAirIndex,
    h_layout.equalAmbientBaselinePaths units] at hoptical
  norm_num at hoptical
  have hpropagation := h_phase ((7 : ℝ) / 5) units
  rw [hdarkPhase, h_layout.initiallyInPhase,
    h_layout.equalReflectionPhaseShifts, hoptical] at hpropagation
  nlinarith [Real.pi_pos]

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The wavelength multiple printed beside each answer choice. -/
def AnswerChoice.wavelengthMultiple : AnswerChoice → ℝ
  | .A => (3 : ℝ) / 4
  | .B => (3 : ℝ) / 2
  | .C => (5 : ℝ) / 4
  | .D => (5 : ℝ) / 2

/-- Dataset metadata: the recorded answer label, never used as a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A choice is correct when its multiple equals the phase difference at `n = 2`. -/
def IsCorrectAnswer
    (setup : VariableIndexInterferometer) (choice : AnswerChoice) : Prop :=
  setup.phaseDifferenceInWavelengthsAtP 2 = choice.wavelengthMultiple

/-!
When the slab index is `n = 2.0`, the optical path (and hence phase)
difference at screen point `P` is `5/4` of the common air wavelength. This is
answer choice C, `1.25 λ`.

Blueprint: `thm:physics:phyx_mini_0089:target`.
-/
theorem problem_phyx_mini_0089
    (setup : VariableIndexInterferometer)
    (h_layout : HasDepictedCoherentLayout setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_readouts : MatchesStatedAndGraphReadouts setup)
    (h_path : SatisfiesOpticalPathDifferenceLaw setup)
    (h_phase : SatisfiesPhaseDifferenceLaw setup)
    (h_interference : SatisfiesTwoBeamInterferenceLaw setup) :
    setup.phaseDifferenceInWavelengthsAtP 2 = (5 : ℝ) / 4 ∧
      IsCorrectAnswer setup .C := by
  let units : UnitChoices := UnitChoices.SI
  let wavelength := lengthReadout units setup.airWavelength
  let materialLength := lengthReadout units setup.materialLength
  have hwavelength : 0 < wavelength := h_physical.wavelengthPositive units
  have hmaterialLength :
      materialLength = (5 : ℝ) / 4 * wavelength :=
    materialLength_eq_fiveFourths_wavelength setup h_layout h_physical
      h_readouts h_path h_phase h_interference units
  have hoptical := h_path 2 units
  rw [h_readouts.ambientAirIndex,
    h_layout.equalAmbientBaselinePaths units] at hoptical
  norm_num at hoptical
  have hpropagation := h_phase 2 units
  rw [h_layout.initiallyInPhase, h_layout.equalReflectionPhaseShifts,
    hoptical] at hpropagation
  have htarget :
      setup.phaseDifferenceInWavelengthsAtP 2 = (5 : ℝ) / 4 := by
    have hpropagation' :
        (2 * Real.pi * setup.phaseDifferenceInWavelengthsAtP 2) *
            lengthReadout units setup.airWavelength =
          2 * Real.pi * lengthReadout units setup.materialLength := by
      simpa only [sub_self, sub_zero] using hpropagation
    have hphaseTimesWavelength :
        setup.phaseDifferenceInWavelengthsAtP 2 *
            lengthReadout units setup.airWavelength =
          lengthReadout units setup.materialLength := by
      apply mul_left_cancel₀ (ne_of_gt Real.two_pi_pos)
      calc
        (2 * Real.pi) *
            (setup.phaseDifferenceInWavelengthsAtP 2 *
              lengthReadout units setup.airWavelength) =
            (2 * Real.pi * setup.phaseDifferenceInWavelengthsAtP 2) *
              lengthReadout units setup.airWavelength := by ring
        _ = 2 * Real.pi * lengthReadout units setup.materialLength :=
          hpropagation'
        _ = (2 * Real.pi) *
            lengthReadout units setup.materialLength := by ring
    apply mul_right_cancel₀ (ne_of_gt hwavelength)
    calc
      setup.phaseDifferenceInWavelengthsAtP 2 * wavelength =
          materialLength := hphaseTimesWavelength
      _ = (5 : ℝ) / 4 * wavelength := hmaterialLength
  constructor
  · exact htarget
  · simpa [IsCorrectAnswer, AnswerChoice.wavelengthMultiple] using htarget

end PhyXMiniProblems.ProblemPhyXMini0089

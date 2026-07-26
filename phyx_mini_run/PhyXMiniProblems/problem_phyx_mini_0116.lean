import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Basic

/-!
# Minimum pit depth for destructive reflection from a compact disc

The primary figure is modeled as a cross section of a compact disc read from
below.  Two branches of the same semiconductor-laser beam propagate through
the plastic substrate and reflect from the common reflective coating, one at
a pit floor and one at the neighboring flat land.  Their round-trip optical
path difference produces destructive interference.

Physical wavelengths, pit depths, and optical path differences are represented
by PhysLean dimensionful lengths.  Real numbers occur only as dimensionless
refractive indices, phase readouts, or scalar readouts in a named length unit.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0116

open CarriesDimension Dimension

/-- A signed physical length represented coherently in every unit system. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a scalar in the specified length unit. -/
def lengthValueIn (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The nanometre readout used for the laser wavelength. -/
def nanometersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- The micrometre readout used for the pit depth and displayed answers. -/
def micrometersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.micrometers length

/-- Construct a physical length from a scalar readout in a chosen length unit. -/
noncomputable def lengthFromReadout
    (unit : LengthUnit) (value : ℝ) : LengthQuantity :=
  toDimensionful ({ UnitChoices.SI with length := unit } : UnitChoices) ⟨value⟩

/-- Construct a physical length from its micrometre readout. -/
noncomputable def lengthInMicrometers (value : ℝ) : LengthQuantity :=
  lengthFromReadout LengthUnit.micrometers value

/-- The two portions of the reflected laser beam that interfere. -/
inductive ReflectedBranch where
  | fromPit
  | fromFlatRegion
  deriving DecidableEq, Repr

/-- Surface features distinguished in the compact-disc cross section. -/
inductive SurfaceFeature where
  | pitFloor
  | flatLand
  deriving DecidableEq, Repr

/-- Optical media through which a branch might propagate. -/
inductive OpticalMedium where
  | plasticSubstrate
  | exterior
  deriving DecidableEq, Repr

/-- Layers at which a branch might be reflected. -/
inductive ReflectingLayer where
  | reflectiveCoating
  | otherLayer
  deriving DecidableEq, Repr

/-- Directions singled out by the bottom-reading geometry in the figure. -/
inductive BeamDirection where
  | fromBottomTowardCoating
  | backTowardBottom
  deriving DecidableEq, Repr

/-
The physical quantities and labeled geometry of the compact-disc experiment.

`reflectionPhaseHalfTurns` measures the phase shift on reflection in integral
multiples of `π`.  `opticalPathDifferenceAtDepth` is the magnitude of the
round-trip optical path difference produced by a proposed pit depth.
-/
structure CompactDiscInterferenceSetup where
  /-- Vacuum wavelength of the semiconductor laser. -/
  laserVacuumWavelength : LengthQuantity
  /-- Dimensionless refractive index of each optical medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Physical depth of the depicted manufactured pit. -/
  pitDepth : LengthQuantity
  /-- Surface feature from which each branch reflects. -/
  reflectionSite : ReflectedBranch → SurfaceFeature
  /-- Medium traversed by each branch before and after reflection. -/
  propagationMedium : ReflectedBranch → OpticalMedium
  /-- Coating or layer from which each branch reflects. -/
  reflectionLayer : ReflectedBranch → ReflectingLayer
  /-- Incident direction of the bottom-reading laser beam. -/
  incidentDirection : BeamDirection
  /-- Direction of the reflected light returning toward the reader. -/
  returnDirection : BeamDirection
  /-- Incidence angle from the local surface normal, in radians. -/
  incidenceAngleFromNormalRadians : ReflectedBranch → ℝ
  /-- Reflection phase shift, in half-turns, of each branch. -/
  reflectionPhaseHalfTurns : ReflectedBranch → ℤ
  /-- Optical path difference caused by any proposed physical pit depth. -/
  opticalPathDifferenceAtDepth : LengthQuantity → LengthQuantity
  /-- Whether the two reflected branches cancel for a proposed pit depth. -/
  cancelsAtDepth : LengthQuantity → Prop

/-
Numerical and figure-derived data stated by the problem.

The unknown pit depth receives no numerical readout.  The final field records
only the observed cancellation at the depicted pit, not the requested minimum
depth or its answer choice.
-/
structure MatchesProblemAndFigure
    (setup : CompactDiscInterferenceSetup) : Prop where
  wavelength_nanometers : nanometersValue setup.laserVacuumWavelength = 790
  plastic_refractive_index :
    setup.refractiveIndex .plasticSubstrate = (9 : ℝ) / 5
  pit_branch_site : setup.reflectionSite .fromPit = .pitFloor
  flat_branch_site : setup.reflectionSite .fromFlatRegion = .flatLand
  pit_branch_in_plastic :
    setup.propagationMedium .fromPit = .plasticSubstrate
  flat_branch_in_plastic :
    setup.propagationMedium .fromFlatRegion = .plasticSubstrate
  pit_branch_reflects_from_coating :
    setup.reflectionLayer .fromPit = .reflectiveCoating
  flat_branch_reflects_from_coating :
    setup.reflectionLayer .fromFlatRegion = .reflectiveCoating
  beam_enters_from_bottom :
    setup.incidentDirection = .fromBottomTowardCoating
  reflected_beam_returns_downward :
    setup.returnDirection = .backTowardBottom
  pit_branch_normal_incidence :
    setup.incidenceAngleFromNormalRadians .fromPit = 0
  flat_branch_normal_incidence :
    setup.incidenceAngleFromNormalRadians .fromFlatRegion = 0
  depicted_pit_cancels : setup.cancelsAtDepth setup.pitDepth

/-- Positivity conditions selecting the physical branch of the model. -/
structure HasPhysicalParameters
    (setup : CompactDiscInterferenceSetup) : Prop where
  refractive_indices_positive :
    ∀ medium : OpticalMedium, 0 < setup.refractiveIndex medium
  wavelength_positive :
    ∀ units : UnitChoices, 0 < (setup.laserVacuumWavelength units).val
  depicted_pit_depth_nonnegative :
    ∀ units : UnitChoices, 0 ≤ (setup.pitDepth units).val

/-
The governing laws for normal-incidence interference of the two reflected
branches.

The path difference is the extra down-and-back optical distance `2 n d` in the
plastic.  Branches reflected by the same coating acquire the same reflection
phase shift.  Cancellation occurs exactly when propagation plus reflection
phase is an odd number of half-turns; the denominator-free equation is

`2 Δ + (h_pit - h_flat) λ₀ = (2 m + 1) λ₀`.

These laws quantify over every proposed nonnegative depth.  They do not fix a
pit depth or select an answer choice.
-/
structure SatisfiesNormalIncidenceInterferenceLaws
    (setup : CompactDiscInterferenceSetup) : Prop where
  round_trip_optical_path_law :
    ∀ (units : UnitChoices) (depth : LengthQuantity),
      0 ≤ (depth units).val →
        (setup.opticalPathDifferenceAtDepth depth units).val =
          2 * setup.refractiveIndex .plasticSubstrate * (depth units).val
  same_reflective_layer_same_phase :
    ∀ first second : ReflectedBranch,
      setup.reflectionLayer first = setup.reflectionLayer second →
        setup.reflectionPhaseHalfTurns first =
          setup.reflectionPhaseHalfTurns second
  destructive_interference_law :
    ∀ depth : LengthQuantity,
      0 ≤ micrometersValue depth →
        setup.cancelsAtDepth depth ↔
          ∃ order : ℕ,
            2 * micrometersValue
                  (setup.opticalPathDifferenceAtDepth depth) +
                ((setup.reflectionPhaseHalfTurns .fromPit -
                    setup.reflectionPhaseHalfTurns .fromFlatRegion : ℤ) : ℝ) *
                  micrometersValue setup.laserVacuumWavelength =
              (2 * (order : ℝ) + 1) *
                micrometersValue setup.laserVacuumWavelength

/-- The set of nonnegative physical pit depths that produce cancellation. -/
def DestructivePitDepths
    (setup : CompactDiscInterferenceSetup) : Set LengthQuantity :=
  {depth | 0 ≤ micrometersValue depth ∧ setup.cancelsAtDepth depth}

/--
`depth` is a least destructive pit depth when it cancels and its micrometre
readout is no larger than that of any other nonnegative cancelling depth.
PhysLean dimensionful quantities deliberately have no unit-independent global
order, so the comparison is made through one explicitly named length unit.
-/
def IsLeastDestructivePitDepth
    (setup : CompactDiscInterferenceSetup) (depth : LengthQuantity) : Prop :=
  depth ∈ DestructivePitDepths setup ∧
    ∀ other ∈ DestructivePitDepths setup,
      micrometersValue depth ≤ micrometersValue other

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The pit-depth readout, in micrometres, printed beside each answer label. -/
def AnswerChoice.depthMicrometers : AnswerChoice → ℝ
  | .A => 11 / 100
  | .B => 21 / 100
  | .C => 9 / 100
  | .D => 32 / 100

/-- A displayed answer is selected when it is uniquely closest to a readout. -/
def IsUniquelyClosestAnswer
    (actualDepthMicrometers : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualDepthMicrometers - choice.depthMicrometers| <
      |actualDepthMicrometers - other.depthMicrometers|

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-
The least nonnegative destructive-interference depth is

`790 nm / (4 · 1.8) = 79/720 µm`.

This is an intermediate consequence of the physical laws and readouts, not an
input field of any setup or law structure.
-/
lemma firstDestructivePitDepth_exact
    (setup : CompactDiscInterferenceSetup)
    (_data : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesNormalIncidenceInterferenceLaws setup) :
    IsLeastDestructivePitDepth setup
      (lengthInMicrometers ((79 : ℝ) / 720)) := by
  let uNano : UnitChoices :=
    { UnitChoices.SI with length := LengthUnit.nanometers }
  let uMicro : UnitChoices :=
    { UnitChoices.SI with length := LengthUnit.micrometers }
  have hCandidate :
      micrometersValue (lengthInMicrometers ((79 : ℝ) / 720)) =
        (79 : ℝ) / 720 := by
    simp [micrometersValue, lengthValueIn, lengthInMicrometers,
      lengthFromReadout, CarriesDimension.toDimensionful_apply_apply]
  have hCandidateNonnegative :
      0 ≤ micrometersValue (lengthInMicrometers ((79 : ℝ) / 720)) := by
    rw [hCandidate]
    norm_num
  have hWavelength :
      micrometersValue setup.laserVacuumWavelength = (79 : ℝ) / 100 := by
    have hScale := setup.laserVacuumWavelength.2 uNano uMicro
    have hScaleValues := congrArg WithDim.val hScale
    simp only [WithDim.smul_val, NNReal.smul_def] at hScaleValues
    have hNano := _data.wavelength_nanometers
    change (setup.laserVacuumWavelength uNano).val = 790 at hNano
    change (setup.laserVacuumWavelength uMicro).val = (79 : ℝ) / 100
    rw [hNano] at hScaleValues
    norm_num [UnitChoices.dimScale, uNano, uMicro,
      LengthUnit.nanometers, LengthUnit.micrometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.toReal] at hScaleValues ⊢
    exact hScaleValues
  have hSamePhase :
      setup.reflectionPhaseHalfTurns .fromPit =
        setup.reflectionPhaseHalfTurns .fromFlatRegion := by
    apply _laws.same_reflective_layer_same_phase
    rw [_data.pit_branch_reflects_from_coating,
      _data.flat_branch_reflects_from_coating]
  have hPhaseDifference :
      ((setup.reflectionPhaseHalfTurns .fromPit -
          setup.reflectionPhaseHalfTurns .fromFlatRegion : ℤ) : ℝ) = 0 := by
    rw [hSamePhase]
    simp
  have hCandidatePath :=
    _laws.round_trip_optical_path_law uMicro
      (lengthInMicrometers ((79 : ℝ) / 720))
      (by
        change 0 ≤
          micrometersValue (lengthInMicrometers ((79 : ℝ) / 720))
        exact hCandidateNonnegative)
  change
    micrometersValue
        (setup.opticalPathDifferenceAtDepth
          (lengthInMicrometers ((79 : ℝ) / 720))) =
      2 * setup.refractiveIndex .plasticSubstrate *
        micrometersValue (lengthInMicrometers ((79 : ℝ) / 720))
    at hCandidatePath
  rw [_data.plastic_refractive_index, hCandidate] at hCandidatePath
  have hCandidateCancels :
      setup.cancelsAtDepth
        (lengthInMicrometers ((79 : ℝ) / 720)) := by
    have hDestructiveLaw :=
      _laws.destructive_interference_law
        (depth := lengthInMicrometers ((79 : ℝ) / 720))
    have hExistsOrder : ∃ order : ℕ,
        2 * micrometersValue
              (setup.opticalPathDifferenceAtDepth
                (lengthInMicrometers ((79 : ℝ) / 720))) +
            ((setup.reflectionPhaseHalfTurns .fromPit -
                setup.reflectionPhaseHalfTurns .fromFlatRegion : ℤ) : ℝ) *
              micrometersValue setup.laserVacuumWavelength =
          (2 * (order : ℝ) + 1) *
            micrometersValue setup.laserVacuumWavelength := by
      refine ⟨0, ?_⟩
      rw [hCandidatePath, hPhaseDifference, hWavelength]
      norm_num
    exact (hDestructiveLaw.mpr hExistsOrder) hCandidateNonnegative
  constructor
  · exact ⟨hCandidateNonnegative, hCandidateCancels⟩
  · intro other hOther
    change
      0 ≤ micrometersValue other ∧ setup.cancelsAtDepth other
      at hOther
    rcases hOther with ⟨hOtherNonnegative, hOtherCancels⟩
    have hOtherPath :=
      _laws.round_trip_optical_path_law uMicro other
        (by
          change 0 ≤ micrometersValue other
          exact hOtherNonnegative)
    change
      micrometersValue (setup.opticalPathDifferenceAtDepth other) =
        2 * setup.refractiveIndex .plasticSubstrate *
          micrometersValue other
      at hOtherPath
    rw [_data.plastic_refractive_index] at hOtherPath
    have hDestructiveLaw :=
      _laws.destructive_interference_law (depth := other)
    obtain ⟨order, hOrder⟩ :=
      hDestructiveLaw.mp (fun _ => hOtherCancels)
    rw [hOtherPath, hPhaseDifference, hWavelength] at hOrder
    rw [hCandidate]
    have hOrderNonnegative : 0 ≤ (order : ℝ) := Nat.cast_nonneg order
    nlinarith

/-
The minimum depth is `79/720 µm ≈ 0.1097 µm`, uniquely closest to the
displayed `0.11 µm` (answer A).  Any depicted pit that cancels the flat-land
reflection is at least this deep.

This formalizes `thm:physics:phyx_mini_0116:target`.
-/
theorem minimumPitDepth_is_recordedAnswerA
    (setup : CompactDiscInterferenceSetup)
    (_data : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesNormalIncidenceInterferenceLaws setup) :
    IsLeastDestructivePitDepth setup
        (lengthInMicrometers ((79 : ℝ) / 720)) ∧
      IsUniquelyClosestAnswer ((79 : ℝ) / 720) recordedDatasetAnswer ∧
      (79 : ℝ) / 720 ≤ micrometersValue setup.pitDepth := by
  have hLeast :=
    firstDestructivePitDepth_exact setup _data _physical _laws
  have hClosest :
      IsUniquelyClosestAnswer ((79 : ℝ) / 720)
        recordedDatasetAnswer := by
    unfold IsUniquelyClosestAnswer recordedDatasetAnswer
    intro other hOther
    cases other with
    | A => exact (hOther rfl).elim
    | B =>
        simp only [AnswerChoice.depthMicrometers]
        rw [abs_of_neg (by norm_num), abs_of_neg (by norm_num)]
        norm_num
    | C =>
        simp only [AnswerChoice.depthMicrometers]
        rw [abs_of_neg (by norm_num), abs_of_pos (by norm_num)]
        norm_num
    | D =>
        simp only [AnswerChoice.depthMicrometers]
        rw [abs_of_neg (by norm_num), abs_of_neg (by norm_num)]
        norm_num
  have hPitNonnegative : 0 ≤ micrometersValue setup.pitDepth := by
    have hPhysical :=
      _physical.depicted_pit_depth_nonnegative
        ({ UnitChoices.SI with length := LengthUnit.micrometers } :
          UnitChoices)
    exact hPhysical
  have hPitMembership :
      setup.pitDepth ∈ DestructivePitDepths setup :=
    ⟨hPitNonnegative, _data.depicted_pit_cancels⟩
  have hPitBound :=
    hLeast.2 setup.pitDepth hPitMembership
  refine ⟨hLeast, hClosest, ?_⟩
  simpa [micrometersValue, lengthValueIn, lengthInMicrometers,
    lengthFromReadout, CarriesDimension.toDimensionful_apply_apply]
    using hPitBound

end PhyXMiniProblems.ProblemPhyXMini0116

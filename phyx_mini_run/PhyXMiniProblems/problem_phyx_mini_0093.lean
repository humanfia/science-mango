import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0093

/--
The physical dimension of optical intensity (power per unit area), namely
`M T⁻³` in the mass--length--time basis.
-/
def opticalIntensityDimension : Dimension :=
  Dimension.M𝓭 / Dimension.T𝓭 ^ 3

/--
Optical intensity measured in one fixed common unit.  The Physlib `WithDim`
tag prevents this physical quantity from being identified with a bare real
number, while `.val` is its scalar readout in that common unit.
-/
abbrev OpticalIntensity : Type := WithDim opticalIntensityDimension ℝ

/--
The polarization information carried by a beam in this problem.  A linear
polarization axis is represented by its real-valued radian angle from the
vertical reference line in the figure.
-/
inductive PolarizationState where
  | unpolarized
  | linearlyPolarized (axisAngleRadians : ℝ)

/--
A light beam together with its measured optical-intensity readout and
polarization state.  All intensity readouts use one fixed common physical unit,
so the real scalar records a measurement rather than identifying intensity as
an untyped scalar primitive.
-/
structure LightBeam where
  /-- Dimensioned optical intensity, with a scalar readout in the common unit. -/
  intensity : OpticalIntensity
  /-- Physical light intensity is nonnegative. -/
  intensity_nonnegative : 0 ≤ intensity
  /-- Qualitative polarization data needed by the ideal-polarizer laws. -/
  polarization : PolarizationState

/-- An ideal linear polarizing filter and the orientation of its transmission axis. -/
structure IdealLinearPolarizer where
  /-- Transmission-axis angle in radians, measured from the figure's vertical reference. -/
  axisAngleRadians : ℝ

/--
The ideal-filter transition law.  Unpolarized incident light loses half its
intensity.  Linearly polarized incident light obeys Malus's cosine-squared law.
In either case, the outgoing polarization is aligned with the filter axis.
-/
def PassesThroughIdealLinearPolarizer
    (incoming : LightBeam) (filter : IdealLinearPolarizer)
    (outgoing : LightBeam) : Prop :=
  outgoing.polarization =
      .linearlyPolarized filter.axisAngleRadians ∧
    outgoing.intensity.val =
      match incoming.polarization with
      | .unpolarized => incoming.intensity.val / 2
      | .linearlyPolarized incomingAxis =>
          incoming.intensity.val *
            Real.cos (filter.axisAngleRadians - incomingAxis) ^ 2

/--
Physical objects and labeled beam locations in the three-polarizer figure.
`beamAtCWithoutB` belongs to the modified experiment in which the middle
filter is removed; its intensity is deliberately not fixed by this structure.
-/
structure ThreePolarizerSetup where
  /-- The dimensioned optical intensity denoted by the figure label `I₀`. -/
  sourceIntensityI0 : OpticalIntensity
  /-- Beam immediately before polarizer A. -/
  incidentBeam : LightBeam
  /-- First (leftmost) polarizer, followed by figure point A. -/
  polarizerA : IdealLinearPolarizer
  /-- Middle polarizer, followed by figure point B. -/
  polarizerB : IdealLinearPolarizer
  /-- Last (rightmost) polarizer, followed by figure point C. -/
  polarizerC : IdealLinearPolarizer
  /-- Beam at point A in both the original and modified arrangements. -/
  beamAtA : LightBeam
  /-- Beam at point B in the original three-filter arrangement. -/
  beamAtB : LightBeam
  /-- Beam at point C in the original three-filter arrangement. -/
  beamAtC : LightBeam
  /-- Beam at point C when polarizer B has been removed. -/
  beamAtCWithoutB : LightBeam

/--
Direct readouts from the source label and the displayed filter-axis geometry.
The three angles are respectively `0°`, `60°`, and `90°` from vertical.
-/
structure ThreePolarizerFigureReadouts (setup : ThreePolarizerSetup) : Prop where
  source_intensity :
    setup.incidentBeam.intensity = setup.sourceIntensityI0
  source_unpolarized :
    setup.incidentBeam.polarization = .unpolarized
  axis_A_vertical :
    setup.polarizerA.axisAngleRadians = 0
  axis_B_sixty_degrees :
    setup.polarizerB.axisAngleRadians = Real.pi / 3
  axis_C_ninety_degrees :
    setup.polarizerC.axisAngleRadians = Real.pi / 2

/--
Applications of the ideal-polarizer law to the original A--B--C arrangement
and to the modified arrangement with B removed.  These transition assumptions
do not state the requested intensity at C.
-/
structure ThreePolarizerOpticsLaws (setup : ThreePolarizerSetup) : Prop where
  through_A :
    PassesThroughIdealLinearPolarizer
      setup.incidentBeam setup.polarizerA setup.beamAtA
  original_through_B :
    PassesThroughIdealLinearPolarizer
      setup.beamAtA setup.polarizerB setup.beamAtB
  original_through_C :
    PassesThroughIdealLinearPolarizer
      setup.beamAtB setup.polarizerC setup.beamAtC
  without_B_through_C :
    PassesThroughIdealLinearPolarizer
      setup.beamAtA setup.polarizerC setup.beamAtCWithoutB

/--
After the middle `60°` filter is removed, the remaining A and C filters have
crossed transmission axes.  Hence the light intensity at point C is zero,
which is answer choice A.

Blueprint label: `thm:physics:phyx_mini_0093:target`.
-/
theorem intensity_at_C_after_removing_middle_filter
    (setup : ThreePolarizerSetup)
    (_figure : ThreePolarizerFigureReadouts setup)
    (_laws : ThreePolarizerOpticsLaws setup) :
    setup.beamAtCWithoutB.intensity = 0 := by
  apply WithDim.ext
  rcases _laws.through_A with ⟨hApolarization, _⟩
  rcases _laws.without_B_through_C with ⟨_, hCintensity⟩
  rw [hApolarization, _figure.axis_C_ninety_degrees,
    _figure.axis_A_vertical] at hCintensity
  simpa using hCintensity

end PhyXMiniProblems.ProblemPhyXMini0093

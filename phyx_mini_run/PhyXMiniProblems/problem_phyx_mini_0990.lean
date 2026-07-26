import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0990

open Dimension

/-!
# Inductance of two coaxial series solenoids after reversing one winding

The primary raster `990.png` shows two long coaxial solenoids of common length
`λ`.  The outer solenoid has `N₁` turns and radius `b`; the inner solenoid has
`N₂` turns and radius `a`, with `a < b`.  Their left ends are separate leads,
whereas their right ends are connected.  The current arrow at the left lead
therefore describes a series path toward the right through the outer winding
and back toward the leads through the inner winding.

All physical magnitudes use Physlib's unit-independent
`Dimensionful (WithDim ...)` representation.  Real numbers occur only at
coherent-SI readout boundaries and in the literal multiple-choice metadata.

Assumption/target split:

* governing laws: the long-solenoid self-inductance formulas, the mutual
  inductance formula based on the common inner cross-section, and the magnetic
  energy/equivalent-inductance laws for a nonzero series current;
* previous-part results: none;
* figure/data readouts: `N₁`, `N₂`, `λ`, `a`, `b`, `a < b`, coaxial nesting,
  two left leads, the right-end series connection, and the directed outer-then-
  inner current path;
* current target conclusions: reversing the inner winding makes the coupling
  aiding, so the equivalent inductance is `L₁ + L₂ + 2 M`, and hence has the
  standard closed form in `N₁`, `N₂`, `λ`, `a`, `b`, and the medium
  permeability.

The source's recorded choice `B: 6.67 Ω` is retained below as typed dataset
metadata, but it is not identified with an inductance: ohms have the wrong
physical dimension, and the source supplies no numerical solenoid parameters.
-/

/-! ## Dimensions, physical quantities, and coherent-SI readouts -/

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Energy has dimension `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Inductance is energy divided by current squared. -/
def inductanceDimension : Dimension :=
  energyDimension * electricCurrentDimension⁻¹ * electricCurrentDimension⁻¹

/-- Magnetic permeability has dimension inductance per unit length. -/
def magneticPermeabilityDimension : Dimension :=
  inductanceDimension * L𝓭⁻¹

/-- Resistance has dimension inductance per unit time. -/
def electricalResistanceDimension : Dimension :=
  inductanceDimension * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev CurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-energy magnitude. -/
abbrev EnergyMagnitude : Type :=
  Dimensionful (WithDim energyDimension NNReal)

/-- A nonnegative, unit-independent inductance magnitude. -/
abbrev InductanceMagnitude : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- A nonnegative, unit-independent permeability magnitude. -/
abbrev MagneticPermeabilityMagnitude : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- Read any nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : CurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read magnetic energy in joules. -/
def energyInJoules (energy : EnergyMagnitude) : ℝ :=
  nonnegativeSIReadout energy

/-- Read an inductance in henries. -/
def inductanceInHenries (inductance : InductanceMagnitude) : ℝ :=
  nonnegativeSIReadout inductance

/-- Read a magnetic permeability in henries per metre. -/
def permeabilityInHenriesPerMeter
    (permeability : MagneticPermeabilityMagnitude) : ℝ :=
  nonnegativeSIReadout permeability

/-! ## Figure labels, topology, and winding configurations -/

/-- Physical objects visible in the primary raster. -/
inductive FigureObject where
  | outerSolenoid
  | innerSolenoid
  | outerLead
  | innerLead
  | rightEndConnection
  | currentArrow
  deriving DecidableEq, Fintype, Repr

/-- Textual or symbolic annotations visible in `990.png`. -/
inductive FigureLabel where
  | commonLengthLambda
  | outerRadiusB
  | innerRadiusA
  | outerTurnCountN1
  | innerTurnCountN2
  | currentI
  | leadsText
  | connectedAtThisEndText
  deriving DecidableEq, Fintype, Repr

/-- The two axial ends of the coaxial pair in the raster. -/
inductive SolenoidEnd where
  | leadEnd
  | connectedEnd
  deriving DecidableEq, Repr

/-- Directed travel along the common solenoid axis. -/
inductive AxialCurrentDirection where
  | towardConnectedEnd
  | towardLeadEnd
  deriving DecidableEq, Repr

/-- The series-current route determined by the right-end connection. -/
inductive SeriesCurrentPath where
  | outerThenInner
  | innerThenOuter
  deriving DecidableEq, Repr

/-- The winding state relevant to the question. -/
inductive WindingConfiguration where
  | asDrawn
  | innerWindingReversed
  deriving DecidableEq, Fintype, Repr

/-- Whether the two solenoid fields oppose or reinforce for the series current. -/
inductive MagneticCouplingSense where
  | opposing
  | aiding
  deriving DecidableEq, Repr

/-- Literal presentation and spatial relations transcribed from `990.png`. -/
structure CoaxialSolenoidFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  outerSurroundsInner : Bool
  solenoidAxesCoincide : Bool
  commonAxialExtentMarkedLambda : Bool
  leadsAt : SolenoidEnd
  solenoidsConnectedAt : SolenoidEnd
  displayedSeriesPath : SeriesCurrentPath
  outerCurrentDirection : AxialCurrentDirection
  innerCurrentDirection : AxialCurrentDirection

/-!
Independent geometry, material properties, inductances, and energy observables.
In particular, the reversed equivalent inductance is an independent field and
is not defined from the desired closed formula.
-/
structure CoaxialSeriesSolenoidSetup where
  outerTurnCount : ℕ
  innerTurnCount : ℕ
  commonLength : LengthMagnitude
  outerRadius : LengthMagnitude
  innerRadius : LengthMagnitude
  mediumPermeability : MagneticPermeabilityMagnitude
  outerSelfInductance : InductanceMagnitude
  innerSelfInductance : InductanceMagnitude
  mutualInductanceMagnitude : InductanceMagnitude
  couplingSense : WindingConfiguration → MagneticCouplingSense
  equivalentInductance : WindingConfiguration → InductanceMagnitude
  magneticEnergy : WindingConfiguration → CurrentMagnitude → EnergyMagnitude
  figure : CoaxialSolenoidFigure

/-! ## Figure evidence and physical scenario -/

/-- The labels, nesting, connection, and current arrows read from the image. -/
structure MatchesSuppliedCoaxialSolenoidFigure
    (setup : CoaxialSeriesSolenoidSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.objectShown object = true
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  outerSurroundsInner : setup.figure.outerSurroundsInner = true
  axesAreCoaxial : setup.figure.solenoidAxesCoincide = true
  lambdaMarksCommonLength :
    setup.figure.commonAxialExtentMarkedLambda = true
  twoLeadsAtLeftEnd : setup.figure.leadsAt = .leadEnd
  connectedAtRightEnd : setup.figure.solenoidsConnectedAt = .connectedEnd
  currentTraversesOuterThenInner :
    setup.figure.displayedSeriesPath = .outerThenInner
  currentTravelsDownOuter :
    setup.figure.outerCurrentDirection = .towardConnectedEnd
  currentReturnsThroughInner :
    setup.figure.innerCurrentDirection = .towardLeadEnd

/-- Positivity and the strict radius relation `0 < a < b`. -/
structure HasPhysicalLongCoaxialGeometry
    (setup : CoaxialSeriesSolenoidSetup) : Prop where
  outerHasTurns : 0 < setup.outerTurnCount
  innerHasTurns : 0 < setup.innerTurnCount
  positiveCommonLength : 0 < lengthInMeters setup.commonLength
  positiveInnerRadius : 0 < lengthInMeters setup.innerRadius
  innerRadiusLessThanOuterRadius :
    lengthInMeters setup.innerRadius < lengthInMeters setup.outerRadius
  positivePermeability :
    0 < permeabilityInHenriesPerMeter setup.mediumPermeability

/-!
Reversing only the inner winding changes an opposing series-field arrangement
into an aiding one; it does not change the geometry, turn counts, or material.
This is qualitative winding data, not an inductance-value premise.
-/
structure ModelsInnerWindingReversal
    (setup : CoaxialSeriesSolenoidSetup) : Prop where
  asDrawnIsOpposing : setup.couplingSense .asDrawn = .opposing
  reversedIsAiding :
    setup.couplingSense .innerWindingReversed = .aiding

/-! ## Governing long-solenoid and magnetic-energy laws -/

/-!
The standard long-solenoid self and mutual inductances.  The mutual term uses
the area `π a²` common to both coaxial fields, not the outer area `π b²`.
None of these fields mentions the equivalent inductance after reversal.
-/
structure SatisfiesLongCoaxialSolenoidLaws
    (setup : CoaxialSeriesSolenoidSetup) : Prop where
  outerSelfInductanceLaw :
    inductanceInHenries setup.outerSelfInductance =
      permeabilityInHenriesPerMeter setup.mediumPermeability * Real.pi *
        (setup.outerTurnCount : ℝ) ^ 2 *
        lengthInMeters setup.outerRadius ^ 2 /
        lengthInMeters setup.commonLength
  innerSelfInductanceLaw :
    inductanceInHenries setup.innerSelfInductance =
      permeabilityInHenriesPerMeter setup.mediumPermeability * Real.pi *
        (setup.innerTurnCount : ℝ) ^ 2 *
        lengthInMeters setup.innerRadius ^ 2 /
        lengthInMeters setup.commonLength
  mutualInductanceLaw :
    inductanceInHenries setup.mutualInductanceMagnitude =
      permeabilityInHenriesPerMeter setup.mediumPermeability * Real.pi *
        (setup.outerTurnCount : ℝ) * (setup.innerTurnCount : ℝ) *
        lengthInMeters setup.innerRadius ^ 2 /
        lengthInMeters setup.commonLength

/-!
Magnetic energy is both `L_eq I² / 2` and the sum of the two self-energy
terms plus the aiding mutual-energy term after reversal.  Stating the laws for
every current avoids defining the requested inductance by the target formula.
-/
structure SatisfiesSeriesMagneticEnergyLaws
    (setup : CoaxialSeriesSolenoidSetup) : Prop where
  energyDefinesEquivalentInductance :
    ∀ configuration current,
      energyInJoules (setup.magneticEnergy configuration current) =
        (1 / 2 : ℝ) *
          inductanceInHenries (setup.equivalentInductance configuration) *
          currentInAmperes current ^ 2
  aidingEnergyAfterInnerReversal :
    ∀ current,
      energyInJoules
          (setup.magneticEnergy .innerWindingReversed current) =
        (1 / 2 : ℝ) * inductanceInHenries setup.outerSelfInductance *
            currentInAmperes current ^ 2 +
          (1 / 2 : ℝ) * inductanceInHenries setup.innerSelfInductance *
            currentInAmperes current ^ 2 +
          inductanceInHenries setup.mutualInductanceMagnitude *
            currentInAmperes current ^ 2
  admitsNonzeroSeriesCurrent :
    ∃ current : CurrentMagnitude, 0 < currentInAmperes current

/-! ## Recorded multiple-choice metadata -/

/-- Labels printed beside the four dataset choices. -/
inductive AnswerLabel where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The source explicitly prints the resistance unit ohm after every value. -/
inductive PrintedElectricalUnit where
  | ohm
  deriving DecidableEq, Repr

/-- A literal answer row, kept separate from dimensionful physical quantities. -/
structure ListedAnswer where
  label : AnswerLabel
  displayedValue : ℝ
  printedUnit : PrintedElectricalUnit

/-- The four rows exactly as numerically represented in the source. -/
def listedAnswer : AnswerLabel → ListedAnswer
  | .A => ⟨.A, 10, .ohm⟩
  | .B => ⟨.B, 6.67, .ohm⟩
  | .C => ⟨.C, 3.33, .ohm⟩
  | .D => ⟨.D, 13.3, .ohm⟩

/-- The answer key records row B; this is metadata, not an inductance claim. -/
def recordedDatasetAnswer : ListedAnswer :=
  listedAnswer .B

/-! ## Derived reversed-winding inductance -/

/-- Aiding magnetic energy gives the standard series formula. -/
lemma reversed_series_inductance_eq_self_add_self_add_twice_mutual
    (setup : CoaxialSeriesSolenoidSetup)
    (hgeometry : HasPhysicalLongCoaxialGeometry setup)
    (hreversal : ModelsInnerWindingReversal setup)
    (henergy : SatisfiesSeriesMagneticEnergyLaws setup) :
    inductanceInHenries
        (setup.equivalentInductance .innerWindingReversed) =
      inductanceInHenries setup.outerSelfInductance +
        inductanceInHenries setup.innerSelfInductance +
        2 * inductanceInHenries setup.mutualInductanceMagnitude := by
  obtain ⟨current, hcurrent⟩ := henergy.admitsNonzeroSeriesCurrent
  have hequivalent :=
    henergy.energyDefinesEquivalentInductance
      WindingConfiguration.innerWindingReversed current
  have haiding := henergy.aidingEnergyAfterInnerReversal current
  have hmul :
      (inductanceInHenries
          (setup.equivalentInductance .innerWindingReversed) -
        (inductanceInHenries setup.outerSelfInductance +
          inductanceInHenries setup.innerSelfInductance +
          2 * inductanceInHenries setup.mutualInductanceMagnitude)) *
          currentInAmperes current ^ 2 = 0 := by
    calc
      _ = 2 * ((1 / 2 : ℝ) *
          inductanceInHenries
            (setup.equivalentInductance .innerWindingReversed) *
            currentInAmperes current ^ 2 -
        ((1 / 2 : ℝ) * inductanceInHenries setup.outerSelfInductance *
            currentInAmperes current ^ 2 +
          (1 / 2 : ℝ) * inductanceInHenries setup.innerSelfInductance *
            currentInAmperes current ^ 2 +
          inductanceInHenries setup.mutualInductanceMagnitude *
            currentInAmperes current ^ 2)) := by ring
      _ = 0 := by rw [← hequivalent, ← haiding]; ring
  have hcurrent_sq : currentInAmperes current ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt hcurrent)
  have hcoefficient := (mul_eq_zero.mp hmul).resolve_right hcurrent_sq
  linarith

/-!
Reversing the inner winding changes the series coupling from opposing to aiding.
Consequently the common-area mutual term enters with a plus sign.

This theorem is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0990:target`.
-/
theorem problem_phyx_mini_0990
    (setup : CoaxialSeriesSolenoidSetup)
    (hfigure : MatchesSuppliedCoaxialSolenoidFigure setup)
    (hgeometry : HasPhysicalLongCoaxialGeometry setup)
    (hreversal : ModelsInnerWindingReversal setup)
    (hlong : SatisfiesLongCoaxialSolenoidLaws setup)
    (henergy : SatisfiesSeriesMagneticEnergyLaws setup) :
    inductanceInHenries
        (setup.equivalentInductance .innerWindingReversed) =
      permeabilityInHenriesPerMeter setup.mediumPermeability * Real.pi /
        lengthInMeters setup.commonLength *
        ((setup.outerTurnCount : ℝ) ^ 2 *
            lengthInMeters setup.outerRadius ^ 2 +
          (setup.innerTurnCount : ℝ) ^ 2 *
            lengthInMeters setup.innerRadius ^ 2 +
          2 * (setup.outerTurnCount : ℝ) * (setup.innerTurnCount : ℝ) *
            lengthInMeters setup.innerRadius ^ 2) := by
  calc
    _ = inductanceInHenries setup.outerSelfInductance +
          inductanceInHenries setup.innerSelfInductance +
          2 * inductanceInHenries setup.mutualInductanceMagnitude :=
      reversed_series_inductance_eq_self_add_self_add_twice_mutual
        setup hgeometry hreversal henergy
    _ = _ := by
      rw [hlong.outerSelfInductanceLaw, hlong.innerSelfInductanceLaw,
        hlong.mutualInductanceLaw]
      ring

end PhyXMiniProblems.ProblemPhyXMini0990

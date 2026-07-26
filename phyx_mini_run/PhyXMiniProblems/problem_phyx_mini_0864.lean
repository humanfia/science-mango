import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0864

open Dimension
open scoped BigOperators

/-!
# Four identical charged spheres released from the corners of a square

The primary image shows four identical positive `10 nC` charges, one at each
corner of a dashed square.  Both the top and left sides are labelled `1.0 cm`.
The prose states that the four spheres each have mass `1.0 g`, are released
simultaneously, and move far apart.

The physical mass, charge, length, speed, and energy observables below are
unit-independent Physlib quantities.  Real numbers are used only for coherent
SI readouts, literal figure inscriptions, and dimensionless answer data.

Assumption/target split:

* governing laws: pairwise Coulomb potential energy, additive electrostatic
  energy, translational kinetic energy, mechanical-energy conservation, the
  vanishing of electrostatic potential energy in the far-apart regime, and
  preservation of the square release symmetry;
* previous-part results: none;
* figure/data readouts: four positive `10 nC` corner charges, four `1.0 g`
  spheres, a dashed square with top and left sides labelled `1.0 cm`, release
  from rest, and the free-space Coulomb constant;
* target conclusions: the common final speed has the energy-derived square-root
  formula, lies between `0.49 m/s` and `0.50 m/s`, and makes answer D (`0.49
  m/s`) the unique nearest displayed choice.

No target speed or answer label is stored in a setup field or law premise.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- The physical dimension `L T⁻¹` of speed. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the two dimension labels in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Gram readout used by the prose description of each sphere. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-- Coherent-SI coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the four printed charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedMagnitudeQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Coherent-SI joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Sphere labels, unordered pairs, and primary-image vocabulary -/

/-- The four physical spheres, named by their initial image locations. -/
inductive SphereLabel where
  | topLeft
  | topRight
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- The four corners of the dashed square. -/
inductive SquareCorner where
  | topLeft
  | topRight
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- Corner at which each named sphere appears in the primary image. -/
def expectedSphereCorner : SphereLabel → SquareCorner
  | .topLeft => .topLeft
  | .topRight => .topRight
  | .bottomLeft => .bottomLeft
  | .bottomRight => .bottomRight

/-- The six unordered pairs among the four spheres. -/
inductive SpherePair where
  | topLeft_topRight
  | topLeft_bottomLeft
  | topRight_bottomRight
  | bottomLeft_bottomRight
  | topLeft_bottomRight
  | topRight_bottomLeft
  deriving DecidableEq, Fintype, Repr

/-- First endpoint of a named unordered sphere pair. -/
def SpherePair.first : SpherePair → SphereLabel
  | .topLeft_topRight => .topLeft
  | .topLeft_bottomLeft => .topLeft
  | .topRight_bottomRight => .topRight
  | .bottomLeft_bottomRight => .bottomLeft
  | .topLeft_bottomRight => .topLeft
  | .topRight_bottomLeft => .topRight

/-- Second endpoint of a named unordered sphere pair. -/
def SpherePair.second : SpherePair → SphereLabel
  | .topLeft_topRight => .topRight
  | .topLeft_bottomLeft => .bottomLeft
  | .topRight_bottomRight => .bottomRight
  | .bottomLeft_bottomRight => .bottomRight
  | .topLeft_bottomRight => .bottomRight
  | .topRight_bottomLeft => .bottomLeft

/-- Whether a pair spans a side or a diagonal of the square. -/
inductive PairGeometry where
  | edge
  | diagonal
  deriving DecidableEq, Repr

/-- Geometric role of each unordered sphere pair. -/
def SpherePair.geometry : SpherePair → PairGeometry
  | .topLeft_topRight => .edge
  | .topLeft_bottomLeft => .edge
  | .topRight_bottomRight => .edge
  | .bottomLeft_bottomRight => .edge
  | .topLeft_bottomRight => .diagonal
  | .topRight_bottomLeft => .diagonal

/-- The four dashed boundary edges visible in the raster. -/
inductive SquareEdge where
  | top
  | right
  | bottom
  | left
  deriving DecidableEq, Fintype, Repr

/-- The primary image prints `1.0 cm` only on the top and left edges. -/
def expectedDimensionLabelCentimeters : SquareEdge → Option ℝ
  | .top => some 1
  | .right => none
  | .bottom => none
  | .left => some 1

/-- Fill colour of each positive-charge circle in the supplied image. -/
inductive ChargeCircleColor where
  | lightRed
  deriving DecidableEq, Repr

/-- Charge-sign glyph drawn inside every sphere circle. -/
inductive ChargeSignGlyph where
  | plus
  deriving DecidableEq, Repr

/-- Literal presentation data transcribed from image `864.png`. -/
structure FourChargeSquareFigure where
  sphereCorner : SphereLabel → SquareCorner
  sphereCircleColor : SphereLabel → ChargeCircleColor
  sphereSignGlyph : SphereLabel → ChargeSignGlyph
  printedChargeNanocoulombs : SphereLabel → ℝ
  dashedEdgeShown : SquareEdge → Bool
  dimensionLabelCentimeters : SquareEdge → Option ℝ

/-! ## Independent physical setup -/

/-- The qualitative interaction idealization used after simultaneous release. -/
inductive InteractionModel where
  | isolatedElectrostaticRepulsion
  | other
  deriving DecidableEq, Repr

/-- The separation regime at which the final speed is observed. -/
inductive SeparationRegime where
  | finite
  | veryFarApart
  deriving DecidableEq, Repr

/-!
Independent quantities and energy observables for the square release.

The final speeds are unknown physical observables.  They are not defined from
the recorded answer or from the derived square-root expression.
-/
structure FourChargedSphereReleaseSetup where
  figure : FourChargeSquareFigure
  sphereMass : SphereLabel → MassQuantity
  sphereCharge : SphereLabel → SignedChargeQuantity
  squareSideLength : LengthQuantity
  initialPosition : SphereLabel → Space 2
  initialPairSeparation : SpherePair → LengthQuantity
  initialSpeed : SphereLabel → SpeedMagnitudeQuantity
  finalSpeed : SphereLabel → SpeedMagnitudeQuantity
  initialPairPotentialEnergy : SpherePair → DimEnergy
  initialKineticEnergy : SphereLabel → DimEnergy
  finalKineticEnergy : SphereLabel → DimEnergy
  initialElectrostaticPotentialEnergy : DimEnergy
  finalElectrostaticPotentialEnergy : DimEnergy
  electromagneticSystem : Electromagnetism.EMSystem
  interactionModel : InteractionModel
  finalSeparationRegime : SeparationRegime
  releasedSimultaneously : Bool

/-- Turn a planar `Space 2` point into its explicitly metre-valued vector. -/
def positionVectorInMeters (point : Space 2) : EuclideanSpace ℝ (Fin 2) :=
  !₂[point.val 0, point.val 1]

/-- Initial displacement between the endpoints of an unordered pair. -/
def initialPairDisplacementInMeters
    (setup : FourChargedSphereReleaseSetup) (pair : SpherePair) :
    EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters (setup.initialPosition pair.second) -
    positionVectorInMeters (setup.initialPosition pair.first)

/-! ## Problem data and primary-image evidence -/

/-!
The numerical labels, corner associations, and release conditions stated in
the problem and visible in the primary image.  No final speed occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : FourChargedSphereReleaseSetup) : Prop where
  sphereLocations : ∀ sphere,
    setup.figure.sphereCorner sphere = expectedSphereCorner sphere
  allCirclesLightRed : ∀ sphere,
    setup.figure.sphereCircleColor sphere = .lightRed
  allGlyphsPositive : ∀ sphere,
    setup.figure.sphereSignGlyph sphere = .plus
  allPrintedChargesTenNanocoulombs : ∀ sphere,
    setup.figure.printedChargeNanocoulombs sphere = 10
  physicalChargesMatchPrintedLabels : ∀ sphere,
    chargeInNanocoulombs (setup.sphereCharge sphere) =
      setup.figure.printedChargeNanocoulombs sphere
  everySphereHasMassOneGram : ∀ sphere,
    massInGrams (setup.sphereMass sphere) = 1
  everyBoundaryEdgeIsDashed : ∀ edge,
    setup.figure.dashedEdgeShown edge = true
  dimensionLabelsMatchImage : ∀ edge,
    setup.figure.dimensionLabelCentimeters edge =
      expectedDimensionLabelCentimeters edge
  sideLengthMatchesTopLabel :
    setup.figure.dimensionLabelCentimeters .top =
      some (lengthInCentimeters setup.squareSideLength)
  sideLengthMatchesLeftLabel :
    setup.figure.dimensionLabelCentimeters .left =
      some (lengthInCentimeters setup.squareSideLength)
  releasedAtTheSameTime : setup.releasedSimultaneously = true
  releasedFromRest : ∀ sphere,
    speedInMetersPerSecond (setup.initialSpeed sphere) = 0
  electrostaticInteractionOnly :
    setup.interactionModel = .isolatedElectrostaticRepulsion

/-!
Coordinate realization of the square and the relation between Euclidean
separation and the physical pair-distance quantity.  The bottom-left corner
is chosen as the coordinate origin without loss of physical generality.
-/
structure MatchesSquareGeometry
    (setup : FourChargedSphereReleaseSetup) : Prop where
  bottomLeftAtOrigin :
    positionVectorInMeters (setup.initialPosition .bottomLeft) = !₂[0, 0]
  bottomRightCoordinates :
    positionVectorInMeters (setup.initialPosition .bottomRight) =
      !₂[lengthInMeters setup.squareSideLength, 0]
  topLeftCoordinates :
    positionVectorInMeters (setup.initialPosition .topLeft) =
      !₂[0, lengthInMeters setup.squareSideLength]
  topRightCoordinates :
    positionVectorInMeters (setup.initialPosition .topRight) =
      !₂[lengthInMeters setup.squareSideLength,
        lengthInMeters setup.squareSideLength]
  pairSeparationIsEuclideanDistance : ∀ pair,
    lengthInMeters (setup.initialPairSeparation pair) =
      ‖initialPairDisplacementInMeters setup pair‖

/-- Positivity conditions selecting the nondegenerate physical branch. -/
structure HasPhysicalSquareReleaseParameters
    (setup : FourChargedSphereReleaseSetup) : Prop where
  massesPositive : ∀ sphere,
    0 < massInKilograms (setup.sphereMass sphere)
  chargesPositive : ∀ sphere,
    0 < chargeInCoulombs (setup.sphereCharge sphere)
  sideLengthPositive : 0 < lengthInMeters setup.squareSideLength
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-- Free-space calibration of Physlib's electromagnetic system in SI units. -/
structure UsesVacuumCoulombConstant
    (setup : FourChargedSphereReleaseSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 8.9875517923e9

/-! ## Governing electrostatic and mechanical-energy laws -/

/-!
Every unordered pair contributes `k q₁ q₂/r`, the pair energies add to the
initial electrostatic energy, and each sphere has translational kinetic energy
`m v²/2`.  Conservation is stated between release and the far-apart state.
These laws contain no numerical assertion about the final speed.
-/
structure SatisfiesCoulombAndMechanicalEnergyLaws
    (setup : FourChargedSphereReleaseSetup) : Prop where
  pairwiseCoulombPotentialEnergy : ∀ pair,
    energyInJoules (setup.initialPairPotentialEnergy pair) =
      setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.sphereCharge pair.first) *
          chargeInCoulombs (setup.sphereCharge pair.second) /
        lengthInMeters (setup.initialPairSeparation pair)
  initialElectrostaticEnergyIsPairSum :
    energyInJoules setup.initialElectrostaticPotentialEnergy =
      ∑ pair : SpherePair,
        energyInJoules (setup.initialPairPotentialEnergy pair)
  initialTranslationalKineticEnergy : ∀ sphere,
    energyInJoules (setup.initialKineticEnergy sphere) =
      (1 / 2 : ℝ) * massInKilograms (setup.sphereMass sphere) *
        speedInMetersPerSecond (setup.initialSpeed sphere) ^ 2
  finalTranslationalKineticEnergy : ∀ sphere,
    energyInJoules (setup.finalKineticEnergy sphere) =
      (1 / 2 : ℝ) * massInKilograms (setup.sphereMass sphere) *
        speedInMetersPerSecond (setup.finalSpeed sphere) ^ 2
  mechanicalEnergyConservation :
    (∑ sphere : SphereLabel,
        energyInJoules (setup.initialKineticEnergy sphere)) +
        energyInJoules setup.initialElectrostaticPotentialEnergy =
      (∑ sphere : SphereLabel,
        energyInJoules (setup.finalKineticEnergy sphere)) +
        energyInJoules setup.finalElectrostaticPotentialEnergy

/-!
At asymptotically large mutual separation the zero of Coulomb potential is
chosen so that the remaining electrostatic potential energy vanishes.
-/
structure ReachesVeryFarApartRegime
    (setup : FourChargedSphereReleaseSetup) : Prop where
  finalRegimeIsVeryFarApart :
    setup.finalSeparationRegime = .veryFarApart
  finalElectrostaticPotentialVanishes :
    energyInJoules setup.finalElectrostaticPotentialEnergy = 0

/-!
The isolated evolution preserves the rotational and reflection symmetries of
four identical charges released from rest at the corners of a square.  This
states equality of final speed magnitudes, not their requested value.
-/
structure PreservesSquareReleaseSymmetry
    (setup : FourChargedSphereReleaseSetup) : Prop where
  allFinalSpeedMagnitudesEqual : ∀ first second,
    speedInMetersPerSecond (setup.finalSpeed first) =
      speedInMetersPerSecond (setup.finalSpeed second)

/-! ## Derived speed and displayed answer choices -/

/--
The speed candidate obtained by converting the six initial pair energies into
the kinetic energy of four equal-mass spheres.  The factor `4 + sqrt 2` comes
from four side pairs and two diagonal pairs.
-/
def energyDerivedSpeedInMetersPerSecond
    (setup : FourChargedSphereReleaseSetup) : ℝ :=
  Real.sqrt
    (setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs (setup.sphereCharge .topLeft) ^ 2 *
        (4 + Real.sqrt 2) /
      (2 * massInKilograms (setup.sphereMass .topLeft) *
        lengthInMeters setup.squareSideLength))

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre-per-second value printed beside each answer label. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 59 / 100
  | .B => 149 / 100
  | .C => 19 / 100
  | .D => 49 / 100

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed answer is uniquely closest to every sphere's final speed. -/
def IsUniqueClosestDisplayedSpeed
    (setup : FourChargedSphereReleaseSetup)
    (choice : AnswerChoice) : Prop :=
  ∀ sphere : SphereLabel, ∀ other : AnswerChoice, other ≠ choice →
    |speedInMetersPerSecond (setup.finalSpeed sphere) -
        choice.speedInMetersPerSecond| <
      |speedInMetersPerSecond (setup.finalSpeed sphere) -
        other.speedInMetersPerSecond|

/-!
Euclidean square geometry gives four separations equal to the side length and
two equal to `sqrt 2` times that length.  This is a derived geometric fact,
not an extra setup assumption.
-/
lemma initialPairSeparation_formula
    (setup : FourChargedSphereReleaseSetup)
    (h_geometry : MatchesSquareGeometry setup) :
    ∀ pair : SpherePair,
      lengthInMeters (setup.initialPairSeparation pair) =
        match pair.geometry with
        | .edge => lengthInMeters setup.squareSideLength
        | .diagonal =>
            Real.sqrt 2 * lengthInMeters setup.squareSideLength := by
  intro pair
  have hl : 0 ≤ lengthInMeters setup.squareSideLength := by
    unfold lengthInMeters
    positivity
  fin_cases pair <;>
    simp [SpherePair.geometry, h_geometry.pairSeparationIsEuclideanDistance,
      initialPairDisplacementInMeters, SpherePair.first, SpherePair.second,
      h_geometry.bottomLeftAtOrigin, h_geometry.bottomRightCoordinates,
      h_geometry.topLeftCoordinates, h_geometry.topRightCoordinates,
      EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  all_goals first | exact Real.sqrt_sq hl | skip
  all_goals
    rw [show lengthInMeters setup.squareSideLength ^ 2 +
        lengthInMeters setup.squareSideLength ^ 2 =
        2 * lengthInMeters setup.squareSideLength ^ 2 by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hl]

/-!
Summing the four edge-pair and two diagonal-pair Coulomb energies yields the
initial electrostatic energy.  No displayed speed is used.
-/
lemma initialElectrostaticPotentialEnergy_formula
    (setup : FourChargedSphereReleaseSetup)
    (h_data : MatchesProblemAndPrimaryFigure setup)
    (h_geometry : MatchesSquareGeometry setup)
    (h_physical : HasPhysicalSquareReleaseParameters setup)
    (h_laws : SatisfiesCoulombAndMechanicalEnergyLaws setup) :
    energyInJoules setup.initialElectrostaticPotentialEnergy =
      setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.sphereCharge .topLeft) ^ 2 *
          (4 + Real.sqrt 2) /
        lengthInMeters setup.squareSideLength := by
  classical
  have hsep := initialPairSeparation_formula setup h_geometry
  have hq : ∀ sphere, chargeInCoulombs (setup.sphereCharge sphere) =
      chargeInCoulombs (setup.sphereCharge .topLeft) := by
    intro sphere
    have hs := h_data.physicalChargesMatchPrintedLabels sphere
    have ht :=
      h_data.physicalChargesMatchPrintedLabels SphereLabel.topLeft
    rw [h_data.allPrintedChargesTenNanocoulombs sphere] at hs
    rw [h_data.allPrintedChargesTenNanocoulombs SphereLabel.topLeft] at ht
    unfold chargeInNanocoulombs at hs ht
    linarith
  have huniv : (Finset.univ : Finset SpherePair) =
      {.topLeft_topRight, .topLeft_bottomLeft, .topRight_bottomRight,
        .bottomLeft_bottomRight, .topLeft_bottomRight,
        .topRight_bottomLeft} := by
    ext pair
    fin_cases pair <;> simp
  rw [h_laws.initialElectrostaticEnergyIsPairSum]
  rw [show (∑ pair : SpherePair,
      energyInJoules (setup.initialPairPotentialEnergy pair)) =
      (∑ pair ∈
        ({.topLeft_topRight, .topLeft_bottomLeft, .topRight_bottomRight,
          .bottomLeft_bottomRight, .topLeft_bottomRight,
          .topRight_bottomLeft} : Finset SpherePair),
        energyInJoules (setup.initialPairPotentialEnergy pair)) by
          rw [← huniv]]
  simp [h_laws.pairwiseCoulombPotentialEnergy, hsep, SpherePair.geometry,
    SpherePair.first, SpherePair.second, hq]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [h_physical.sideLengthPositive.ne', hsqrt]
  ring_nf
  rw [show Real.sqrt 2 ^ 2 = 2 by norm_num]
  ring

/-!
Energy conservation, release from rest, the far-apart zero of potential, and
square symmetry determine the common final speed.
-/
lemma finalSpeed_formula
    (setup : FourChargedSphereReleaseSetup)
    (h_data : MatchesProblemAndPrimaryFigure setup)
    (h_geometry : MatchesSquareGeometry setup)
    (h_physical : HasPhysicalSquareReleaseParameters setup)
    (h_laws : SatisfiesCoulombAndMechanicalEnergyLaws setup)
    (h_far : ReachesVeryFarApartRegime setup)
    (h_symmetry : PreservesSquareReleaseSymmetry setup) :
    ∀ sphere : SphereLabel,
      speedInMetersPerSecond (setup.finalSpeed sphere) =
        energyDerivedSpeedInMetersPerSecond setup := by
  intro sphere
  have hm : ∀ s, massInKilograms (setup.sphereMass s) =
      massInKilograms (setup.sphereMass .topLeft) := by
    intro s
    have hs := h_data.everySphereHasMassOneGram s
    have ht := h_data.everySphereHasMassOneGram SphereLabel.topLeft
    unfold massInGrams at hs ht
    linarith
  have hv : ∀ s, speedInMetersPerSecond (setup.finalSpeed s) =
      speedInMetersPerSecond (setup.finalSpeed .topLeft) := by
    intro s
    exact h_symmetry.allFinalSpeedMagnitudesEqual s .topLeft
  have hinit : ∀ s,
      energyInJoules (setup.initialKineticEnergy s) = 0 := by
    intro s
    rw [h_laws.initialTranslationalKineticEnergy s,
      h_data.releasedFromRest s]
    ring
  have hfinal : ∀ s,
      energyInJoules (setup.finalKineticEnergy s) =
        (1 / 2 : ℝ) * massInKilograms (setup.sphereMass .topLeft) *
          speedInMetersPerSecond (setup.finalSpeed .topLeft) ^ 2 := by
    intro s
    rw [h_laws.finalTranslationalKineticEnergy s, hm s, hv s]
  have henergy := h_laws.mechanicalEnergyConservation
  rw [initialElectrostaticPotentialEnergy_formula setup h_data h_geometry
    h_physical h_laws, h_far.finalElectrostaticPotentialVanishes] at henergy
  simp_rw [hinit, hfinal] at henergy
  have hcard : Fintype.card SphereLabel = 4 := by decide
  norm_num [hcard] at henergy
  have hmpos := h_physical.massesPositive SphereLabel.topLeft
  have hvsq : speedInMetersPerSecond (setup.finalSpeed .topLeft) ^ 2 =
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs (setup.sphereCharge .topLeft) ^ 2 *
        (4 + Real.sqrt 2) /
      (2 * massInKilograms (setup.sphereMass .topLeft) *
        lengthInMeters setup.squareSideLength) := by
    field_simp [hmpos.ne', h_physical.sideLengthPositive.ne'] at henergy ⊢
    nlinarith
  rw [hv sphere, energyDerivedSpeedInMetersPerSecond, ← hvsq]
  have hvnonneg :
      0 ≤ speedInMetersPerSecond (setup.finalSpeed .topLeft) := by
    unfold speedInMetersPerSecond
    positivity
  exact (Real.sqrt_sq hvnonneg).symm

/-!
With the printed mass, charge, side length, and reference Coulomb constant,
the derived final speed lies strictly between `0.49 m/s` and `0.50 m/s`.
-/
lemma finalSpeed_numericalBounds
    (setup : FourChargedSphereReleaseSetup)
    (h_data : MatchesProblemAndPrimaryFigure setup)
    (h_geometry : MatchesSquareGeometry setup)
    (h_constants : UsesVacuumCoulombConstant setup)
    (h_physical : HasPhysicalSquareReleaseParameters setup)
    (h_laws : SatisfiesCoulombAndMechanicalEnergyLaws setup)
    (h_far : ReachesVeryFarApartRegime setup)
    (h_symmetry : PreservesSquareReleaseSymmetry setup) :
    ∀ sphere : SphereLabel,
      49 / 100 < speedInMetersPerSecond (setup.finalSpeed sphere) ∧
        speedInMetersPerSecond (setup.finalSpeed sphere) < 50 / 100 := by
  intro sphere
  rw [finalSpeed_formula setup h_data h_geometry h_physical h_laws h_far
    h_symmetry sphere]
  have hq :=
    h_data.physicalChargesMatchPrintedLabels SphereLabel.topLeft
  rw [h_data.allPrintedChargesTenNanocoulombs SphereLabel.topLeft] at hq
  norm_num [chargeInNanocoulombs] at hq
  have hq' : chargeInCoulombs (setup.sphereCharge .topLeft) =
      (1 / 100000000 : ℝ) := by
    linarith
  have hm := h_data.everySphereHasMassOneGram SphereLabel.topLeft
  norm_num [massInGrams] at hm
  have hm' : massInKilograms (setup.sphereMass .topLeft) =
      (1 / 1000 : ℝ) := by
    linarith
  have hl := h_data.sideLengthMatchesTopLabel
  rw [h_data.dimensionLabelsMatchImage SquareEdge.top] at hl
  norm_num [expectedDimensionLabelCentimeters, lengthInCentimeters] at hl
  have hl' : lengthInMeters setup.squareSideLength = (1 / 100 : ℝ) := by
    linarith
  rw [energyDerivedSpeedInMetersPerSecond,
    h_constants.coulombConstantCalibration, hq', hm', hl']
  constructor
  · apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 49 / 100)).2
    have hsqrt : (7 / 5 : ℝ) < Real.sqrt 2 := by
      apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 5)).2
      norm_num
    norm_num
    nlinarith
  · apply (Real.sqrt_lt (by positivity)
      (by norm_num : (0 : ℝ) ≤ 50 / 100)).2
    have hsqrt : Real.sqrt 2 < (3 / 2 : ℝ) := by
      apply (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) ≤ 3 / 2)).2
      norm_num
    norm_num
    nlinarith

/-!
The four charged spheres therefore acquire the common energy-derived speed,
approximately `0.49 m/s`; D is the unique nearest displayed answer.

This formalizes `thm:physics:phyx_mini_0864:target`.
-/
theorem problem_phyx_mini_0864
    (setup : FourChargedSphereReleaseSetup)
    (h_data : MatchesProblemAndPrimaryFigure setup)
    (h_geometry : MatchesSquareGeometry setup)
    (h_constants : UsesVacuumCoulombConstant setup)
    (h_physical : HasPhysicalSquareReleaseParameters setup)
    (h_laws : SatisfiesCoulombAndMechanicalEnergyLaws setup)
    (h_far : ReachesVeryFarApartRegime setup)
    (h_symmetry : PreservesSquareReleaseSymmetry setup) :
    (∀ sphere : SphereLabel,
      speedInMetersPerSecond (setup.finalSpeed sphere) =
        energyDerivedSpeedInMetersPerSecond setup) ∧
      IsUniqueClosestDisplayedSpeed setup recordedDatasetAnswer := by
  constructor
  · exact finalSpeed_formula setup h_data h_geometry h_physical h_laws h_far
      h_symmetry
  · intro sphere other hne
    have hb := finalSpeed_numericalBounds setup h_data h_geometry h_constants
      h_physical h_laws h_far h_symmetry sphere
    fin_cases other
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.speedInMetersPerSecond] at hne ⊢
      rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
      linarith
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.speedInMetersPerSecond] at hne ⊢
      rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
      linarith
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.speedInMetersPerSecond] at hne ⊢
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
    · simp [recordedDatasetAnswer] at hne

end PhyXMiniProblems.ProblemPhyXMini0864

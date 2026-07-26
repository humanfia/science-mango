import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0716

open Dimension

/-!
# Separation of the stars in an equal-mass binary system

Two stars, each of mass two nominal solar masses, move on circular orbits of
the same radius `r` about their common center of mass.  The primary figure
labels the stars `1` and `2`, displays the mutually inward forces
`F_(2 on 1)` and `F_(1 on 2)`, and states that their separation is `d = 2r`.
The common orbital period is 90 days.

Masses, durations, lengths, force magnitudes, and Newton's gravitational
constant are represented by unit-independent Physlib quantities.  Real
numbers are used only for readouts in specified units and for the displayed
multiple-choice distances.

Assumption/target split:

* `MatchesPrimaryBinaryStarFigure` records the labels, force-arrow directions,
  circular-orbit geometry, common radius, and the displayed relation `d = 2r`;
* `MatchesBinaryStarScenario` records the 90-day period and two-solar-mass
  value of each star, together with their coherent SI conversions;
* `UsesStandardGravitationalConstant` records the standard SI calibration of
  Newton's gravitational constant;
* `SatisfiesNewtonianCircularOrbitLaws` states inverse-square gravity and the
  centripetal-force law for each star; and
* only the theorems conclude the binary Kepler relation or that the separation
  rounds to `9.3 * 10^10 m` and uniquely selects answer C.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- The physical dimension `L^3 M^-1 T^-2` of Newton's gravitational constant. -/
def gravitationalConstantDimension : Dimension :=
  L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T^-2` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative physical value of Newton's gravitational constant. -/
abbrev GravitationalConstantQuantity : Type :=
  Dimensionful (WithDim gravitationalConstantDimension NNReal)

/-- Unit choices that differ from SI only by measuring mass in nominal solar masses. -/
def nominalSolarMassUnitChoices : UnitChoices :=
  { UnitChoices.SI with mass := MassUnit.nominalSolarMasses }

/-- Unit choices that differ from SI only by measuring time in 24-hour days. -/
def dayUnitChoices : UnitChoices :=
  { UnitChoices.SI with time := TimeUnit.days }

/-- Read a nonnegative dimensionful quantity in the specified coherent units. -/
def nonnegativeReadout {d : Dimension} (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI mass

/-- Nominal-solar-mass readout of a physical mass. -/
def massInNominalSolarMasses (mass : MassQuantity) : ℝ :=
  nonnegativeReadout nominalSolarMassUnitChoices mass

/-- Second readout of a physical duration. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI duration

/-- 24-hour-day readout of a physical duration. -/
def durationInDays (duration : DurationQuantity) : ℝ :=
  nonnegativeReadout dayUnitChoices duration

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI length

/-- Newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI force

/-- SI readout of `G`, in cubic metres per kilogram per second squared. -/
def gravitationalConstantInSI
    (constant : GravitationalConstantQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI constant

/-! ## Stars, force labels, and the primary figure -/

/-- The two stars numbered in the supplied diagram. -/
inductive Star where
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- The two directed force labels printed in the diagram. -/
inductive DirectedForceLabel where
  | starTwoOnStarOne
  | starOneOnStarTwo
  deriving DecidableEq, Fintype, Repr

/-- The star on which a labelled force acts. -/
def DirectedForceLabel.actingStar : DirectedForceLabel → Star
  | .starTwoOnStarOne => .one
  | .starOneOnStarTwo => .two

/-- The star exerting a labelled force. -/
def DirectedForceLabel.exertingStar : DirectedForceLabel → Star
  | .starTwoOnStarOne => .two
  | .starOneOnStarTwo => .one

/-- The force label whose arrow acts on a given star. -/
def forceActingOn : Star → DirectedForceLabel
  | .one => .starTwoOnStarOne
  | .two => .starOneOnStarTwo

/-- Directions available for the mutually attractive force arrows. -/
inductive ForceArrowDirection where
  | towardStarOne
  | towardStarTwo
  deriving DecidableEq, Repr

/-- Direction dictated by attraction for each printed force label. -/
def DirectedForceLabel.inwardDirection : DirectedForceLabel → ForceArrowDirection
  | .starTwoOnStarOne => .towardStarTwo
  | .starOneOnStarTwo => .towardStarOne

/-- The sense of revolution indicated by the tangential arrows in the image. -/
inductive OrbitDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-!
Qualitative evidence transcribed from image `716.png`.  These Boolean fields
record which literal marks and labels are shown; physical radii and distances
are independent quantities in `BinaryStarSystem` below.
-/
structure BinaryStarFigure where
  showsNumberedStar : Star → Bool
  showsCenterOfMassMarker : Bool
  showsCircularOrbit : Star → Bool
  showsRadiusLabelR : Star → Bool
  showsForceArrow : DirectedForceLabel → Bool
  showsForceLabel : DirectedForceLabel → Bool
  forceArrowDirection : DirectedForceLabel → ForceArrowDirection
  orbitDirection : Star → OrbitDirection
  showsSeparationEquationDIsTwoR : Bool

/-!
Independent observables of the binary system.  In particular, `separation`
is not defined from any answer choice, and no numerical separation appears in
this structure.
-/
structure BinaryStarSystem where
  figure : BinaryStarFigure
  mass : Star → MassQuantity
  orbitalPeriod : DurationQuantity
  orbitalRadius : Star → LengthQuantity
  separation : LengthQuantity
  gravitationalConstant : GravitationalConstantQuantity
  mutualForceMagnitude : DirectedForceLabel → ForceMagnitudeQuantity

/-!
Literal image readout and its associated geometry.  The equality `d = 2r` is
printed in the supplied figure.  It is geometric input, not the requested
numerical separation.
-/
structure MatchesPrimaryBinaryStarFigure
    (system : BinaryStarSystem) : Prop where
  bothNumberedStarsShown :
    ∀ star, system.figure.showsNumberedStar star = true
  centerOfMassMarkerShown :
    system.figure.showsCenterOfMassMarker = true
  bothCircularOrbitsShown :
    ∀ star, system.figure.showsCircularOrbit star = true
  bothRadiusLabelsShown :
    ∀ star, system.figure.showsRadiusLabelR star = true
  bothForceArrowsShown :
    ∀ label, system.figure.showsForceArrow label = true
  bothForceLabelsShown :
    ∀ label, system.figure.showsForceLabel label = true
  forceArrowsPointTowardOtherStar :
    ∀ label,
      system.figure.forceArrowDirection label = label.inwardDirection
  bothOrbitsShownCounterclockwise :
    ∀ star, system.figure.orbitDirection star = .counterclockwise
  separationEquationShown :
    system.figure.showsSeparationEquationDIsTwoR = true
  equalOrbitRadii :
    lengthInMeters (system.orbitalRadius .one) =
      lengthInMeters (system.orbitalRadius .two)
  separationIsTwiceOrbitRadius :
    lengthInMeters system.separation =
      2 * lengthInMeters (system.orbitalRadius .one)

/-! ## Scenario data, physical conditions, and governing laws -/

/-!
The numerical data stated in the problem, with coherent SI conversions made
explicit for the later Newtonian calculation.  The value of a nominal solar
mass is the Physlib value `1.988416 * 10^30 kg`.
-/
structure MatchesBinaryStarScenario
    (system : BinaryStarSystem) : Prop where
  periodIsNinetyDays :
    durationInDays system.orbitalPeriod = 90
  periodInSeconds :
    durationInSeconds system.orbitalPeriod = 90 * 24 * 60 * 60
  eachStarHasTwoSolarMasses :
    ∀ star, massInNominalSolarMasses (system.mass star) = 2
  eachStarMassInKilograms :
    ∀ star,
      massInKilograms (system.mass star) = 2 * (1.988416 * 10 ^ 30)

/-- SI calibration of Newton's gravitational constant used in the calculation. -/
structure UsesStandardGravitationalConstant
    (system : BinaryStarSystem) : Prop where
  gravitationalConstantValue :
    gravitationalConstantInSI system.gravitationalConstant =
      6.67430 * 10 ^ (-11 : ℤ)

/-- Nondegeneracy conditions for the Newtonian circular-orbit model. -/
structure HasPhysicalBinaryStarParameters
    (system : BinaryStarSystem) : Prop where
  eachMassPositive :
    ∀ star, 0 < massInKilograms (system.mass star)
  periodPositive :
    0 < durationInSeconds system.orbitalPeriod
  eachRadiusPositive :
    ∀ star, 0 < lengthInMeters (system.orbitalRadius star)
  separationPositive :
    0 < lengthInMeters system.separation
  gravitationalConstantPositive :
    0 < gravitationalConstantInSI system.gravitationalConstant
  eachForceMagnitudePositive :
    ∀ label, 0 < forceInNewtons (system.mutualForceMagnitude label)

/-!
Newtonian laws for the idealized equal-mass circular binary:

* the mutual force has magnitude `G m₁ m₂ / d²`;
* the force on each star supplies `m ω² r`, where `ω = 2π/T`; and
* the two labelled forces form an action-reaction pair.

These are general governing relations involving the independent observable
`d`; no answer choice or numerical value of `d` occurs here.
-/
structure SatisfiesNewtonianCircularOrbitLaws
    (system : BinaryStarSystem) : Prop where
  inverseSquareGravity : ∀ label,
    forceInNewtons (system.mutualForceMagnitude label) =
      gravitationalConstantInSI system.gravitationalConstant *
        massInKilograms (system.mass label.exertingStar) *
        massInKilograms (system.mass label.actingStar) /
        lengthInMeters system.separation ^ 2
  forceSuppliesCentripetalAcceleration : ∀ star,
    forceInNewtons (system.mutualForceMagnitude (forceActingOn star)) =
      massInKilograms (system.mass star) *
        (2 * Real.pi / durationInSeconds system.orbitalPeriod) ^ 2 *
        lengthInMeters (system.orbitalRadius star)
  actionReactionMagnitudesEqual :
    forceInNewtons
        (system.mutualForceMagnitude .starTwoOnStarOne) =
      forceInNewtons
        (system.mutualForceMagnitude .starOneOnStarTwo)

/-! ## Derived binary relation and answer choices -/

/-!
Eliminating the force and orbit radius from the governing laws yields the
two-body form of Kepler's third law for the separation `d`.
-/
theorem binaryStarSeparationCubed
    (system : BinaryStarSystem)
    (h_figure : MatchesPrimaryBinaryStarFigure system)
    (h_physical : HasPhysicalBinaryStarParameters system)
    (h_laws : SatisfiesNewtonianCircularOrbitLaws system) :
    lengthInMeters system.separation ^ 3 =
      gravitationalConstantInSI system.gravitationalConstant *
        (massInKilograms (system.mass .one) +
          massInKilograms (system.mass .two)) *
        durationInSeconds system.orbitalPeriod ^ 2 /
        (4 * Real.pi ^ 2) := by
  let d := lengthInMeters system.separation
  let r₁ := lengthInMeters (system.orbitalRadius .one)
  let r₂ := lengthInMeters (system.orbitalRadius .two)
  let m₁ := massInKilograms (system.mass .one)
  let m₂ := massInKilograms (system.mass .two)
  let T := durationInSeconds system.orbitalPeriod
  let G := gravitationalConstantInSI system.gravitationalConstant
  let f₁ :=
    forceInNewtons
      (system.mutualForceMagnitude .starTwoOnStarOne)
  let f₂ :=
    forceInNewtons
      (system.mutualForceMagnitude .starOneOnStarTwo)
  have hd_pos : 0 < d := by
    simpa [d] using h_physical.separationPositive
  have hr₁_pos : 0 < r₁ := by
    simpa [r₁] using h_physical.eachRadiusPositive .one
  have hr₂_pos : 0 < r₂ := by
    simpa [r₂] using h_physical.eachRadiusPositive .two
  have hm₁_pos : 0 < m₁ := by
    simpa [m₁] using h_physical.eachMassPositive .one
  have hm₂_pos : 0 < m₂ := by
    simpa [m₂] using h_physical.eachMassPositive .two
  have hT_pos : 0 < T := by
    simpa [T] using h_physical.periodPositive
  have hG_pos : 0 < G := by
    simpa [G] using h_physical.gravitationalConstantPositive
  have hradii : r₁ = r₂ := by
    simpa [r₁, r₂] using h_figure.equalOrbitRadii
  have hsep₁ : d = 2 * r₁ := by
    simpa [d, r₁] using h_figure.separationIsTwiceOrbitRadius
  have hsep₂ : d = 2 * r₂ := by
    calc
      d = 2 * r₁ := hsep₁
      _ = 2 * r₂ := by rw [hradii]
  have hgravity₁ :
      f₁ = G * m₂ * m₁ / d ^ 2 := by
    simpa [f₁, G, m₁, m₂, d, DirectedForceLabel.exertingStar,
      DirectedForceLabel.actingStar] using
      h_laws.inverseSquareGravity .starTwoOnStarOne
  have hcentripetal₁ :
      f₁ = m₁ * (2 * Real.pi / T) ^ 2 * r₁ := by
    simpa [f₁, m₁, T, r₁, forceActingOn] using
      h_laws.forceSuppliesCentripetalAcceleration .one
  have hgravity₂ :
      f₂ = G * m₁ * m₂ / d ^ 2 := by
    simpa [f₂, G, m₁, m₂, d, DirectedForceLabel.exertingStar,
      DirectedForceLabel.actingStar] using
      h_laws.inverseSquareGravity .starOneOnStarTwo
  have hcentripetal₂ :
      f₂ = m₂ * (2 * Real.pi / T) ^ 2 * r₂ := by
    simpa [f₂, m₂, T, r₂, forceActingOn] using
      h_laws.forceSuppliesCentripetalAcceleration .two
  have hforce₁ :
      G * m₂ / d ^ 2 = (2 * Real.pi / T) ^ 2 * r₁ := by
    apply mul_left_cancel₀ (ne_of_gt hm₁_pos)
    calc
      m₁ * (G * m₂ / d ^ 2) = G * m₂ * m₁ / d ^ 2 := by ring
      _ = f₁ := hgravity₁.symm
      _ = m₁ * (2 * Real.pi / T) ^ 2 * r₁ := hcentripetal₁
      _ = m₁ * ((2 * Real.pi / T) ^ 2 * r₁) := by ring
  have hforce₂ :
      G * m₁ / d ^ 2 = (2 * Real.pi / T) ^ 2 * r₂ := by
    apply mul_left_cancel₀ (ne_of_gt hm₂_pos)
    calc
      m₂ * (G * m₁ / d ^ 2) = G * m₁ * m₂ / d ^ 2 := by ring
      _ = f₂ := hgravity₂.symm
      _ = m₂ * (2 * Real.pi / T) ^ 2 * r₂ := hcentripetal₂
      _ = m₂ * ((2 * Real.pi / T) ^ 2 * r₂) := by ring
  have hcubic₁ :
      4 * Real.pi ^ 2 * d ^ 3 = 2 * G * m₂ * T ^ 2 := by
    field_simp [ne_of_gt hd_pos, ne_of_gt hT_pos] at hforce₁
    rw [hsep₁] at hforce₁
    rw [hsep₁]
    nlinarith
  have hcubic₂ :
      4 * Real.pi ^ 2 * d ^ 3 = 2 * G * m₁ * T ^ 2 := by
    field_simp [ne_of_gt hd_pos, ne_of_gt hT_pos] at hforce₂
    rw [hsep₂] at hforce₂
    rw [hsep₂]
    nlinarith
  field_simp [Real.pi_ne_zero]
  nlinarith

/-- Labels of the four displayed multiple-choice distances. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Distance in metres printed beside each answer choice. -/
def AnswerChoice.distanceInMeters : AnswerChoice → ℝ
  | .A => 83 * 10 ^ 9
  | .B => 93 * 10 ^ 8
  | .C => 93 * 10 ^ 9
  | .D => 103 * 10 ^ 9

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The physical separation rounds to the displayed answer at its stated
precision of one billion metres (half-width `5 * 10^8 m`).
-/
def RoundsToDisplayedDistance
    (system : BinaryStarSystem) (choice : AnswerChoice) : Prop :=
  |lengthInMeters system.separation - choice.distanceInMeters| < 5 * 10 ^ 8

/-- The selected displayed distance is strictly nearer than every other choice. -/
def IsUniqueClosestAnswer
    (system : BinaryStarSystem) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |lengthInMeters system.separation - choice.distanceInMeters| <
      |lengthInMeters system.separation - other.distanceInMeters|

/-!
Using the 90-day period, two nominal solar masses per star, Newton's constant,
the figure relation `d = 2r`, and circular Newtonian dynamics, the separation
rounds to `9.3 * 10^10 m`.  This is uniquely answer C.

This declaration corresponds to blueprint label
`thm:physics:phyx_mini_0716:target`.
-/
theorem problem_phyx_mini_0716
    (system : BinaryStarSystem)
    (h_figure : MatchesPrimaryBinaryStarFigure system)
    (h_scenario : MatchesBinaryStarScenario system)
    (h_constant : UsesStandardGravitationalConstant system)
    (h_physical : HasPhysicalBinaryStarParameters system)
    (h_laws : SatisfiesNewtonianCircularOrbitLaws system) :
    RoundsToDisplayedDistance system recordedAnswerChoice ∧
      IsUniqueClosestAnswer system recordedAnswerChoice := by
  let d := lengthInMeters system.separation
  have hd_pos : 0 < d := by
    simpa [d] using h_physical.separationPositive
  have hcubic :=
    binaryStarSeparationCubed system h_figure h_physical h_laws
  rw [h_constant.gravitationalConstantValue,
    h_scenario.eachStarMassInKilograms .one,
    h_scenario.eachStarMassInKilograms .two,
    h_scenario.periodInSeconds] at hcubic
  norm_num at hcubic
  change d ^ 3 =
    32098553961665789952000000000000000 / (4 * Real.pi ^ 2) at hcubic
  field_simp [Real.pi_ne_zero] at hcubic
  have hpi_sq_upper :
      Real.pi ^ 2 < (3141593 / 1000000 : ℝ) ^ 2 := by
    have hdecimal :=
      pow_lt_pow_left₀ (n := 2) Real.pi_lt_d6 Real.pi_pos.le
        (by norm_num)
    norm_num at hdecimal ⊢
    exact hdecimal
  have hpi_sq_lower :
      (3141592 / 1000000 : ℝ) ^ 2 < Real.pi ^ 2 := by
    have hdecimal :=
      pow_lt_pow_left₀ (n := 2) Real.pi_gt_d6 (by norm_num)
        (by norm_num)
    norm_num at hdecimal ⊢
    exact hdecimal
  have hden_pos : 0 < 4 * Real.pi ^ 2 := by positivity
  have hcubic_at_lower :
      (92500000000 : ℝ) ^ 3 * (4 * Real.pi ^ 2) <
        32098553961665789952000000000000000 := by
    nlinarith [hpi_sq_upper]
  have hcubic_at_upper :
      32098553961665789952000000000000000 <
        (93500000000 : ℝ) ^ 3 * (4 * Real.pi ^ 2) := by
    nlinarith [hpi_sq_lower]
  have hlower_cube : (92500000000 : ℝ) ^ 3 < d ^ 3 := by
    exact lt_of_mul_lt_mul_right (by
      calc
        (92500000000 : ℝ) ^ 3 * (4 * Real.pi ^ 2) <
            32098553961665789952000000000000000 := hcubic_at_lower
        _ = d ^ 3 * (4 * Real.pi ^ 2) := by nlinarith [hcubic])
      hden_pos.le
  have hupper_cube : d ^ 3 < (93500000000 : ℝ) ^ 3 := by
    exact lt_of_mul_lt_mul_right (by
      calc
        d ^ 3 * (4 * Real.pi ^ 2) =
            32098553961665789952000000000000000 := by nlinarith [hcubic]
        _ < (93500000000 : ℝ) ^ 3 * (4 * Real.pi ^ 2) :=
          hcubic_at_upper)
      hden_pos.le
  have hd_lower : (92500000000 : ℝ) < d := by
    exact (pow_lt_pow_iff_left₀ (by norm_num) hd_pos.le
      (by norm_num : (3 : ℕ) ≠ 0)).mp hlower_cube
  have hd_upper : d < (93500000000 : ℝ) := by
    exact (pow_lt_pow_iff_left₀ hd_pos.le (by norm_num)
      (by norm_num : (3 : ℕ) ≠ 0)).mp hupper_cube
  have hround : |d - 93000000000| < (500000000 : ℝ) := by
    rw [abs_lt]
    constructor <;> nlinarith
  constructor
  · norm_num [RoundsToDisplayedDistance, recordedAnswerChoice,
      AnswerChoice.distanceInMeters]
    simpa [d] using hround
  · unfold IsUniqueClosestAnswer
    intro other hne
    cases other with
    | A =>
        norm_num [recordedAnswerChoice, AnswerChoice.distanceInMeters]
        change |d - 93000000000| < |d - 83000000000|
        have hsign : 0 < d - (83000000000 : ℝ) := by nlinarith
        rw [abs_of_pos hsign, abs_lt]
        constructor <;> nlinarith
    | B =>
        norm_num [recordedAnswerChoice, AnswerChoice.distanceInMeters]
        change |d - 93000000000| < |d - 9300000000|
        have hsign : 0 < d - (9300000000 : ℝ) := by nlinarith
        rw [abs_of_pos hsign, abs_lt]
        constructor <;> nlinarith
    | C =>
        exact (hne rfl).elim
    | D =>
        norm_num [recordedAnswerChoice, AnswerChoice.distanceInMeters]
        change |d - 93000000000| < |d - 103000000000|
        have hsign : d - (103000000000 : ℝ) < 0 := by nlinarith
        rw [abs_of_neg hsign, abs_lt]
        constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0716

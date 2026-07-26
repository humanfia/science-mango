import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0551

open Dimension

/-!
# Total kinetic energy in spontaneous uranium decay

A uranium atom initially at rest decays into a helium atom and a thorium atom.
The primary figure places the uranium atom at the origin before decay, then
shows thorium recoiling along negative `x` and helium moving along positive
`x`.  The helium speed is measured as `1.423 * 10^7 m/s`.

Masses, signed axial velocities, and energies are represented by
unit-independent Physlib quantities.  Real numbers are used only for named-unit
readouts, raster metadata, and the numerical values printed with the answer
choices.

Assumption/target boundary:

* `MatchesUraniumDecayReadouts` contains only the three stated masses, the
  initially stationary parent, and the observed helium velocity.
* `MatchesSuppliedUraniumDecayFigure` records the labels, axes, locations, and
  velocity-arrow directions visible in image `551.png`.
* `SatisfiesFigureVelocityDirectionConvention` connects the displayed arrow
  directions to signs of physical axial velocity.
* `SatisfiesDecayMomentumConservation` and
  `SatisfiesNonrelativisticKineticEnergyLaws` state the governing physics.
* There are no previous-part results.  The thorium recoil velocity, total
  kinetic energy, rounding to `6.844 * 10^-13 J`, and choice `D` occur only as
  conclusions below.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed one-dimensional physical velocity along the decay axis. -/
abbrev SignedAxialVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A signed physical energy; kinetic energies are constrained to be nonnegative. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a signed axial velocity in coherent selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedAxialVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read an energy in the coherent unit determined by the selected base units. -/
def energyReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (energy : EnergyQuantity) : ℝ :=
  (energy {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre-per-second readout of a signed axial velocity. -/
def velocityInMetersPerSecond
    (velocity : SignedAxialVelocityQuantity) : ℝ :=
  velocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds energy

/-! ## Atom identities, decay geometry, and primary-figure evidence -/

/-- The three atom labels in the physical process and its figure. -/
inductive AtomSpecies where
  | uranium
  | helium
  | thorium
  deriving DecidableEq, Fintype, Repr

/-- The two products of the spontaneous decay. -/
inductive DecayProduct where
  | helium
  | thorium
  deriving DecidableEq, Fintype, Repr

/-- Regard a decay product as its corresponding atom species. -/
def DecayProduct.atomSpecies : DecayProduct → AtomSpecies
  | .helium => .helium
  | .thorium => .thorium

/-- The coordinate axes drawn in both panels of the source image. -/
inductive CoordinateAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- The states shown above and below the horizontal divider in the image. -/
inductive FigurePanel where
  | beforeDecay
  | afterDecay
  deriving DecidableEq, Fintype, Repr

/-- Qualitative horizontal locations relative to the drawn coordinate origin. -/
inductive HorizontalLocation where
  | negativeX
  | origin
  | positiveX
  deriving DecidableEq, Repr

/-- Directions of the two post-decay velocity arrows. -/
inductive HorizontalDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- The physical decay classification stated in the scenario. -/
inductive DecayMode where
  | spontaneousTwoBodyAlphaDecay
  | other
  deriving DecidableEq, Repr

/-!
Qualitative and raster evidence extracted from the supplied primary image.
There is no quantitative energy or unobserved thorium speed in this structure.
-/
structure UraniumDecayFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  horizontalPanelDividerShown : Bool
  axisShown : FigurePanel → CoordinateAxis → Bool
  atomShown : FigurePanel → AtomSpecies → Bool
  atomLabelShown : FigurePanel → AtomSpecies → Bool
  atomHorizontalLocation : FigurePanel → AtomSpecies → HorizontalLocation
  velocityArrowShown : DecayProduct → Bool
  velocityPrimeLabelShown : DecayProduct → Bool
  velocityArrowDirection : DecayProduct → HorizontalDirection

/-!
All independent physical quantities in the modeled event.  In particular,
the thorium velocity, both daughter kinetic energies, and their total are
unconstrained fields until the governing laws are supplied; none is defined
from an answer choice.
-/
structure UraniumDecaySetup where
  decayMode : DecayMode
  decayAxis : CoordinateAxis
  uraniumMass : MassQuantity
  daughterMass : DecayProduct → MassQuantity
  uraniumVelocityBeforeDecay : SignedAxialVelocityQuantity
  daughterVelocityAfterDecay : DecayProduct → SignedAxialVelocityQuantity
  daughterKineticEnergyAfterDecay : DecayProduct → EnergyQuantity
  totalKineticEnergyAfterDecay : EnergyQuantity
  figure : UraniumDecayFigure

/-! ## Scenario, measured data, figure readouts, and governing laws -/

/-- The qualitative spontaneous, one-dimensional decay scenario. -/
structure MatchesUraniumDecayScenario (setup : UraniumDecaySetup) : Prop where
  spontaneousAlphaDecay :
    setup.decayMode = .spontaneousTwoBodyAlphaDecay
  motionAlongXAxis : setup.decayAxis = .x

/-!
The three stated masses, the initially stationary uranium atom, and the
observed signed helium velocity.  No thorium velocity or energy is assumed.
-/
structure MatchesUraniumDecayReadouts (setup : UraniumDecaySetup) : Prop where
  uraniumMassKilograms :
    massInKilograms setup.uraniumMass = 3.9529e-25
  heliumMassKilograms :
    massInKilograms (setup.daughterMass .helium) = 6.6465e-27
  thoriumMassKilograms :
    massInKilograms (setup.daughterMass .thorium) = 3.8864e-25
  uraniumInitiallyAtRest :
    velocityInMetersPerSecond setup.uraniumVelocityBeforeDecay = 0
  observedHeliumVelocityMetersPerSecond :
    velocityInMetersPerSecond
      (setup.daughterVelocityAfterDecay .helium) = 1.423e7

/-- Positivity and nonnegativity conditions selecting the physical branch. -/
structure HasPhysicalUraniumDecayParameters
    (setup : UraniumDecaySetup) : Prop where
  uraniumMassPositive : 0 < massInKilograms setup.uraniumMass
  daughterMassPositive :
    ∀ product, 0 < massInKilograms (setup.daughterMass product)
  daughterKineticEnergyNonnegative :
    ∀ product,
      0 ≤ energyInJoules (setup.daughterKineticEnergyAfterDecay product)
  totalKineticEnergyNonnegative :
    0 ≤ energyInJoules setup.totalKineticEnergyAfterDecay

/-!
Visible contents of the `430 × 400` source raster.  The uranium atom occupies
the origin in the upper panel.  In the lower panel, thorium lies to the left
and helium to the right, with arrows labeled `v'_Th` and `v'_He` pointing in
the corresponding directions.
-/
structure MatchesSuppliedUraniumDecayFigure
    (figure : UraniumDecayFigure) : Prop where
  rasterWidth : figure.rasterWidthPixels = 430
  rasterHeight : figure.rasterHeightPixels = 400
  panelDividerVisible : figure.horizontalPanelDividerShown = true
  bothAxesShown :
    ∀ panel axis, figure.axisShown panel axis = true
  uraniumShownBefore : figure.atomShown .beforeDecay .uranium = true
  uraniumLabelShownBefore :
    figure.atomLabelShown .beforeDecay .uranium = true
  uraniumAtOriginBefore :
    figure.atomHorizontalLocation .beforeDecay .uranium = .origin
  noHeliumBefore : figure.atomShown .beforeDecay .helium = false
  noThoriumBefore : figure.atomShown .beforeDecay .thorium = false
  noUraniumAfter : figure.atomShown .afterDecay .uranium = false
  heliumShownAfter : figure.atomShown .afterDecay .helium = true
  thoriumShownAfter : figure.atomShown .afterDecay .thorium = true
  heliumLabelShownAfter :
    figure.atomLabelShown .afterDecay .helium = true
  thoriumLabelShownAfter :
    figure.atomLabelShown .afterDecay .thorium = true
  heliumRightOfOrigin :
    figure.atomHorizontalLocation .afterDecay .helium = .positiveX
  thoriumLeftOfOrigin :
    figure.atomHorizontalLocation .afterDecay .thorium = .negativeX
  bothVelocityArrowsShown :
    ∀ product, figure.velocityArrowShown product = true
  bothPrimeVelocityLabelsShown :
    ∀ product, figure.velocityPrimeLabelShown product = true
  heliumArrowPointsPositiveX :
    figure.velocityArrowDirection .helium = .positiveX
  thoriumArrowPointsNegativeX :
    figure.velocityArrowDirection .thorium = .negativeX

/-!
The conventional interpretation of each displayed velocity arrow.  It links
qualitative figure direction to the sign of a physical velocity but supplies
neither the thorium speed magnitude nor any energy.
-/
structure SatisfiesFigureVelocityDirectionConvention
    (setup : UraniumDecaySetup) : Prop where
  arrowDirectionAgreesWithVelocitySign :
    ∀ product,
      match setup.figure.velocityArrowDirection product with
      | .negativeX =>
          velocityInMetersPerSecond
            (setup.daughterVelocityAfterDecay product) < 0
      | .positiveX =>
          0 < velocityInMetersPerSecond
            (setup.daughterVelocityAfterDecay product)

/-!
One-dimensional linear momentum conservation for the isolated two-body decay,
stated in every coherent choice of mass, length, and time units.  The parent
term is retained explicitly so the initially-at-rest datum remains separate.
-/
structure SatisfiesDecayMomentumConservation
    (setup : UraniumDecaySetup) : Prop where
  momentumBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.uraniumMass *
          velocityReadout lengthUnit timeUnit
            setup.uraniumVelocityBeforeDecay =
        massReadout massUnit (setup.daughterMass .helium) *
            velocityReadout lengthUnit timeUnit
              (setup.daughterVelocityAfterDecay .helium) +
          massReadout massUnit (setup.daughterMass .thorium) *
            velocityReadout lengthUnit timeUnit
              (setup.daughterVelocityAfterDecay .thorium)

/-!
The nonrelativistic translational kinetic-energy law for each daughter and the
additivity of their total kinetic energy.  These are general governing laws;
they contain no measured or displayed numerical energy.
-/
structure SatisfiesNonrelativisticKineticEnergyLaws
    (setup : UraniumDecaySetup) : Prop where
  daughterKineticEnergy :
    ∀ (product : DecayProduct) (massUnit : MassUnit)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      energyReadout massUnit lengthUnit timeUnit
          (setup.daughterKineticEnergyAfterDecay product) =
        (1 / 2 : ℝ) * massReadout massUnit (setup.daughterMass product) *
          velocityReadout lengthUnit timeUnit
              (setup.daughterVelocityAfterDecay product) ^ 2
  totalKineticEnergyIsSum :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      energyReadout massUnit lengthUnit timeUnit
          setup.totalKineticEnergyAfterDecay =
        energyReadout massUnit lengthUnit timeUnit
            (setup.daughterKineticEnergyAfterDecay .helium) +
          energyReadout massUnit lengthUnit timeUnit
            (setup.daughterKineticEnergyAfterDecay .thorium)

/-! ## Derived relations and displayed answer -/

/-!
Momentum conservation determines the signed thorium recoil velocity.  This is
a derived conclusion and is not a premise of the main theorem.
-/
lemma thorium_recoil_velocity_exact
    (setup : UraniumDecaySetup)
    (_readouts : MatchesUraniumDecayReadouts setup)
    (_physical : HasPhysicalUraniumDecayParameters setup)
    (_momentum : SatisfiesDecayMomentumConservation setup) :
    velocityInMetersPerSecond
        (setup.daughterVelocityAfterDecay .thorium) =
      -(massInKilograms (setup.daughterMass .helium) *
          velocityInMetersPerSecond
            (setup.daughterVelocityAfterDecay .helium)) /
        massInKilograms (setup.daughterMass .thorium) := by
  have hmomentum :
      massInKilograms setup.uraniumMass *
          velocityInMetersPerSecond setup.uraniumVelocityBeforeDecay =
        massInKilograms (setup.daughterMass .helium) *
            velocityInMetersPerSecond
              (setup.daughterVelocityAfterDecay .helium) +
          massInKilograms (setup.daughterMass .thorium) *
            velocityInMetersPerSecond
              (setup.daughterVelocityAfterDecay .thorium) := by
    simpa [massInKilograms, velocityInMetersPerSecond] using
      _momentum.momentumBalance
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  rw [_readouts.uraniumInitiallyAtRest, mul_zero] at hmomentum
  have hmTh : massInKilograms (setup.daughterMass .thorium) ≠ 0 :=
    ne_of_gt (_physical.daughterMassPositive .thorium)
  apply (eq_div_iff hmTh).2
  nlinarith [hmomentum]

/-!
Substituting the recoil relation into `K = m v² / 2` gives an exact SI formula
for the total daughter kinetic energy before numerical rounding.
-/
lemma total_kinetic_energy_exact
    (setup : UraniumDecaySetup)
    (_readouts : MatchesUraniumDecayReadouts setup)
    (_physical : HasPhysicalUraniumDecayParameters setup)
    (_momentum : SatisfiesDecayMomentumConservation setup)
    (_kinetic : SatisfiesNonrelativisticKineticEnergyLaws setup) :
    energyInJoules setup.totalKineticEnergyAfterDecay =
      (1 / 2 : ℝ) * massInKilograms (setup.daughterMass .helium) *
          velocityInMetersPerSecond
              (setup.daughterVelocityAfterDecay .helium) ^ 2 +
        (1 / 2 : ℝ) * massInKilograms (setup.daughterMass .thorium) *
          (-(massInKilograms (setup.daughterMass .helium) *
                velocityInMetersPerSecond
                  (setup.daughterVelocityAfterDecay .helium)) /
            massInKilograms (setup.daughterMass .thorium)) ^ 2 := by
  have hsum :
      energyInJoules setup.totalKineticEnergyAfterDecay =
        energyInJoules
            (setup.daughterKineticEnergyAfterDecay .helium) +
          energyInJoules
            (setup.daughterKineticEnergyAfterDecay .thorium) := by
    simpa [energyInJoules] using
      _kinetic.totalKineticEnergyIsSum
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hHe :
      energyInJoules
          (setup.daughterKineticEnergyAfterDecay .helium) =
        (1 / 2 : ℝ) *
            massInKilograms (setup.daughterMass .helium) *
          velocityInMetersPerSecond
              (setup.daughterVelocityAfterDecay .helium) ^ 2 := by
    simpa [energyInJoules, massInKilograms,
      velocityInMetersPerSecond] using
      _kinetic.daughterKineticEnergy .helium
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hTh :
      energyInJoules
          (setup.daughterKineticEnergyAfterDecay .thorium) =
        (1 / 2 : ℝ) *
            massInKilograms (setup.daughterMass .thorium) *
          velocityInMetersPerSecond
              (setup.daughterVelocityAfterDecay .thorium) ^ 2 := by
    simpa [energyInJoules, massInKilograms,
      velocityInMetersPerSecond] using
      _kinetic.daughterKineticEnergy .thorium
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  rw [hsum, hHe, hTh,
    thorium_recoil_velocity_exact setup _readouts _physical _momentum]

/-- Labels printed beside the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Total kinetic energy printed beside each answer label, in joules. -/
def AnswerChoice.energyInJoules : AnswerChoice → ℝ
  | .A => 6.09e-13
  | .B => 5.992e-13
  | .C => 7.231e-13
  | .D => 6.844e-13

/-- The answer label recorded in the source dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A displayed choice is uniquely closest to the physical total-energy readout.
This is a target-side comparison, not an assumed law or data calibration.
-/
def IsUniqueClosestDisplayedEnergy
    (setup : UraniumDecaySetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |energyInJoules setup.totalKineticEnergyAfterDecay -
        choice.energyInJoules| <
      |energyInJoules setup.totalKineticEnergyAfterDecay -
        other.energyInJoules|

/-!
The data and governing laws give
`6.844430194... * 10^-13 J`, which rounds to the displayed
`6.844 * 10^-13 J` and makes choice `D` uniquely closest.  Half a unit in the
last displayed digit is `5 * 10^-17 J`.

This formalizes `thm:physics:phyx_mini_0551:target`.  Neither the rounding
bound nor the choice comparison occurs in any assumption-side structure.
-/
theorem problem_phyx_mini_0551
    (setup : UraniumDecaySetup)
    (_scenario : MatchesUraniumDecayScenario setup)
    (_readouts : MatchesUraniumDecayReadouts setup)
    (_physical : HasPhysicalUraniumDecayParameters setup)
    (_figure : MatchesSuppliedUraniumDecayFigure setup.figure)
    (_direction : SatisfiesFigureVelocityDirectionConvention setup)
    (_momentum : SatisfiesDecayMomentumConservation setup)
    (_kinetic : SatisfiesNonrelativisticKineticEnergyLaws setup) :
    |energyInJoules setup.totalKineticEnergyAfterDecay - 6.844e-13| ≤
        5e-17 ∧
      IsUniqueClosestDisplayedEnergy setup .D := by
  have henergy :=
    total_kinetic_energy_exact
      setup _readouts _physical _momentum _kinetic
  norm_num [_readouts.heliumMassKilograms,
    _readouts.thoriumMassKilograms,
    _readouts.observedHeliumVelocityMetersPerSecond] at henergy
  constructor
  · rw [henergy]
    norm_num [abs_le]
  · intro other hother
    simp only [henergy]
    cases other with
    | A => norm_num [AnswerChoice.energyInJoules]
    | B => norm_num [AnswerChoice.energyInJoules]
    | C => norm_num [AnswerChoice.energyInJoules]
    | D => exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0551

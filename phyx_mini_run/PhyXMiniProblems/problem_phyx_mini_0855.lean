import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Energy

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0855

open Dimension

/-!
# Electrostatic potential energy of three positive point charges

The primary figure places positive charges of `2.0 nC`, `3.0 nC`, and
`3.0 nC` at the top-left, top-right, and bottom-left vertices of a right
triangle.  The two perpendicular sides are `3.0 cm` and `4.0 cm`; hence the
unlabelled diagonal separation is `5.0 cm`.

Charges, separations, Coulomb's constant, and potential energy below are
unit-independent Physlib dimensional quantities.  Real numbers occur only as
explicit coherent-SI readouts, figure coordinates measured in metres, and
values transcribed from the answer table.

Assumption/target split:

* governing laws: metric separation agrees with the displayed planar
  positions, Physlib's Coulomb constant agrees with its dimensionful SI
  readout, and the energy is the sum of the three unordered pair energies;
* previous-part results: none;
* figure/data readouts: three positive signs, charge labels `2`, `3`, `3 nC`,
  perpendicular positions, and side labels `3`, `4 cm`;
* current target conclusions: the missing separation is `5 cm`, the pairwise
  factor is `53 / 10^17 C^2/m`, and the potential energy is
  `47647 / 10^10 J = 4.7647 * 10^-6 J`, so it is positive and matches none of
  the literal displayed choices.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A signed, unit-independent electric charge. -/
abbrev ChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent physical separation. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- The physical dimension `M L^3 T^-2 C^-2` of Coulomb's constant. -/
def coulombConstantDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent Coulomb constant. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- The affine plane used for the metre-coordinate readouts in the figure. -/
abbrev FigurePlane : Type := Space 2

/-- Read a physical charge in coherent SI coulombs. -/
def chargeInCoulombs (charge : ChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a physical charge in nanocoulombs. -/
def chargeInNanocoulombs (charge : ChargeQuantity) : ℝ :=
  chargeInCoulombs charge * (10 : ℝ) ^ 9

/-- Read a physical separation in coherent SI metres. -/
def separationInMeters (separation : LengthQuantity) : ℝ :=
  ((separation UnitChoices.SI).val : ℝ)

/-- Read a physical separation in centimetres. -/
def separationInCentimeters (separation : LengthQuantity) : ℝ :=
  separationInMeters separation * 100

/-- Read Coulomb's constant in `N m^2 / C^2 = J m / C^2`. -/
def coulombConstantInNewtonSquareMetersPerSquareCoulomb
    (constant : CoulombConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Read electrostatic potential energy in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Primary-figure labels and physical setup -/

/-- The three charge locations identifiable in the supplied image. -/
inductive ChargeSite where
  | topLeft
  | topRight
  | bottomLeft
  deriving DecidableEq, Fintype, Repr

/-- The two dotted, dimension-labelled sides drawn in the image. -/
inductive LabelledSide where
  | topHorizontal
  | leftVertical
  deriving DecidableEq, Fintype, Repr

/-!
Literal evidence carried by the primary raster.  Its scalar labels are kept
separate from the physical quantities in the setup.
-/
structure ThreeChargeFigure where
  showsCharge : ChargeSite → Bool
  showsPositiveSign : ChargeSite → Bool
  chargeLabelNanocoulombs : ChargeSite → ℝ
  separationLabelCentimeters : LabelledSide → ℝ
  sideIsDotted : LabelledSide → Bool
  topLeftIsRightAngleVertex : Bool

/-- The material environment in which the electrostatic interaction occurs. -/
inductive AmbientMedium where
  | vacuum
  | other
  deriving DecidableEq, Repr

/-- Reference configuration used to assign electrostatic potential energy. -/
inductive PotentialEnergyReference where
  | infinitelySeparatedCharges
  | other
  deriving DecidableEq, Repr

/-!
Independent physical quantities for the three-charge configuration.  The
potential energy is an observable field and is not defined from the requested
numeric answer.
-/
structure ThreePointChargeSetup where
  charge : ChargeSite → ChargeQuantity
  positionInMeters : ChargeSite → FigurePlane
  separation : ChargeSite → ChargeSite → LengthQuantity
  electrostaticPotentialEnergy : DimEnergy
  coulombConstant : CoulombConstantQuantity
  vacuumElectromagnetism : Electromagnetism.EMSystem
  ambientMedium : AmbientMedium
  energyReference : PotentialEnergyReference
  chargesArePointlike : Bool
  configurationIsStatic : Bool
  figure : ThreeChargeFigure

/-!
Numerical and qualitative information read directly from image `855.png`.
The coordinate origin is chosen at the top-left charge, the positive
horizontal axis points right, and the positive vertical axis points up.
The unprinted diagonal distance and the electrostatic energy do not occur in
this structure.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : ThreePointChargeSetup) : Prop where
  everyChargeIsShown : ∀ site, setup.figure.showsCharge site = true
  everyChargeHasPositiveSign :
    ∀ site, setup.figure.showsPositiveSign site = true
  topLeftChargeLabel :
    setup.figure.chargeLabelNanocoulombs .topLeft = 2
  topRightChargeLabel :
    setup.figure.chargeLabelNanocoulombs .topRight = 3
  bottomLeftChargeLabel :
    setup.figure.chargeLabelNanocoulombs .bottomLeft = 3
  physicalChargesMatchLabels : ∀ site,
    chargeInNanocoulombs (setup.charge site) =
      setup.figure.chargeLabelNanocoulombs site
  topHorizontalLabel :
    setup.figure.separationLabelCentimeters .topHorizontal = 3
  leftVerticalLabel :
    setup.figure.separationLabelCentimeters .leftVertical = 4
  bothLabelledSidesAreDotted :
    ∀ side, setup.figure.sideIsDotted side = true
  rightAngleAtTopLeft : setup.figure.topLeftIsRightAngleVertex = true
  topLeftPosition : setup.positionInMeters .topLeft = ⟨![0, 0]⟩
  topRightPosition :
    setup.positionInMeters .topRight = ⟨![(3 : ℝ) / 100, 0]⟩
  bottomLeftPosition :
    setup.positionInMeters .bottomLeft = ⟨![0, -(4 : ℝ) / 100]⟩
  topSeparationMatchesLabel :
    separationInCentimeters
        (setup.separation .topLeft .topRight) =
      setup.figure.separationLabelCentimeters .topHorizontal
  leftSeparationMatchesLabel :
    separationInCentimeters
        (setup.separation .topLeft .bottomLeft) =
      setup.figure.separationLabelCentimeters .leftVertical
  mediumIsVacuum : setup.ambientMedium = .vacuum
  referenceIsInfiniteSeparation :
    setup.energyReference = .infinitelySeparatedCharges
  pointChargeModel : setup.chargesArePointlike = true
  staticConfiguration : setup.configurationIsStatic = true

/-- Positivity and nondegeneracy conditions for the physical configuration. -/
structure HasPhysicalThreeChargeParameters
    (setup : ThreePointChargeSetup) : Prop where
  everyDisplayedChargeIsPositive :
    ∀ site, 0 < chargeInCoulombs (setup.charge site)
  distinctSitesHavePositiveSeparation :
    ∀ first second, first ≠ second →
      0 < separationInMeters (setup.separation first second)
  coulombConstantPositive :
    0 < coulombConstantInNewtonSquareMetersPerSquareCoulomb
      setup.coulombConstant
  vacuumPermittivityPositive : 0 < setup.vacuumElectromagnetism.ε₀

/-! ## Governing geometry and electrostatic laws -/

/-!
Each dimensionful pair separation has the same metre readout as the metric
distance between the corresponding plotted positions.  This generic geometry
law does not assume the unlabelled `5 cm` diagonal.
-/
structure SatisfiesDepictedSeparationGeometry
    (setup : ThreePointChargeSetup) : Prop where
  separationAgreesWithMetricDistance : ∀ first second,
    separationInMeters (setup.separation first second) =
      dist (setup.positionInMeters first) (setup.positionInMeters second)

/-!
The dimensionful constant is calibrated against Physlib's definition
`1 / (4 pi epsilon_0)`, and that real readout uses the conventional
`8.99 * 10^9 N m^2 / C^2` textbook approximation.  This is universal
calibration data, not a conclusion about the current charge configuration.
-/
structure UsesTextbookVacuumCoulombConstant
    (setup : ThreePointChargeSetup) : Prop where
  dimensionfulReadoutAgreesWithPhyslib :
    coulombConstantInNewtonSquareMetersPerSquareCoulomb
        setup.coulombConstant =
      setup.vacuumElectromagnetism.coulombConstant
  calibratedPhyslibReadout :
    setup.vacuumElectromagnetism.coulombConstant = 8990000000

/-!
For point charges in vacuum with zero potential energy at infinite
separation, the total energy is the sum over the three unordered pairs,
`k q_i q_j / r_ij`.  The field is a governing law and contains no numeric
answer or answer-choice label.
-/
structure SatisfiesThreePointChargeElectrostaticEnergyLaw
    (setup : ThreePointChargeSetup) : Prop where
  pairwiseCoulombEnergySum :
    energyInJoules setup.electrostaticPotentialEnergy =
      coulombConstantInNewtonSquareMetersPerSquareCoulomb
          setup.coulombConstant *
        (chargeInCoulombs (setup.charge .topLeft) *
              chargeInCoulombs (setup.charge .topRight) /
            separationInMeters
              (setup.separation .topLeft .topRight) +
          chargeInCoulombs (setup.charge .topLeft) *
              chargeInCoulombs (setup.charge .bottomLeft) /
            separationInMeters
              (setup.separation .topLeft .bottomLeft) +
          chargeInCoulombs (setup.charge .topRight) *
              chargeInCoulombs (setup.charge .bottomLeft) /
            separationInMeters
              (setup.separation .topRight .bottomLeft))

/-! ## Derived geometric and energetic conclusions -/

/-- The unlabelled hypotenuse of the depicted `3-4-5` triangle is `5 cm`. -/
lemma diagonalSeparationInCentimeters
    (setup : ThreePointChargeSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_geometry : SatisfiesDepictedSeparationGeometry setup) :
    separationInCentimeters
      (setup.separation .topRight .bottomLeft) = 5 := by
  rw [separationInCentimeters,
    h_geometry.separationAgreesWithMetricDistance,
    h_figure.topRightPosition, h_figure.bottomLeftPosition]
  rw [Space.dist_eq]
  norm_num [Fin.sum_univ_two]

/-!
After substituting the three charges and the `3`, `4`, `5 cm` separations, the
sum of `q_i q_j / r_ij` is exactly `53 / 10^17 C^2/m`.
-/
lemma pairwiseChargeDistanceFactor
    (setup : ThreePointChargeSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_geometry : SatisfiesDepictedSeparationGeometry setup) :
    chargeInCoulombs (setup.charge .topLeft) *
          chargeInCoulombs (setup.charge .topRight) /
        separationInMeters (setup.separation .topLeft .topRight) +
      chargeInCoulombs (setup.charge .topLeft) *
          chargeInCoulombs (setup.charge .bottomLeft) /
        separationInMeters (setup.separation .topLeft .bottomLeft) +
      chargeInCoulombs (setup.charge .topRight) *
          chargeInCoulombs (setup.charge .bottomLeft) /
        separationInMeters (setup.separation .topRight .bottomLeft) =
      53 / (10 : ℝ) ^ 17 := by
  have h_q_tl := h_figure.physicalChargesMatchLabels .topLeft
  rw [h_figure.topLeftChargeLabel] at h_q_tl
  have h_q_tr := h_figure.physicalChargesMatchLabels .topRight
  rw [h_figure.topRightChargeLabel] at h_q_tr
  have h_q_bl := h_figure.physicalChargesMatchLabels .bottomLeft
  rw [h_figure.bottomLeftChargeLabel] at h_q_bl
  have h_r_top := h_figure.topSeparationMatchesLabel
  rw [h_figure.topHorizontalLabel] at h_r_top
  have h_r_left := h_figure.leftSeparationMatchesLabel
  rw [h_figure.leftVerticalLabel] at h_r_left
  have h_r_diag :=
    diagonalSeparationInCentimeters setup h_figure h_geometry
  simp only [chargeInNanocoulombs] at h_q_tl h_q_tr h_q_bl
  simp only [separationInCentimeters] at h_r_top h_r_left h_r_diag
  rw [show chargeInCoulombs (setup.charge .topLeft) = 2 / 10^9 by
        linarith,
    show chargeInCoulombs (setup.charge .topRight) = 3 / 10^9 by
      linarith,
    show chargeInCoulombs (setup.charge .bottomLeft) = 3 / 10^9 by
      linarith,
    show separationInMeters
        (setup.separation .topLeft .topRight) = 3 / 100 by
      linarith,
    show separationInMeters
        (setup.separation .topLeft .bottomLeft) = 4 / 100 by
      linarith,
    show separationInMeters
        (setup.separation .topRight .bottomLeft) = 5 / 100 by
      linarith]
  norm_num

/-! ## Literal answer table and recorded metadata -/

/-- The answer labels supplied with the dataset item. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Literal energy in joules printed beside each answer label.  These values are
source metadata and do not constrain the independent physical energy field.
-/
def displayedEnergyInJoules : AnswerChoice → ℝ
  | .A => (6 / 5) * (10 : ℝ) ^ 19
  | .B => -(6 / 5) * (10 : ℝ) ^ 19
  | .C => (11 / 5) * (10 : ℝ) ^ 19
  | .D => 0

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The standard point-charge calculation gives

`U = (8.99 * 10^9) (53 / 10^17) J = 4.7647 * 10^-6 J`.

It is strictly positive because all three charges are positive.  It equals
none of the literal displayed values, in particular not the recorded `0 J`
choice D.
-/
theorem problem_phyx_mini_0855
    (setup : ThreePointChargeSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalThreeChargeParameters setup)
    (h_geometry : SatisfiesDepictedSeparationGeometry setup)
    (h_constant : UsesTextbookVacuumCoulombConstant setup)
    (h_energy : SatisfiesThreePointChargeElectrostaticEnergyLaw setup) :
    energyInJoules setup.electrostaticPotentialEnergy =
        47647 / (10 : ℝ) ^ 10 ∧
      0 < energyInJoules setup.electrostaticPotentialEnergy ∧
      ∀ choice,
        energyInJoules setup.electrostaticPotentialEnergy ≠
          displayedEnergyInJoules choice := by
  have h_factor :=
    pairwiseChargeDistanceFactor setup h_figure h_geometry
  have h_constant_value :=
    h_constant.dimensionfulReadoutAgreesWithPhyslib.trans
      h_constant.calibratedPhyslibReadout
  have h_value :
      energyInJoules setup.electrostaticPotentialEnergy =
        47647 / (10 : ℝ) ^ 10 := by
    rw [h_energy.pairwiseCoulombEnergySum, h_constant_value, h_factor]
    norm_num
  refine ⟨h_value, ?_, ?_⟩
  · rw [h_energy.pairwiseCoulombEnergySum]
    have h_q_tl :=
      h_physical.everyDisplayedChargeIsPositive .topLeft
    have h_q_tr :=
      h_physical.everyDisplayedChargeIsPositive .topRight
    have h_q_bl :=
      h_physical.everyDisplayedChargeIsPositive .bottomLeft
    have h_r_top :=
      h_physical.distinctSitesHavePositiveSeparation
        .topLeft .topRight (by decide)
    have h_r_left :=
      h_physical.distinctSitesHavePositiveSeparation
        .topLeft .bottomLeft (by decide)
    have h_r_diag :=
      h_physical.distinctSitesHavePositiveSeparation
        .topRight .bottomLeft (by decide)
    have h_k := h_physical.coulombConstantPositive
    positivity
  · intro choice
    rw [h_value]
    cases choice <;> norm_num [displayedEnergyInJoules]

end PhyXMiniProblems.ProblemPhyXMini0855

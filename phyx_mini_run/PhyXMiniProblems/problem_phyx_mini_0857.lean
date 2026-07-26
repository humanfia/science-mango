import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0857

open Dimension

/-!
# Electric potential at point C outside a positive point charge

The primary image shows a positive `2.0 nC` point charge at the common center
of two dashed circles.  Points `A` and `B` lie on the inner `1.0 cm` circle,
and point `C` lies on the outer `2.0 cm` circle.  The requested quantity is
the electric potential at `C`, with zero potential taken at infinity.

Charge, radial distance, and electric potential are represented by Physlib's
unit-independent `Dimensionful` quantities.  Real numbers occur only as
explicit readouts in nanocoulombs, centimetres, metres, and volts.

Assumption/target split:

* governing laws: the point-charge potential law `V = k q / r` and the
  zero-at-infinity reference convention;
* previous-part results: none;
* figure/data readouts: the positive `2.0 nC` source, both dashed circle
  radii, the memberships of `A`, `B`, and `C`, and the school-level
  `k = 9 * 10^9` SI calibration;
* current target: the potential at `C` is `900 V`.

No setup field or premise states the target potential.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent radial distance. -/
abbrev RadialDistanceQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed, unit-independent electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- Coherent-SI readout of a radial distance in metres. -/
def radialDistanceInMeters (distance : RadialDistanceQuantity) : ℝ :=
  ((distance UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the radius labels in the image. -/
def radialDistanceInCentimeters (distance : RadialDistanceQuantity) : ℝ :=
  100 * radialDistanceInMeters distance

/-- Coherent-SI readout of a signed electric charge in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the source label in the image. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI readout of electric potential in volts. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-! ## Figure labels and independent physical setup -/

/-- The three observation points named in the supplied figure. -/
inductive DiagramPoint where
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

/-- The two dashed circles centered on the source charge. -/
inductive RadialCircle where
  | inner
  | outer
  deriving DecidableEq, Fintype, Repr

/-- The sign glyph drawn inside the central source circle. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Circle on which each named point appears in the primary image. -/
def expectedCircleForPoint : DiagramPoint → RadialCircle
  | .A => .inner
  | .B => .inner
  | .C => .outer

/-- Literal presentation data transcribed from image `857.png`. -/
structure PointChargePotentialFigure where
  sourceSign : FigureChargeSign
  sourceChargeLabelNanocoulombs : ℝ
  sourceAtCommonCenter : Bool
  pointShown : DiagramPoint → Bool
  pointCircle : DiagramPoint → RadialCircle
  dashedCircleShown : RadialCircle → Bool
  radialArrowShown : RadialCircle → Bool
  radiusLabelCentimeters : RadialCircle → ℝ

/-- The convention used to choose the additive constant of the potential. -/
inductive PotentialReference where
  | zeroAtInfinity
  | other
  deriving DecidableEq, Repr

/-!
Independent physical quantities in the point-charge setup.  In particular,
`potentialAt` is an observable field and is not defined from an answer choice
or from the desired `900 V` value.
-/
structure PointChargePotentialSetup where
  figure : PointChargePotentialFigure
  sourceCharge : SignedChargeQuantity
  centerToPointDistance : DiagramPoint → RadialDistanceQuantity
  potentialAt : DiagramPoint → ElectricPotentialQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  potentialReference : PotentialReference

/-! ## Problem data, figure evidence, and governing electrostatics -/

/-!
The labels and geometry read directly from the primary image, together with
their association to the independent physical charge and distances.  No
electric-potential value occurs in this data structure.
-/
structure MatchesSuppliedPointChargeFigure
    (setup : PointChargePotentialSetup) : Prop where
  sourceSignIsPositive : setup.figure.sourceSign = .plus
  printedSourceCharge : setup.figure.sourceChargeLabelNanocoulombs = 2
  physicalChargeMatchesLabel :
    chargeInNanocoulombs setup.sourceCharge =
      setup.figure.sourceChargeLabelNanocoulombs
  sourceIsAtCommonCenter : setup.figure.sourceAtCommonCenter = true
  allPointsAreShown : ∀ point, setup.figure.pointShown point = true
  pointCircleMembership : ∀ point,
    setup.figure.pointCircle point = expectedCircleForPoint point
  bothDashedCirclesAreShown : ∀ circle,
    setup.figure.dashedCircleShown circle = true
  bothRadiusArrowsAreShown : ∀ circle,
    setup.figure.radialArrowShown circle = true
  innerRadiusLabel : setup.figure.radiusLabelCentimeters .inner = 1
  outerRadiusLabel : setup.figure.radiusLabelCentimeters .outer = 2
  physicalDistancesMatchCircleLabels : ∀ point,
    radialDistanceInCentimeters (setup.centerToPointDistance point) =
      setup.figure.radiusLabelCentimeters (setup.figure.pointCircle point)

/-!
The rounded Coulomb constant used by the multiple-choice calculation.  The
Physlib declaration `Electromagnetism.EMSystem.coulombConstant` is the scalar
coherent-SI constant `1 / (4 π ε₀)` appearing in the governing law.
-/
structure UsesSchoolCoulombConstant
    (setup : PointChargePotentialSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9

/-- Positivity and separation conditions selecting the physical branch. -/
structure HasPhysicalPointChargeParameters
    (setup : PointChargePotentialSetup) : Prop where
  sourceChargePositive : 0 < chargeInCoulombs setup.sourceCharge
  pointSeparatedFromSource : ∀ point,
    0 < radialDistanceInMeters (setup.centerToPointDistance point)
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-!
For a point charge `q`, with the potential zero fixed at infinity, the
potential at every observation point a nonzero distance `r` from the source is
`k q / r`.  This is a general governing law and contains no numerical target.
-/
structure SatisfiesPointChargePotentialLaw
    (setup : PointChargePotentialSetup) : Prop where
  referenceIsZeroAtInfinity :
    setup.potentialReference = .zeroAtInfinity
  potentialOfPointCharge : ∀ point,
    radialDistanceInMeters (setup.centerToPointDistance point) ≠ 0 →
      electricPotentialInVolts (setup.potentialAt point) =
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs setup.sourceCharge /
            radialDistanceInMeters (setup.centerToPointDistance point)

/-! ## Displayed choices and target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Voltage in volts printed beside each displayed answer label. -/
def AnswerChoice.voltageInVolts : AnswerChoice → ℝ
  | .A => 1100
  | .B => 1600
  | .C => 800
  | .D => 900

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The image data place point `C` at a radial distance of `2.0 cm`. -/
lemma pointC_distance_readout
    (setup : PointChargePotentialSetup)
    (_figure : MatchesSuppliedPointChargeFigure setup) :
    radialDistanceInCentimeters
      (setup.centerToPointDistance .C) = 2 := by
  calc
    radialDistanceInCentimeters (setup.centerToPointDistance .C) =
        setup.figure.radiusLabelCentimeters (setup.figure.pointCircle .C) :=
      _figure.physicalDistancesMatchCircleLabels .C
    _ = setup.figure.radiusLabelCentimeters .outer := by
      rw [_figure.pointCircleMembership .C]
      rfl
    _ = 2 := _figure.outerRadiusLabel

/-!
Specializing the governing point-charge law at point `C` gives the Coulomb
expression whose independent numerical inputs are supplied above.
-/
lemma potentialAtPointC_eq_coulombExpression
    (setup : PointChargePotentialSetup)
    (_physical : HasPhysicalPointChargeParameters setup)
    (_law : SatisfiesPointChargePotentialLaw setup) :
    electricPotentialInVolts (setup.potentialAt .C) =
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs setup.sourceCharge /
          radialDistanceInMeters (setup.centerToPointDistance .C) := by
  exact _law.potentialOfPointCharge .C
    (ne_of_gt (_physical.pointSeparatedFromSource .C))

/-!
For the `+2.0 nC` source and `2.0 cm` radius shown in the image,
`V_C = (9 * 10^9)(2 * 10^-9)/(2 * 10^-2) = 900 V`.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0857:target`.
-/
theorem problem_phyx_mini_0857
    (setup : PointChargePotentialSetup)
    (_figure : MatchesSuppliedPointChargeFigure setup)
    (_constant : UsesSchoolCoulombConstant setup)
    (_physical : HasPhysicalPointChargeParameters setup)
    (_law : SatisfiesPointChargePotentialLaw setup) :
    electricPotentialInVolts (setup.potentialAt .C) = 900 := by
  have hDistanceCentimeters :=
    pointC_distance_readout setup _figure
  have hDistanceMeters :
      radialDistanceInMeters (setup.centerToPointDistance .C) =
        (1 : ℝ) / 50 := by
    unfold radialDistanceInCentimeters at hDistanceCentimeters
    linarith
  have hChargeNanocoulombs :
      chargeInNanocoulombs setup.sourceCharge = 2 := by
    calc
      chargeInNanocoulombs setup.sourceCharge =
          setup.figure.sourceChargeLabelNanocoulombs :=
        _figure.physicalChargeMatchesLabel
      _ = 2 := _figure.printedSourceCharge
  have hChargeCoulombs :
      chargeInCoulombs setup.sourceCharge =
        (2 : ℝ) / (10 : ℝ) ^ 9 := by
    unfold chargeInNanocoulombs at hChargeNanocoulombs
    norm_num at hChargeNanocoulombs ⊢
    linarith
  have hPotential :=
    potentialAtPointC_eq_coulombExpression setup _physical _law
  rw [_constant.coulombConstantCalibration, hChargeCoulombs,
    hDistanceMeters] at hPotential
  norm_num at hPotential
  exact hPotential

end PhyXMiniProblems.ProblemPhyXMini0857
